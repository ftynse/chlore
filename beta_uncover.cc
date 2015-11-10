#define CLOOG_INT_LONG_LONG
#include <cloog/int.h>
#include <cloog/cloog.h>

#include <osl/osl.h>

#include <clay/array.h>
#include <clay/relation.h>
#include <clay/util.h>

#include <cassert>
#include <cstdio>
#include <iostream>
#include <map>
#include <vector>
#include <utility>

#include "osl_wrapper.h"

char *clay_array_string(clay_array_p array) {
  size_t length = 3 + array->size * sizeof(int) * 4;
  char *string = (char *) malloc(length);
  char *start = string;
  int i;
  char buffer[sizeof(int) * 3 + 1];
  int watermark = length;

  snprintf(string, watermark, "[");
  string += 1;
  watermark -= 1;

  for (i = 0; i < array->size - 1; i++) {
    int current_length;
    snprintf(buffer, sizeof(int) * 3 + 1, "%d", array->data[i]);
    snprintf(string, watermark, "%s,", buffer);
    current_length = strlen(buffer);
    string += current_length + 1;
    watermark -= current_length + 1;
  }
  if (array->size != 0) {
    int current_length;
    snprintf(buffer, sizeof(int) * 3 + 1, "%d", array->data[array->size - 1]);
    snprintf(string, watermark, "%s", buffer);
    current_length = strlen(buffer);
    string += current_length;
    watermark -= current_length;
  }
  snprintf(string, watermark, "]");

  return start;
}

int maximum_depth(CloogLoop *loop, int start = 0) {
  if (loop == NULL)
    return start;
  int result = start;
  for (CloogLoop *l = loop->inner; l != NULL; l = l->next) {
    int current = maximum_depth(l, start + 1);
    if (current > result)
      result = current;
  }
  return result;
}

void uncover_betas(CloogLoop *loop, std::map<int, ClayArray> &mapping, clay_array_p prefix, int depth = 0) {
  if (loop == NULL)
    return;

  if ((depth % 2) == 1 && !loop->block) {
//    assert(loop->inner != NULL && loop->inner->next == NULL);
//    uncover_betas(loop->inner, mapping, prefix, depth + 1);
  }

  if (loop->block) {
    int index = 0;
    for (CloogStatement *stmt = loop->block->statement; stmt != NULL; stmt = stmt->next, ++index) {
      clay_array_p beta = clay_array_clone(prefix);
      clay_array_add(beta, index);
      mapping.emplace(std::make_pair(stmt->number, ClayArray(beta)));
    }
    return;
  }

  int index = 0;
  for (CloogLoop *inner = loop->inner; inner != NULL; inner = inner->next, ++index) {
    clay_array_p child_prefix = clay_array_clone(prefix);
    clay_array_add(child_prefix, index);
    uncover_betas(inner, mapping, child_prefix, depth + 1);
    clay_array_free(child_prefix);
  }
}

void postprocess_mapping(std::map<int, ClayArray> &mapping, int extra_dims) {
  for (auto &it : mapping) {
    clay_array_p beta = static_cast<clay_array_p>(it.second);
    int initial_size = beta->size;
    beta->size -= extra_dims + 1;
    int updated = beta->data[initial_size - 1] + beta->data[beta->size - 1];

    for (auto &it2 : mapping) {
      clay_array_p current = static_cast<clay_array_p>(it2.second);
      if (current->size >= beta->size &&
          current->data[beta->size - 1] >= updated) {
        current->data[beta->size - 1] += beta->data[initial_size- 1];
      }
    }

    beta->data[beta->size - 1] = updated;
  }
}

std::vector<std::pair<int, int>> scalar_dimensions(osl_relation_p relation) {
  std::vector<std::pair<int, int>> dimensions;

  for (int i = 0; i < relation->nb_rows; i++) {
    int dim = -1;
    bool scalar = true;
    if (!osl_int_zero(relation->precision,
                      relation->m[i][0])) {
      scalar = false;
    }
    for (int j = 0; j < relation->nb_output_dims; j++) {
      if (dim == -1) {
        if (osl_int_mone(relation->precision,
                         relation->m[i][1 + j])) {
          dim = j;
          continue;
        }
      } else {
        if (!osl_int_zero(relation->precision,
                          relation->m[i][1 + j])) {
          scalar = false;
          break;
        }
      }
    }
    for (int j = relation->nb_output_dims + 1; j < relation->nb_columns - 1; j++) {
      if (!osl_int_zero(relation->precision,
                        relation->m[i][j])) {
        scalar = false;
        break;
      }
    }

    // Check if this dimension does not appear in other (in)equalities.
    for (int j = 0; j < relation->nb_rows; j++) {
      if (i != j) {
        if (!osl_int_zero(relation->precision,
                          relation->m[j][1 + dim])) {
          scalar = false;
        }
      }
    }


    if (scalar) {
      assert(dim != -1);
      dimensions.push_back(std::make_pair(dim, i));
    }
  }

  return dimensions;
}

void remove_adjacent_scalar_dimension(osl_relation_p relation,
                                      std::vector<std::pair<int, int>> &scalar_dims) {
  // Go in inverse direction to prevent row/column reindexing after deletion
  for (size_t i = 0; i < scalar_dims.size() - 1; i++) {
    size_t idx = scalar_dims.size() - i - 2;
    if (scalar_dims[idx].first == scalar_dims[idx + 1].first - 1) {
      osl_relation_remove_row(relation, scalar_dims[idx + 1].second);
      osl_relation_remove_column(relation, scalar_dims[idx + 1].first + 1);
      relation->nb_output_dims -= 1;
      scalar_dims.erase(scalar_dims.begin() + idx + 1);
      --i;
    }
  }
}

void replace_beta(osl_relation_p relation, clay_array_p beta) {
  std::vector<std::pair<int, int>> scalar_dims = scalar_dimensions(relation);

  // Keep only first of adjacent scalar dimensions (pluto may add multiple,
  // but they are trivially linearizable using their lexicographic order).
  remove_adjacent_scalar_dimension(relation, scalar_dims);

  for (int i = 0; i < beta->size; i++) {
    int current_dimension = 2 * i;

    if (scalar_dims.size() != 0) {
      assert(scalar_dims.front().first >= current_dimension);
    }

    if (scalar_dims.size() != 0 &&
        scalar_dims.front().first == current_dimension) {
      int row = scalar_dims.front().second;
      osl_int_set_si(relation->precision,
                     &relation->m[row][relation->nb_columns - 1],
                     beta->data[i]);
      scalar_dims.erase(scalar_dims.begin());
    } else {
      osl_relation_insert_blank_row(relation, 0);
      osl_relation_insert_blank_column(relation, 1 + current_dimension);
      relation->nb_output_dims += 1;
      osl_int_set_si(relation->precision,
                     &relation->m[0][1 + current_dimension],
                     -1);
      osl_int_set_si(relation->precision,
                     &relation->m[0][relation->nb_columns - 1],
                     beta->data[i]);
      for (size_t j = 0; j < scalar_dims.size(); j++) {
        scalar_dims[j].first += 1;
        scalar_dims[j].second += 1;
      }
    }
  }
}

void reintroduce_betas(osl_scop_p scop) {
  CloogState *cloog_state = cloog_state_malloc();
  CloogOptions *cloog_options = cloog_options_malloc(cloog_state);
  cloog_options->f = -1;
  cloog_options->openscop = 1;

  osl_scop_p linear_scop = osl_scop_remove_unions(scop);

  CloogInput *cloog_input = cloog_input_from_osl_scop(cloog_state, linear_scop);
  CloogProgram *cloog_program = cloog_program_alloc(cloog_input->context, cloog_input->ud, cloog_options);

  cloog_program_generate(cloog_program, cloog_options);

  std::map<int, ClayArray> mapping;
  uncover_betas(cloog_program->loop, mapping, ClayArray());
  int extra_dims = (maximum_depth(cloog_program->loop) - 1) / 2;
  postprocess_mapping(mapping, extra_dims);

  // We assume that after 'remove_unions" call the newly created statements have the
  // same order as the linearized list of scattering relaions in the original SCoP.
  osl_statement_p stmt = scop->statement;
  osl_relation_p scattering = stmt->scattering;
  for (auto it : mapping) {
    assert(scattering != NULL);
    assert(stmt != NULL);
    replace_beta(scattering, it.second);
    if (scattering->next != NULL) {
      scattering = scattering->next;
    } else {
      stmt = stmt->next;
      scattering = stmt ? stmt->scattering : NULL;
    }
  }

  osl_scop_free(linear_scop);
  cloog_program_free(cloog_program);
  cloog_options_free(cloog_options);
  cloog_state_free(cloog_state);
}

int main(int argc, char **argv) {
  if (argc != 2) {
    if (argc == 1) {
      std::cerr << "Usage " << argv[0] << " <filename.scop>" << std::endl;
    } else {
      std::cerr << "Usage ./beta_uncover <filename.scop>" << std::endl;
    }
    return 1;
  }

  FILE *f = fopen(argv[1], "r");
  if (!f)
    return 2;
  osl_scop_p scop = osl_scop_read(f);
  fclose(f);
  if (!scop)
    return 3;
  reintroduce_betas(scop);

  osl_scop_print(stdout, scop);
  osl_scop_free(scop);

  return 0;
}

