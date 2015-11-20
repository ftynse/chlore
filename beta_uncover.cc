#define CLOOG_INT_LONG_LONG
#include <cloog/int.h>
#include <cloog/cloog.h>

#include <osl/osl.h>

#include <clay/array.h>
#include <clay/beta.h>
#include <clay/relation.h>
#include <clay/util.h>

#include <cassert>
#include <cstdio>
#include <iostream>
#include <map>
#include <set>
#include <vector>
#include <utility>

#include "osl_wrapper.h"

std::vector<std::pair<int, int>> scalar_dimensions(osl_relation_p relation,
                                                   const std::map<std::vector<int>, std::set<int>> &context = std::map<std::vector<int>, std::set<int>>());

std::vector<int> form_pseudo_beta(std::vector<std::pair<int, int>> scalars, osl_relation_p scattering);

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

// scop with no unions
void postprocess_mapping(std::map<int, ClayArray> &mapping, int extra_dims, osl_scop_p scop,
                         const std::map<std::vector<int>, std::set<int>> &context) {
  osl_statement_p stmt = scop->statement;
  for (auto &it : mapping) {
    assert(stmt);
    clay_array_p beta = static_cast<clay_array_p>(it.second);
    int initial_size = beta->size;
    osl_relation_p scattering = stmt->scattering;


    std::vector<std::pair<int, int>> contextualized_scalars = scalar_dimensions(scattering, context);
    int current_extra_dims = beta->size - (scattering->nb_output_dims - contextualized_scalars.size() + 2);

    beta->size -= current_extra_dims + 1;
    int updated = beta->data[initial_size - 1] + beta->data[beta->size - 1];

    for (auto &it2 : mapping) {
      clay_array_p current = static_cast<clay_array_p>(it2.second);
      if (current->size >= beta->size &&
          current->data[beta->size - 1] >= updated) {
        current->data[beta->size - 1] += beta->data[initial_size - 1];
      }
    }

    beta->data[beta->size - 1] = updated;
    stmt = stmt->next;
  }
}

std::vector<int> form_pseudo_beta(std::vector<std::pair<int, int>> scalars, osl_relation_p scattering) {
  std::vector<int> pseudo_beta;
  pseudo_beta.resize(scattering->nb_output_dims, -1); // TODO: using -1 for non-scalar equations, allow full equations for more precise comparison
  for (auto it : scalars) {
    int row = it.second;
    int value = osl_int_get_si(scattering->precision,
                               scattering->m[row][scattering->nb_columns - 1]);
    assert(value != -1 &&
           "Scalar value is -1, but -1 is used as a marker for non-scalar dimensions");
    pseudo_beta[it.first] = value;
  }

  return pseudo_beta;
}

// context: pseudo-beta prefix -> list of dimensions that are scalar in some relations, but are not scalar in others
std::vector<std::pair<int, int>> scalar_dimensions(osl_relation_p relation,
                                                   const std::map<std::vector<int>, std::set<int>> &context) {
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

  std::vector<int> pseudo_beta = form_pseudo_beta(dimensions, relation);
  auto it = std::find_if(std::begin(context), std::end(context),
                         [&pseudo_beta] (const std::pair<std::vector<int>, std::set<int>> &entry) {
    if (pseudo_beta.size() >= entry.first.size()) {
      return std::equal(std::begin(entry.first), std::end(entry.first), std::begin(pseudo_beta));
    }
    return false;
  });
  if (it != std::end(context)) {
    const std::set<int> &nonscalar_dimensions = it->second;
    for (auto jt = nonscalar_dimensions.rbegin(), ejt = nonscalar_dimensions.rend(); jt != ejt; ++jt) {
      auto found = std::find_if(std::begin(dimensions), std::end(dimensions),
                                    [jt](const std::pair<int, int> &entry) {
        return entry.first == *jt;
      });
      if (found != std::end(dimensions))
        dimensions.erase(found);
    }
  }

  return dimensions;
}

void replace_beta(osl_relation_p relation, clay_array_p beta,
                  const std::map<std::vector<int>, std::set<int>> &context) {
  std::vector<std::pair<int, int>> scalar_dims = scalar_dimensions(relation, context);

  if (relation->nb_output_dims > beta->size + static_cast<int>(scalar_dims.size()) - 1) {
    // in case of loop [i]->[2*i,i,i], CLooG does not generate surrounding loops for the inners, add more betas.
    int extra_betas = relation->nb_output_dims - (beta->size + static_cast<int>(scalar_dims.size()) - 1);
    fprintf(stderr, "[chlore] adding %d beta values\n", extra_betas);
    for (int i = 0; i < extra_betas; i++) {
      clay_array_add(beta, 0);
    }
  }

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

bool form_pseudo_beta_mapping(osl_scop_p scop,
                              const std::map<std::vector<int>, std::set<int>> &context,
                              std::map<osl_relation_p, std::vector<int>> &pseudo_beta_mapping) {
  bool has_adjacent = false;

  // Construct pseudo-beta vectors with positive values for the scalars
  // and -1 for the non-scalar dimensions.
  for (osl_statement_p stmt = scop->statement; stmt != NULL;
       stmt = stmt->next) {
    for (osl_relation_p scattering = stmt->scattering;
         scattering != NULL; scattering = scattering->next) {
      std::vector<std::pair<int, int>> scalars = scalar_dimensions(scattering, context);

      std::sort(std::begin(scalars), std::end(scalars),
                [](const std::pair<int, int> &a, const std::pair<int, int> &b) {
                  return a.first < b.first;
                }
               );

      if (scalars.size() > 1 && !has_adjacent) {
        for (size_t i = 0; i < scalars.size() - 1; i++) {
          if (scalars[i].first + 1 == scalars[i + 1].first) {
            has_adjacent = true;
            break;
          }
        }
      }

      std::vector<int> pseudo_beta = form_pseudo_beta(scalars, scattering);
      pseudo_beta_mapping[scattering] = pseudo_beta;

    }
  }
  return has_adjacent;
}

void chlore_debug_print_context(const std::map<std::vector<int>, std::set<int>> &context) {
#ifndef NDEBUG
  for (auto element: context) {
    const std::vector<int> &prefix = element.first;
    const std::set<int> &dims = element.second;
    std::cerr << "[";
    std::copy(std::begin(prefix), std::end(prefix), std::ostream_iterator<int>(std::cerr, ", "));
    std::cerr << "]: {";
    std::copy(std::begin(dims), std::end(dims), std::ostream_iterator<int>(std::cerr, ", "));
    std::cerr << "}" << std::endl;
  }
#endif // NDEBUG
}

void scop_remove_adjacent_scalar_dimensions(osl_scop_p scop,
                                            std::map<std::vector<int>, std::set<int>> &context) {
  std::map<osl_relation_p, std::vector<int>> pseudo_beta_mapping;
  bool has_adjacent = form_pseudo_beta_mapping(scop, context, pseudo_beta_mapping);

  if (!has_adjacent)
    return;

  while (true) {
    // Find a pseudo beta with adjacent group
    size_t group_start = -1u; // inclusive
    size_t group_end = -1u;   // non-inclusive
    std::vector<int> pseudo_beta;
    for (auto it : pseudo_beta_mapping) {
      pseudo_beta = it.second;
      group_start = -1u;
      group_end = -1u;
      if (pseudo_beta.size() <= 1) {
        continue;
      }
      // Find first adjacent group.
      for (size_t i = 0; i < pseudo_beta.size() - 1; i++) {
        if (pseudo_beta[i] != -1 && pseudo_beta[i + 1] != -1 && group_start == -1u) {
          group_start = i;
        }
        if (pseudo_beta[i + 1] == -1 && group_start != -1u) {
          group_end = i + 1;
          break;
        }
      }
      if (group_start != -1u && group_end == -1u) {
        group_end = pseudo_beta.size();
      }

      if (group_start != -1u) {
        break;
      }
    }
    if (group_start == -1u) { // No more adjacent groups.
      break;
    }

    // Find all pseudo betas with the same prefix.
    std::vector<int> pseudo_beta_prefix = std::vector<int>(std::begin(pseudo_beta), std::begin(pseudo_beta) + group_start);
    std::set<osl_relation_p> same_prefix_scatterings;
    for (auto it : pseudo_beta_mapping) {
      const std::vector<int> &other_pseudo_beta = it.second;
      if (other_pseudo_beta.size() < pseudo_beta_prefix.size())
        continue;
      if (std::equal(std::begin(pseudo_beta_prefix), std::end(pseudo_beta_prefix),
                     std::begin(other_pseudo_beta))) {
        same_prefix_scatterings.insert(it.first);
      }
    }

    // For all pseudo betas with the same prefix, check if all dimensions in the scalar group
    // are indeed scalar and extract them for sorting.
    std::vector<std::pair<std::vector<int>, osl_relation_p>> sub_pseudo_betas;
    sub_pseudo_betas.reserve(same_prefix_scatterings.size());
    bool restart_required = false;
    for (osl_relation_p scat : same_prefix_scatterings) {
      assert(pseudo_beta_mapping.count(scat) != 0);
      std::vector<int> other_pseudo_beta = pseudo_beta_mapping[scat];

      // Check for clashes scalar/non-scalar, add to context.
      std::set<int> nonscalar_dims;
      for (size_t i = group_start; i < group_end; i++) {
        if (other_pseudo_beta[i] == -1) {
          nonscalar_dims.insert(i);
        }
      }
      if (nonscalar_dims.size() != 0) {
        std::cerr << "[chlore] clash on scalar/non-scalar dimensions" << std::endl;
        std::cerr << "[chlore] treating ";
        std::copy(std::begin(nonscalar_dims), std::end(nonscalar_dims), std::ostream_iterator<int>(std::cerr, " "));
        std::cerr << "as non-scalar dimensions" << std::endl;
        // this will create an empty set if there is not one yet.
        context[pseudo_beta_prefix].insert(std::begin(nonscalar_dims), std::end(nonscalar_dims));

        pseudo_beta_mapping.clear();
        if (!form_pseudo_beta_mapping(scop, context, pseudo_beta_mapping)) {
          // No adjacent scalar dimensions after context correction.
          return;
        } else {
          restart_required = true;
          // Do not break immediately, let discover other clashes.
        }
      }

      sub_pseudo_betas.push_back(std::make_pair(
                                   std::vector<int>(std::begin(other_pseudo_beta) + group_start,
                                                    std::begin(other_pseudo_beta) + group_end),
                                   scat));
    }
    if (restart_required)
      continue;

    std::sort(std::begin(sub_pseudo_betas),
              std::end(sub_pseudo_betas),
              [](std::pair<std::vector<int>, osl_relation_p> a,
                 std::pair<std::vector<int>, osl_relation_p> b) {
      return a.first < b.first;
    });

    // Replace adjacent scalar dimensions with a single dimensions representing their lexicographic order.
    for (size_t i = 0; i < sub_pseudo_betas.size(); i++) {
      osl_relation_p scattering = sub_pseudo_betas[i].second;
      std::vector<std::pair<int, int>> scalars = scalar_dimensions(scattering, context);
      std::set<int> extra_lines; // sorted!
      int replacement_row;
      for (size_t dim = group_start; dim < group_end; dim++) {
        auto it = std::find_if(std::begin(scalars), std::end(scalars),
                              [dim](const std::pair<int, int> &a) { return a.first == (int) dim; });
        assert (it != std::end(scalars));
        if (dim == group_start) {// Keep first dimension for replacement.
          replacement_row = it->second;
        } else {
          extra_lines.insert(it->second);
        }
      }

      // Remove extra rows from scattering, starting from the last one to avoid reindexing.
      for (auto it = extra_lines.rbegin(), eit = extra_lines.rend(); it != eit; ++it) {
        osl_relation_remove_row(scattering, *it);
      }
      // Remove extra columns from scattering, starting from the last one as well
      // without removing the first dimension.
      for (size_t j = group_end; j > group_start + 1; --j) {
        // j >= group_start with group_start == 0 would be always true
        // Index needs -1 to adjust from unsigned loop with negative increment (group_end is outside bounds, so group_end - 1 should be the first)
        // But it needs +1 to remove the proper output column ignoring the e/i column.
        osl_relation_remove_column(scattering, j);
      }
      scattering->nb_output_dims -= (group_end - group_start - 1);
      // Update the remaining scalar value.
      osl_int_set_si(scattering->precision,
                     &scattering->m[replacement_row][scattering->nb_columns - 1],
                     static_cast<int>(i));

      // Update mapping.
      const std::vector<int> old_pseudo_beta = pseudo_beta_mapping[scattering];
      std::vector<int> new_pseudo_beta = std::vector<int>(std::begin(old_pseudo_beta),
                                                          std::begin(old_pseudo_beta) + group_start);
      new_pseudo_beta.push_back(i);
      std::copy(std::begin(old_pseudo_beta) + group_end, std::end(old_pseudo_beta),
                std::back_inserter(new_pseudo_beta));
      pseudo_beta_mapping[scattering] = new_pseudo_beta;
    }

    // Update context once all the statements are updated.
    for (auto it = std::begin(context), eit = std::end(context); it != eit; ++it) {
      std::vector<int> prefix = it->first;
      if (!std::equal(std::begin(prefix), std::end(prefix), std::begin(pseudo_beta_prefix)))
        continue;
      std::set<int> new_dimensions;
      for (auto d : it->second) {
        new_dimensions.insert(d >= (int)group_end ? d - (group_end - group_start - 1) : d);
      }
      it->second = new_dimensions;
    }
  }
}

void scop_remove_scalar_nonbetas(osl_scop_p scop) {
  std::map<std::vector<int>, std::set<int>> empty_context;

  // Verify all betas are properly recovered.
#ifndef _NDEBUG
  for (osl_statement_p stmt = scop->statement; stmt != NULL; stmt = stmt->next) {
    for (osl_relation_p scattering = stmt->scattering;
         scattering != NULL; scattering = scattering->next) {
      std::vector<std::pair<int, int>> scalars = scalar_dimensions(scattering, empty_context);

      std::vector<int> expected_beta_scalars;
      expected_beta_scalars.reserve(scattering->nb_output_dims / 2 + 1);
      for (int i = 0; i < (scattering->nb_output_dims + 1) / 2; i++) {
        expected_beta_scalars.push_back(2*i);
      }
      assert(std::all_of(std::begin(expected_beta_scalars), std::end(expected_beta_scalars),
                         [scalars](int d) {
        return std::find_if(std::begin(scalars), std::end(scalars),
                            [d](const std::pair<int, int> &entry) {
                              return entry.first == d;
                            }
                           ) != std::end(scalars);
      }));
    }
  }
#endif

  for (osl_statement_p stmt = scop->statement; stmt != NULL; stmt = stmt->next) {
    for (osl_relation_p scattering = stmt->scattering;
         scattering != NULL; scattering = scattering->next) {
      std::vector<std::pair<int, int>> scalars = scalar_dimensions(scattering, empty_context);

      // Sort by dimension number ascending.
      std::sort(std::begin(scalars), std::end(scalars),
                [](const std::pair<int, int> &a, const std::pair<int, int> &b) {
        return a.first < b.first;
      });

      // Even values correspond to beta-dimensions, odd -- to scalar alpha dimensions.
      // If all betas are present and known to be scalar, we can integrate an odd
      // scalar dimensions and the subsequent beta to the preceeding beta-dimension.
      auto odd_it = std::find_if(scalars.rbegin(), scalars.rend(),
                                  [](const std::pair<int, int> &entry) {
        return (entry.first % 2) == 1;
      });
      if (odd_it != scalars.rend()) {
        int odd_dimension = odd_it->first;
        int preceeding_even_dimension = odd_dimension - 1;

        // Find all relations with the same beta-prefix, until preceeding
        // beta dimension, inclusive.

        // For all of them with scalar odd dimension at the same position,
        // compute the lexicographic order and replace the preceeding beta
        // with it.

        // Should not be any clashes scalar/non-scalar on odd positions after
        // removing extra alpha dimensions.
      }

    }
  }
}

void scop_remove_linearly_dependent_dimensions(osl_scop_p scop) {
  for (osl_statement_p stmt = scop->statement; stmt != NULL; stmt = stmt->next) {
    for (osl_relation_p scattering = stmt->scattering;
         scattering != NULL; scattering = scattering->next) {
      // Check if linearly-dependent dimensions are present,
      // and if they were added by the transormation.

      // Their relation with the domain: is it possible that such extra
      // dimension is actually executing before/after all iterations
      // on the loop?  If it is, it may be replaced by a scalar/beta.
    }
  }
}

void reintroduce_betas(osl_scop_p scop, const std::map<std::vector<int>, std::set<int>> &context) {
  CloogState *cloog_state = cloog_state_malloc();
  CloogOptions *cloog_options = cloog_options_malloc(cloog_state);
  cloog_options->f = -1;
  cloog_options->openscop = 1;
  cloog_options->otl = 0;
  cloog_options->quiet = 1;

  osl_scop_p linear_scop = osl_scop_remove_unions(scop);

  CloogInput *cloog_input = cloog_input_from_osl_scop(cloog_state, linear_scop);
  CloogProgram *cloog_program = cloog_program_alloc(cloog_input->context, cloog_input->ud, cloog_options);

  cloog_program_generate(cloog_program, cloog_options);

  std::map<int, ClayArray> mapping;
  uncover_betas(cloog_program->loop, mapping, ClayArray());
  int extra_dims = (maximum_depth(cloog_program->loop) - 1) / 2;

  for (auto it : mapping) {
    std::cerr << it.first << " : " << it.second << std::endl;
  }

  postprocess_mapping(mapping, extra_dims, linear_scop, context);

  for (auto it : mapping) {
    std::cerr << it.first << " : " << it.second << std::endl;
  }

  // We assume that after 'remove_unions" call the newly created statements have the
  // same order as the linearized list of scattering relaions in the original SCoP.
  osl_statement_p stmt = scop->statement;
  osl_relation_p scattering = stmt->scattering;
  for (auto it : mapping) {
    assert(scattering != NULL);
    assert(stmt != NULL);
    replace_beta(scattering, it.second, context);
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

int check_beta_uniqueness(osl_scop_p scop,
                          const std::map<std::vector<int>, std::set<int>> &context) {
  std::vector<ClayArray> betas;
  for (osl_statement_p stmt = scop->statement; stmt != NULL; stmt = stmt->next) {
    for (osl_relation_p scattering = stmt->scattering; scattering != NULL; scattering = scattering->next) {
      osl_relation_p scat = osl_relation_nclone(scattering, 1);
      clay_relation_normalize_alpha(scat);
      std::vector<std::pair<int, int>> scalar_dims = scalar_dimensions(scat, context);
//      for (size_t i = 0; i < scalar_dims.size(); i++) {
//        std::cerr << scalar_dims[i].first << std::endl;
//        if ((size_t) scalar_dims[i].first != 2*i) {
//          return 0;
//        }
//      }
//      if ((int) scalar_dims.size() * 2 - 1 != scat->nb_output_dims) {
//        return 0;
//      }

      ClayArray beta = ClayArray(clay_beta_extract(scat));
      if (std::find(std::begin(betas), std::end(betas), beta) != std::end(betas)) {
        return 0;
      }
      betas.push_back(beta);

      osl_relation_free(scat);
    }
  }
  return 1;
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

  std::map<std::vector<int>, std::set<int>> context;

  scop_remove_adjacent_scalar_dimensions(scop, context);

//  for (auto it: context) {
//    std::copy(std::begin(it.first), std::end(it.first), std::ostream_iterator<int>(std::cerr, " "));
//    std::cerr << " :  ";
//    std::copy(std::begin(it.second), std::end(it.second), std::ostream_iterator<int>(std::cerr, " "));
//    std::cerr << std::endl;
//  }

  reintroduce_betas(scop, context);

//  assert(check_beta_uniqueness(scop, context));

  osl_scop_print(stdout, scop);
  osl_scop_free(scop);

  return 0;
}

