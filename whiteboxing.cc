#include <deque>
#include <iostream>
#include <set>
#include <sstream>
#include <tuple>
#include <vector>
#include <exception>
#include <typeinfo>

#include <osl/osl.h>

#include <clay/transformation.h>
#include <clay/beta.h>
#include <clay/relation.h>
#include <clay/errors.h>
#include <clay/util.h>

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

#include <chlore/chlore.h>
#include "beta.h"
#include "osl_wrapper.h"

// chunky loop optimization revealer ||
// chunku loop optimizer reverse engineering
// ChLORe

int chlore_linearizable_lines_impl(osl_scop_p scop, clay_array_p beta, int depth,
                                   clay_list_p found_betas, clay_array_p row_indices,
                                   int pseudo_linearizable);
int chlore_extract_stripmine_size_impl(osl_scop_p scop, clay_array_p beta, int depth, int pseudo_linearizable);

class optional_empty {
  operator bool() const {
    return false;
  }
};

template <typename T>
class optional {
private:
  bool has_value;
  T value;
public:
  optional(const T &t) : has_value(true), value(t) {}
  optional() : has_value(false) {}
  optional(const optional_empty &) : has_value(false) {}

  operator bool () const {
    return has_value;
  }

  operator T& () {
    if (!has_value) {
      throw std::bad_cast();
    }
    return value;
  }

  operator const T& () const {
    if (!has_value) {
      throw std::bad_cast();
    }
    return value;
  }
};

template <typename T>
class optional<T *> {
private:
  T *value;
public:
  optional(T *t) : value(t | 0x1) {}
  optional() : value(0) {}
  optional(const optional_empty &) : value(0) {}

  operator bool () const {
    return value & 0x1;
  }

  operator T* () {
    if (!(value & 0x1))
      throw std::bad_cast();
    return value & ~0x1;
  }

  operator const T* () const {
    if (!(value & 0x1))
      throw std::bad_cast();
    return value & ~0x1;
  }
};

template <typename T>
optional<T> make_optional(T t) {
  return optional<T>(t);
}

struct ChloreBetaTransformation {
  enum {
    FUSE,
    SPLIT,
    REORDER
  } kind;
  ClayArray target;
  int depth;
  int first_loop_size;
  ClayArray order;
};

std::ostream &operator <<(std::ostream &out, const ChloreBetaTransformation &transformation) {
  switch (transformation.kind) {
  case ChloreBetaTransformation::FUSE:
    out << "fuse(" << transformation.target;
    break;

  case ChloreBetaTransformation::SPLIT:
    out << "split(" << transformation.target << ", " << transformation.depth;
    break;

  case ChloreBetaTransformation::REORDER:
    out << "reorder(" << transformation.target << ", " << transformation.order;
  }
  out << ");\n";
  return out;
}

std::deque<ChloreBetaTransformation>
chlore_complementary_beta_transformation(std::vector<ChloreBetaTransformation> sequence) {
  std::deque<ChloreBetaTransformation> result;
  for (ChloreBetaTransformation &transformation : sequence) {
    ChloreBetaTransformation new_transformation;
    switch (transformation.kind) {
    case ChloreBetaTransformation::FUSE:
    {
      new_transformation.kind = ChloreBetaTransformation::SPLIT;
      clay_array_p target = clay_array_clone(transformation.target);
      clay_array_add(target, transformation.first_loop_size);
      new_transformation.target = target;
      new_transformation.depth = target->size - 1;
    }
      break;

    case ChloreBetaTransformation::SPLIT:
    {
      new_transformation.kind = ChloreBetaTransformation::FUSE;
      clay_array_p target = clay_array_clone(transformation.target);
      target->size = transformation.depth;
      new_transformation.target = ClayArray(target);
    }
      break;

    case ChloreBetaTransformation::REORDER:
    {
      new_transformation.kind = ChloreBetaTransformation::REORDER;
      new_transformation.target = transformation.target;
      clay_array_p old_order = static_cast<clay_array_p>(transformation.order);
      clay_array_p new_order = clay_array_clone(transformation.order);
      for (int i = 0; i < old_order->size; i++) {
        new_order->data[old_order->data[i]] = i;
      }
      new_transformation.order = ClayArray(new_order);
    }
      break;

    default:
      assert(0);
    }
    result.push_front(new_transformation);
  }
  return result;
}

template <typename Func, typename... Args>
int chlore_try_transformation(osl_scop_p scop, Func transformation, Args... arguments) {
  osl_scop_p copy = osl_scop_clone(scop);

  int result = transformation(copy, arguments...);
  int success = result == CLAY_SUCCESS;
  success = success && !osl_scop_equal(copy, scop);
  osl_scop_free(copy);
  return success;
}

template <typename T>
void vector_remove_duplicates(std::vector<T> &data) {
  std::set<size_t> to_remove;
  for (size_t i = 0, ei = data.size(); i < ei; i++) {
    for (size_t j = i + 1, ej = data.size(); j < ej; j++) {
      if (data[i] == data[j]) {
        to_remove.insert(j);
      }
    }
  }

  for (auto it = to_remove.rbegin(), eit = to_remove.rend(); it != eit; it++) {
    data.erase(data.begin() + *it);
  }
}

void chlore_info_message(const char *message) {
  fprintf(stderr, "[chlore] %s\n", message);
}

int chlore_check_compatible(osl_scop_p original, osl_scop_p transformed) {
  int nb_stmts_original = 0;
  int nb_stmts_transformed = 0;
  osl_statement_p stmt, original_stmt, transformed_stmt;
  int i;

  if (original == NULL) {
    chlore_info_message("Original scop is null");
    return 0;
  }
  if (transformed == NULL) {
    chlore_info_message("Transformed scop is null");
    return 0;
  }

  for (stmt = original->statement; stmt != NULL; stmt = stmt->next) {
    ++nb_stmts_original;
  }
  for (stmt = transformed->statement; stmt != NULL; stmt = stmt->next) {
    ++nb_stmts_transformed;
  }

  if (nb_stmts_original != nb_stmts_transformed) {
    chlore_info_message("Different number of statements");
    return 0;
  }

  original_stmt = original->statement;
  transformed_stmt = transformed->statement;
  for (i = 0; i < nb_stmts_original; i++) {
    if (!osl_relation_equal(original_stmt->domain, transformed_stmt->domain)) {
      chlore_info_message("Domain was modified for statement");
      return 0;
    }

    original_stmt = original_stmt->next;
    transformed_stmt = transformed_stmt->next;
  }

  return 1;
}

int chlore_check_minimal(osl_relation_p relation) {
  int idx = 0;
  for (int row = 0; row < relation->nb_rows; row++) {
    if (clay_util_is_row_beta_definition(relation, row))
      continue;
    if (!osl_int_zero(relation->precision,
                      relation->m[row][0])) {
      chlore_info_message("relation contains an inequality");
      return 0;  // not an equation
    }
    for (int j = 1; j < relation->nb_columns; j++) {
      if (j == 1 + row) {
        if (!osl_int_mone(relation->precision,
                          relation->m[row][j])) {
          chlore_info_message("output dim is not -1");
          return 0;
        }
      } else if (j == 1 + relation->nb_output_dims + idx) {
        if (!osl_int_one(relation->precision,
                        relation->m[row][j])) {
          chlore_info_message("input dim is not 1");
          return 0;
        }
      } else if (!osl_int_zero(relation->precision,
                               relation->m[row][j])) {
        chlore_info_message("unexpected non-zero value");
        return 0;
      }
    }
    idx++;
  }
  return 1;
}

int chlore_check_structure_compatible(osl_scop_p original, osl_scop_p transformed) {
  if (original == NULL) {
    chlore_info_message("Original scop is null");
    return 0;
  }
  if (transformed == NULL) {
    chlore_info_message("Transformed scop is null");
    return 0;
  }

  osl_statement_p original_stmt = original->statement,
                  transformed_stmt = transformed->statement;
  for ( ;
       original_stmt != NULL && transformed_stmt != NULL;
       original_stmt = original_stmt->next, transformed_stmt = transformed_stmt->next) {
    osl_relation_p original_rel = original_stmt->scattering,
                   transformed_rel = transformed_stmt->scattering;
    for ( ;
         original_rel != NULL && transformed_rel != NULL;
         original_rel = original_rel->next, transformed_rel = transformed_rel->next) {
      if (!chlore_check_minimal(original_rel))
        return 0;
      if (!chlore_check_minimal(transformed_rel))
        return 0;
      if (original_rel->nb_output_dims != transformed_rel->nb_output_dims) {
        chlore_info_message("relation dimensionality mismatch");
        return 0;
      }
    }
    if ((original_rel == NULL) ^ (transformed_rel == NULL)) {
      chlore_info_message("scattering union cardinality mismatch");
      return 0;
    }
  }
  if ((original_stmt == NULL) ^ (transformed_stmt == NULL)) {
    chlore_info_message("statement number mismatch");
    return 0;
  }

  return 1;
}

int chlore_relation_collapsing_lines(osl_relation_p s1, osl_relation_p s2,
                                     int *row_index1, int *row_index2) {
  int row, col, row_1, row_2;
  int candidate_row_1, candidate_row_2;
  clay_array_p matched_rows_2;

  assert(row_index1 && row_index2);

  // Check scattering parameters are compatible.
  if (!s1 || !s2 ||
      s1->nb_rows != s2->nb_rows ||
      s1->nb_input_dims != s2->nb_input_dims ||
      s1->nb_output_dims != s2->nb_output_dims ||
      s1->nb_local_dims != s2->nb_local_dims ||
      s1->nb_parameters != s2->nb_parameters) {
    return CLAY_ERROR_WRONG_COEFF; // FIXME: local dimensions can be merged
  }

  // Check all equalities are the same (in normalized form, equations come
  // before inequalities, sorted lexicographically so that line by line
  // comparison is possible.
  for (row = 0; row < s1->nb_rows; row++) {
    if (clay_util_is_row_beta_definition(s1, row)) {
      continue; // ignore beta rows that are already compare by beta-matching
    }
    if (osl_int_one(s1->precision, s1->m[row][0])) {
      break; // inequality part started
    }
    for (col = 0; col < s1->nb_columns; col++) {
      if (osl_int_ne(s1->precision, s1->m[row][col], s2->m[row][col])) {
        return CLAY_ERROR_WRONG_COEFF;
      }
    }
  }

  matched_rows_2 = clay_array_malloc();
  candidate_row_1 = -1;
  for (row_1 = row; row_1 < s1->nb_rows; row_1++) {
    int matched_row = -1;
    for (row_2 = row; row_2 < s2->nb_rows; row_2++) {
      int mismatch = 0;

      // Skip if row is already matched.
      if (clay_array_contains(matched_rows_2, row_2)) {
        continue;
      }

      for (col = 0; col < s1->nb_columns; col++) {
        if (osl_int_ne(s1->precision,
                       s1->m[row_1][col], s2->m[row_2][col])) {
          mismatch = 1;
          break;
        }
      }
      if (!mismatch) {
        matched_row = row_2;
        clay_array_add(matched_rows_2, row_2);
        break;
      }
    }

    // If no row matched,
    if (matched_row == -1) {
      if (candidate_row_1 != -1) { // Cannot have two unmatching rows.
        clay_array_free(matched_rows_2);
        return CLAY_ERROR_WRONG_COEFF;
      }
      candidate_row_1 = row_1;
    }
  }

  // Find the single unmatched row in s2.
  candidate_row_2 = -1;
  for (row_2 = row; row_2 < s2->nb_rows; row_2++) {
    if (!clay_array_contains(matched_rows_2, row_2)) {
      candidate_row_2 = row_2;
      break;
    }
  }
  clay_array_free(matched_rows_2);
  if (candidate_row_2 == -1) {
    // XXX: Something went wrong...
    return CLAY_ERROR_WRONG_COEFF;
  }

  // Check if unmatched rows differ up to negation.
  clay_util_relation_negate_row(s2, candidate_row_2);
  for (col = 0; col < s1->nb_columns; col++) {
    if (osl_int_ne(s1->precision, s1->m[candidate_row_1][col],
                                  s2->m[candidate_row_2][col])) {
      return CLAY_ERROR_WRONG_COEFF;
    }
  }
  clay_util_relation_negate_row(s2, candidate_row_2);

  // All preconditions are met, now we may remove the inequality and the
  // second relation.

  *row_index1 = candidate_row_1;
  *row_index2 = candidate_row_2;
  return CLAY_SUCCESS;
}

// FIXME: this is almost a copy of clay_collapse()
int chlore_collapsing_lines(osl_scop_p scop, clay_array_p beta,
                            clay_list_p found_betas, clay_array_p row_indices) {
  int i, candidate_row1, candidate_row2, result;
  int nb_pairs;
  clay_array_p first_beta, second_beta, max_beta;
  clay_list_p matching_betas = clay_list_malloc();
  osl_statement_p statement, first_statement, second_statement;
  osl_relation_p scattering, s1, s2;

  if (!scop || !scop->statement || !scop->statement->scattering)
     return CLAY_SUCCESS;

  clay_scop_normalize(scop);

  // Find all betas-vectors matching the given prefix.
  statement = scop->statement;
  while (statement != NULL) {
    scattering = statement->scattering;
    while (scattering != NULL) {
      if (!clay_beta_check_relation(scattering, beta)) {
        scattering = scattering->next;
        continue;
      }
      clay_list_add(matching_betas, clay_beta_extract(scattering));
      scattering = scattering->next;
    }
    statement = statement->next;
  }

  // Every relation should have a pair to collapse it with.
  if ((matching_betas->size % 2) != 0 || matching_betas->size == 0) {
    clay_list_free(matching_betas);
    return CLAY_ERROR_BETA_NOT_FOUND;
  }


  clay_beta_list_sort(matching_betas);
  max_beta = clay_beta_max(scop->statement, beta);
  if (max_beta->size <= beta->size) {
    clay_array_free(max_beta);
    clay_list_free(matching_betas);
    return CLAY_ERROR_BETA_NOT_IN_A_LOOP;
  }
  nb_pairs = (max_beta->data[beta->size] + 1) / 2;// assume betas are normalized
  clay_array_free(max_beta);

  // For each matching beta, find its counterpart by going through half of the
  // sorted beta list (counterpats are also matching) and check if both parts
  // can collapse to one.
  for (i = 0; i < matching_betas->size / 2; i++) {
    first_beta = matching_betas->data[i];
    if (first_beta->size == beta->size) { // Collpase works on loop level.
      clay_list_free(matching_betas);
      return CLAY_ERROR_BETA_NOT_IN_A_LOOP;
    }
    second_beta = clay_array_clone(first_beta);
    second_beta->data[beta->size] += nb_pairs;


    // Both betas should belong to the same statement.
    first_statement = clay_beta_find(scop->statement, first_beta);
    second_statement = clay_beta_find(scop->statement, second_beta);
    if (!first_statement || !second_statement ||
        first_statement != second_statement) {
      clay_array_free(second_beta);
      clay_list_free(matching_betas);
      return CLAY_ERROR_BETA_NOT_FOUND;
    }


    s1 = NULL;
    s2 = NULL;
    for (scattering = first_statement->scattering; scattering != NULL;
         scattering = scattering->next) {
      if (clay_beta_check_relation(scattering, first_beta)) {
        s1 = scattering;
      }
      if (clay_beta_check_relation(scattering, second_beta)) {
        s2 = scattering;
      }
    }
    clay_array_free(second_beta);

    result = chlore_relation_collapsing_lines(s1, s2, &candidate_row1, &candidate_row2);
    if (result != CLAY_SUCCESS) {
      clay_list_free(matching_betas);
      return result;
    }

    clay_list_add(found_betas, clay_beta_extract(s1));
    clay_array_add(row_indices, candidate_row1);
  }

  clay_list_free(matching_betas);
  return CLAY_SUCCESS;
}

// Assumes normalized betas, returns -1 if no children
int chlore_last_statement_beta_dim(osl_scop_p scop, clay_array_p beta) { // XXX: use tree instead
  int last_statement_beta_dim = -1;
  for (osl_statement_p statement = scop->statement; statement != NULL; statement = statement->next) {
    for (osl_relation_p scattering = statement->scattering; scattering != NULL; scattering = scattering->next) {
      if (clay_beta_check_relation(scattering, beta)) {
        clay_array_p scattering_beta = clay_beta_extract(scattering);
        if (scattering_beta->size > beta->size) {
          last_statement_beta_dim = std::max(last_statement_beta_dim, scattering_beta->data[beta->size]);
        }
        clay_array_free(scattering_beta);
      }
    }
  }
  return last_statement_beta_dim;
}

void chlore_put_statement_last(osl_scop_p scop, int last_statement_beta_dim, clay_array_p beta,
                               std::vector<ChloreBetaTransformation> &commands, clay_options_p options) {
  int statement_beta_dim = beta->data[beta->size - 1];
  clay_array_p reorder_list = clay_array_malloc();
  for (int i = 0; i <= last_statement_beta_dim; i++) {
    if (i < statement_beta_dim) {
      clay_array_add(reorder_list, i);
    } else if (i == statement_beta_dim) {
      clay_array_add(reorder_list, last_statement_beta_dim);
    } else {
      clay_array_add(reorder_list, i - 1);
    }
  }


  ChloreBetaTransformation transformation;
  beta->size -= 1;
  transformation.kind = ChloreBetaTransformation::REORDER;
  transformation.target = ClayArray::copy(beta);
  transformation.order = ClayArray::copy(reorder_list);
  commands.push_back(transformation);
  clay_reorder(scop, beta, reorder_list, options);
  beta->size += 1;

  clay_array_free(reorder_list);
}

void chlore_put_statement_first(osl_scop_p scop, clay_array_p beta,
                                std::vector<ChloreBetaTransformation> &commands, clay_options_p options) {
  int statement_beta_dim = beta->data[beta->size - 1];
  beta->size -= 1;
  int last_statement_beta_dim = chlore_last_statement_beta_dim(scop, beta);
  beta->size += 1;

  clay_array_p reorder_list = clay_array_malloc();
  for (int i = 0; i <= last_statement_beta_dim; i++) {
    if (i < statement_beta_dim) {
      clay_array_add(reorder_list, i + 1);
    } else if (i == statement_beta_dim) {
      clay_array_add(reorder_list, 0);
    } else {
      clay_array_add(reorder_list, i);
    }
  }

  ChloreBetaTransformation transformation;
  beta->size -= 1;
  transformation.kind = ChloreBetaTransformation::REORDER;
  transformation.target = ClayArray::copy(beta);
  transformation.order = ClayArray::copy(reorder_list);
  commands.push_back(transformation);
  clay_reorder(scop, beta, reorder_list, options);
  beta->size += 1;

  clay_array_free(reorder_list);

}

static void chlore_reordering_list(int statement_beta_dim, clay_array_p reorder_list, int location, int last_statement_beta_dim) {
  if (statement_beta_dim > location) {
    for (int i = 0; i <= last_statement_beta_dim; i++) {
      if (i > location && i < statement_beta_dim) {
        reorder_list->data[i] = i + 1;
      } else if (i == statement_beta_dim) {
        reorder_list->data[i] = location + 1;
      } else {
        reorder_list->data[i] = i;
      }
    }
  } else {
    for (int i = 0; i <= last_statement_beta_dim; i++) {
      if (i > statement_beta_dim && i <= location) {
        reorder_list->data[i] = i - 1;
      } else if (i == statement_beta_dim) {
        reorder_list->data[i] = location;
      } else {
        reorder_list->data[i] = i;
      }
    }
  }
}

void chlore_put_statement_after(osl_scop_p scop, int location, clay_array_p beta,
                                std::vector<ChloreBetaTransformation> &commands, clay_options_p options) {
  int statement_beta_dim = beta->data[beta->size - 1];
  beta->size -= 1;
  int last_statement_beta_dim = chlore_last_statement_beta_dim(scop, beta);
  beta->size += 1;

  clay_array_p reorder_list = clay_array_malloc();
  for (int i = 0; i <= last_statement_beta_dim; i++) {
    clay_array_add(reorder_list, 0);
  }

  chlore_reordering_list(statement_beta_dim, reorder_list, location, last_statement_beta_dim);

  ChloreBetaTransformation transformation;
  beta->size -= 1;
  transformation.kind = ChloreBetaTransformation::REORDER;
  transformation.target = ClayArray::copy(beta);
  transformation.order = ClayArray::copy(reorder_list);
  commands.push_back(transformation);
  clay_reorder(scop, beta, reorder_list, options);
  beta->size += 1;

  clay_array_free(reorder_list);
}

clay_array_p chlore_detach_statement_from_loop(osl_scop_p scop, clay_array_p beta,
                                               std::vector<ChloreBetaTransformation> &commands, clay_options_p options) {
  assert(beta->size > 1);
  clay_array_p current_beta = clay_array_clone(beta);
  int statement_beta_dim = current_beta->data[current_beta->size - 1];
  int last_statement_beta_dim;
  current_beta->size -= 1;
  last_statement_beta_dim = chlore_last_statement_beta_dim(scop, current_beta);
  current_beta->size += 1;

  // already last, no need to reorder.
  if (statement_beta_dim != last_statement_beta_dim) {
    // put last
    chlore_put_statement_last(scop, last_statement_beta_dim, current_beta, commands, options);
  }

  // If the only statement, no need to perform an actual split.
  if (last_statement_beta_dim != 0) {
    current_beta->data[current_beta->size - 1] = last_statement_beta_dim - 1;
    ChloreBetaTransformation splitting;
    splitting.kind = ChloreBetaTransformation::SPLIT;
    splitting.depth = current_beta->size - 1;
    splitting.target = ClayArray::copy(current_beta);
    commands.push_back(splitting);
    clay_split(scop, current_beta, current_beta->size - 1, options);

    current_beta->size -= 1;
    current_beta->data[current_beta->size - 1] += 1;
    //current_beta->data[current_beta->size - 1] = 0;
  } else {
    current_beta->size -= 1;
  }

  return current_beta;
}

clay_array_p chlore_detach_statement_until_depth(osl_scop_p scop, clay_array_p beta, int depth,
                                                 std::vector<ChloreBetaTransformation> &commands, clay_options_p options) {
  assert(depth > 0);
  clay_array_p current_beta = clay_array_clone(beta);
  while (current_beta->size > depth) {
    clay_array_p old_pointer = current_beta;
    current_beta = chlore_detach_statement_from_loop(scop, current_beta, commands, options);
    clay_array_free(old_pointer);
  }
  return current_beta;
}

// Returns a beta-prefix for which linearization is possible.
clay_array_p chlore_linearizing(osl_scop_p scop, osl_statement_p statement,
                                std::vector<ChloreBetaTransformation> &commands,
                                clay_options_p options,
                                clay_list_p found_betas, clay_array_p row_indices,
                                int pseudo_linearizable) {
  if (!statement || !statement->scattering)
    return NULL;

  for (osl_relation_p scat = statement->scattering;
       scat != NULL; scat = scat->next) {
    clay_array_p current_beta = clay_beta_extract(scat);
    int try_separation_at = -1;
    for (int depth = 1, limit = current_beta->size; depth < limit; depth++) {
      int r = chlore_linearizable_lines_impl(scop, current_beta, depth, found_betas, row_indices, pseudo_linearizable);

      if (r != CLAY_SUCCESS) {
        continue;
      } else {
        try_separation_at = depth;
      }

      current_beta->size = depth;
      if (chlore_extract_stripmine_size_impl(scop, current_beta, depth, pseudo_linearizable) >= 0) {
        return current_beta;
      }
      current_beta->size = limit;

      clay_list_clear(found_betas);
      clay_array_clear(row_indices);
    }

    osl_scop_p clone = osl_scop_clone(scop);
    clay_array_p initial_beta = clay_array_clone(current_beta);
    std::vector<ChloreBetaTransformation> unused_commands;
    for (int d = try_separation_at - 1; d >= 1; --d) {
      clay_array_p detached_beta = chlore_detach_statement_until_depth(clone, current_beta, d, unused_commands, options);
      clay_array_free(current_beta);
      current_beta = detached_beta;
      for (int depth = d; depth < initial_beta->size; depth++) {
        // Grow beta.
        clay_array_p target_beta = clay_array_clone(current_beta);
        ClayArray raiitarget_beta(target_beta);
        for (int j = current_beta->size; j < initial_beta->size; j++) {
          clay_array_add(target_beta, 0);
        }
        if (chlore_extract_stripmine_size_impl(clone, target_beta, depth, pseudo_linearizable) >= 0) {
          // If it worked, perform it on the real scop
          clay_array_free(detached_beta);
          current_beta = chlore_detach_statement_until_depth(scop, initial_beta, d, commands, options);
          for (int j = current_beta->size; j < depth; j++) {
            clay_array_add(current_beta, 0);
          }
          clay_array_free(initial_beta);
          osl_scop_free(clone);
          return current_beta;
        }
      }
    }
    clay_array_free(initial_beta);
    osl_scop_free(clone);
    clay_array_free(current_beta);
  }

  return NULL;
}

// Returns a beta-prefix for which collapsing is possible.
clay_array_p chlore_collapsing(osl_scop_p scop, osl_statement_p statement,
                               std::vector<ChloreBetaTransformation> &commands, clay_options_p options,
                               clay_list_p found_betas, clay_array_p row_indices) {
  int r1, r2, result;
  clay_array_p beta1 = NULL;
  clay_array_p beta2 = NULL;
  clay_array_p collapsing_prefix = NULL;
  if (!statement || !statement->scattering)
    return NULL;

  osl_relation_p first_relation, second_relation;
  for (osl_relation_p s1 = statement->scattering; s1 != NULL; s1 = s1->next) {
    for (osl_relation_p s2 = s1->next; s2 != NULL; s2 = s2->next) {
      result = chlore_relation_collapsing_lines(s1, s2, &r1, &r2);
      if (result == CLAY_SUCCESS) {
        beta1 = clay_beta_extract(s1);
        beta2 = clay_beta_extract(s2);
        first_relation = s1;
        second_relation = s2;
        break;
      }
    }
  }

  if (beta1 != NULL && beta2 != NULL) {
    clay_array_p prefix = chlore_beta_prefix(beta1, beta2);

    int result = chlore_collapsing_lines(scop, prefix, found_betas, row_indices);
    if (result == CLAY_SUCCESS) {
      // just do it! no need for split/reorder
      collapsing_prefix = prefix;
    } else {
      // separate statements into a single loop by reordering them to the end, and then splitting the loop
      int common_prefix_length = prefix->size;
      if (common_prefix_length == 0) common_prefix_length = 1;

      clay_array_p reordered_beta_1 = chlore_detach_statement_until_depth(scop, beta1, common_prefix_length, commands, options);
      // beta2 may have changed....
      clay_array_free(beta2);
      beta2 = clay_beta_extract(second_relation);
      clay_array_p reordered_beta_2 = chlore_detach_statement_until_depth(scop, beta2, common_prefix_length, commands, options);

      // put reordered_beta_2 right after reordered_beta_1
      reordered_beta_1->size -= 1;
      int last_statement_beta_dim = chlore_last_statement_beta_dim(scop, reordered_beta_1);
      reordered_beta_1->size += 1;
      if (last_statement_beta_dim > 1) { // if there are only two statements, the are already adjacent
        chlore_put_statement_last(scop, last_statement_beta_dim, reordered_beta_1, commands, options);
        int old_size  = reordered_beta_2->size;
        clay_array_free(reordered_beta_2);
        reordered_beta_2 = clay_beta_extract(second_relation);
        reordered_beta_2->size = old_size;
        chlore_put_statement_last(scop, last_statement_beta_dim, reordered_beta_2, commands, options);
      }

      // then fuse_next reordered_beta_1 thus creating a new loop with both statements
      int old_size = reordered_beta_1->size;
      clay_array_free(reordered_beta_1);
      reordered_beta_1 = clay_beta_extract(first_relation);
      reordered_beta_1->size = old_size;

      ChloreBetaTransformation fusion;
      fusion.kind = ChloreBetaTransformation::FUSE;
      fusion.target = ClayArray::copy(reordered_beta_1);
      fusion.first_loop_size = chlore_last_statement_beta_dim(scop, reordered_beta_1);
      commands.push_back(fusion);
      clay_fuse(scop, reordered_beta_1, options);

      // may now collapse reordered_beta_1 loop
      collapsing_prefix = reordered_beta_1;
      clay_array_free(reordered_beta_2);

      chlore_collapsing_lines(scop, collapsing_prefix, found_betas, row_indices);
    }

    if (collapsing_prefix != prefix) {
      clay_array_free(prefix);
    }
    clay_array_free(beta1);
    clay_array_free(beta2);
  }

  return collapsing_prefix;
}

// FIXME: this is almost a copy of clay_linearize
// (except for pseudo-lines)
int chlore_linearizable_lines_impl(osl_scop_p scop, clay_array_p beta, int depth,
                                   clay_list_p found_betas, clay_array_p row_indices,
                                   int pseudo_linearizable) {
  osl_statement_p statement;
  osl_relation_p scattering;
  int precision;
  int row, col, i, j;
  clay_array_p candidate_rows_lower, candidate_rows_upper;
  int row_lower = -1;
  int row_upper = -1;
  int nb_output_dims = 0;

  if (!scop || !scop->statement || !scop->statement->scattering)
    return CLAY_SUCCESS;

  statement = clay_beta_find(scop->statement, beta);
  if (!statement)
    return CLAY_ERROR_BETA_NOT_FOUND;

  candidate_rows_lower = clay_array_malloc();
  candidate_rows_upper = clay_array_malloc();
  precision = statement->scattering->precision;
  while (statement != NULL) {
    scattering = statement->scattering;
    while (scattering != NULL) {
      int is_last_alpha_dim = 0;
      if (!clay_beta_check_relation(scattering, beta)) {
        scattering = scattering->next;
        continue;
      }
      // Get the maximum number of output dimensions in all matching scatterings
      if (scattering->nb_output_dims > nb_output_dims) {
        nb_output_dims = scattering->nb_output_dims;
      }
      if ((scattering->nb_output_dims - 1) / 2 < depth + 1) { // Check depth.
        if (pseudo_linearizable && !(scattering->nb_output_dims + 1) / 2 < depth + 1) { // allow looking at the last dim for pseudo
          is_last_alpha_dim = 1;
        } else {
          clay_array_free(candidate_rows_lower);
          clay_array_free(candidate_rows_upper);
          return CLAY_ERROR_DEPTH_OVERFLOW;
        }
      }
      clay_array_clear(candidate_rows_lower);
      clay_array_clear(candidate_rows_upper);

      // Go through all inequalities and find a pair with specific form
      for (row = 0; row < scattering->nb_rows; row++) {
        int all_zero = 1;
        int constant_zero = 0;
        int positive_at_depth = 0;
        int one_at_next = 0;
        int mone_at_next = 0;
        int zero_at_next = 0;
        int one_at_current = 0;
        if (osl_int_zero(precision, scattering->m[row][0])) {
          continue;
        }

        for (col = 1; col < scattering->nb_columns - 1; col++) {
          if (col == 2*depth || (!is_last_alpha_dim && col == 2*depth + 2)) {
            continue;
          } else {
            if (!osl_int_zero(precision, scattering->m[row][col])) {
              all_zero = 0;
              break;
            }
          }
        }
        if (!all_zero) {
          continue;
        }

        if (osl_int_zero(precision, scattering->m[row][2*depth]) ||
            (!is_last_alpha_dim && !pseudo_linearizable && osl_int_zero(precision, scattering->m[row][2*depth + 2]))) {
          continue;
        }

        constant_zero     = osl_int_zero(precision,
                                scattering->m[row][scattering->nb_columns - 1]);
        positive_at_depth = osl_int_pos(precision,
                                scattering->m[row][2*depth]);
        one_at_next       = osl_int_one(precision,
                                scattering->m[row][2*depth + 2]);
        mone_at_next      = osl_int_mone(precision,
                                scattering->m[row][2*depth + 2]);
        zero_at_next      = is_last_alpha_dim || osl_int_zero(precision,
                                scattering->m[row][2*depth + 2]); // short-circuit or prevents access out of bounds
        one_at_current    = osl_int_one(precision,
                                scattering->m[row][2*depth]);

        if (!pseudo_linearizable) {
          if (!positive_at_depth && one_at_next && constant_zero) {
            clay_array_add(candidate_rows_lower, row);
          } else if (positive_at_depth && mone_at_next && (!constant_zero ^ one_at_current)) {
            clay_array_add(candidate_rows_upper, row);
          }
        } else {
          if (!positive_at_depth && zero_at_next) {
            clay_array_add(candidate_rows_lower, row);
          } else if (positive_at_depth && zero_at_next) {
            clay_array_add(candidate_rows_upper, row);
          }
        }
      }

      if (candidate_rows_lower->size == 0 || candidate_rows_upper->size == 0) {
        clay_array_free(candidate_rows_lower);
        clay_array_free(candidate_rows_upper);
        return CLAY_ERROR_WRONG_COEFF;
      }

      // Check if coefficients in the specific form match stripmining
      for (i = 0; i < candidate_rows_lower->size; i++) {
        for (j = 0; j < candidate_rows_upper->size; j++) {
          int row_i = candidate_rows_lower->data[i];
          int row_j = candidate_rows_upper->data[j];
          int same_factor = 0;
          int correct_constant = 0;
          osl_int_t tmp;

          osl_int_init(precision, &tmp);
          osl_int_add(precision, &tmp, scattering->m[row_i][depth * 2],
                                       scattering->m[row_j][depth * 2]);
          same_factor = osl_int_zero(precision, tmp);
          osl_int_add_si(precision, &tmp, scattering->m[row_j][depth * 2], -1);
          correct_constant = osl_int_eq(precision, tmp,
                              scattering->m[row_j][scattering->nb_columns - 1]);
          if (same_factor && correct_constant) {
            // found a pair
            row_lower = row_i;
            row_upper = row_j;
            osl_int_clear(precision, &tmp);
            break;
          }
          osl_int_clear(precision, &tmp);
        }
      }

      if (row_lower == -1 || row_upper == -1) {
        clay_array_free(candidate_rows_lower);
        clay_array_free(candidate_rows_upper);
        return CLAY_ERROR_WRONG_COEFF;
      }

      clay_list_add(found_betas, clay_beta_extract(scattering));
      clay_array_add(row_indices, row_lower);
      clay_array_add(row_indices, row_upper);

      scattering = scattering->next;
    }
    statement = statement->next;
  }

  return CLAY_SUCCESS;
}

int chlore_densifiable(osl_scop_p scop, clay_array_p beta, int depth,
                       clay_list_p found_betas, clay_array_p grains) {
  osl_statement_p statement;
  osl_relation_p scattering;
  int precision;
  osl_int_t factor;
  int row, col;

  if (!scop || !scop->statement || !scop->statement->scattering)
    return CLAY_SUCCESS;

  osl_int_init(scop->statement->scattering->precision, &factor);

  statement = clay_beta_find(scop->statement, beta);
  if (!statement)
    return CLAY_ERROR_BETA_NOT_FOUND;

  precision = statement->scattering->precision;
  while (statement != NULL) {
    scattering = statement->scattering;
    for ( ; scattering != NULL; scattering = scattering->next) {
      if (!clay_beta_check_relation(scattering, beta)) {
        continue;
      }
      CLAY_BETA_CHECK_DEPTH(beta, depth, scattering);

      factor = clay_relation_gcd(scattering, depth);
      if (osl_int_zero(precision, factor)) {
        continue;
      }

      for (row = 0; row < scattering->nb_rows; row++) {
        if (osl_int_zero(precision, scattering->m[row][depth * 2])) {
          continue;
        }
        for (col = 2; col < scattering->nb_columns; col++) {
          // if beta, ignore
          if (col >= 1 && col < scattering->nb_output_dims + 1 && (col % 2) == 1) {
            continue;
          }
          // if target dimension, ignore
          if (col == depth * 2) {
            continue;
          }
          clay_list_add(found_betas, clay_beta_extract(scattering));
          clay_array_add(grains, osl_int_get_si(precision, factor));
        }
      }
    }
    statement = statement->next;
  }

  osl_int_clear(precision, &factor);
  return CLAY_SUCCESS;
}

clay_list_p chlore_extract_iss_line(osl_scop_p scop, clay_list_p found_betas, clay_array_p row_indices) {
  int i, j;
  clay_list_p result = clay_list_malloc();
  clay_array_p output = clay_array_malloc();
  clay_array_p input = clay_array_malloc();
  clay_array_p parameters = clay_array_malloc();
  clay_array_p constant = clay_array_malloc();
  osl_statement_p statement;
  osl_relation_p scattering;
  int error = 0;

  if (found_betas->size == 0) {
    return NULL;
  }

  // Check that all collapsing rows are identical.
  clay_beta_find_relation(scop->statement, found_betas->data[0],
                          &statement, &scattering);
  assert(scattering != NULL);
  for (i = 0; i < scattering->nb_output_dims / 2; i++) {
    clay_array_add(output, osl_int_get_si(scattering->precision,
                                scattering->m[row_indices->data[0]][2 + 2*i]));
  }
  for (i = 0; i < scattering->nb_input_dims; i++) {
    clay_array_add(input, osl_int_get_si(scattering->precision,
      scattering->m[row_indices->data[0]][1 + scattering->nb_output_dims + i]));
  }
  for (i = 0; i < scattering->nb_parameters; i++) {
    clay_array_add(parameters, osl_int_get_si(scattering->precision,
      scattering->m[row_indices->data[0]]
                   [1 + scattering->nb_output_dims + scattering->nb_input_dims
                      + scattering->nb_local_dims + i]));
  }
  clay_array_add(constant, osl_int_get_si(scattering->precision,
      scattering->m[row_indices->data[0]][scattering->nb_columns - 1]));
  clay_list_add(result, output);
  clay_list_add(result, input);
  clay_list_add(result, parameters);
  clay_list_add(result, constant);

  for (i = 1; i < found_betas->size; i++) {
    clay_beta_find_relation(scop->statement, found_betas->data[i],
                            &statement, &scattering);
    if (scattering->nb_output_dims / 2 != output->size ||
        scattering->nb_input_dims != input->size ||
        scattering->nb_parameters != parameters->size) {
      chlore_info_message("Dimensionality mismatch while extracing iss line");
      error = 1;
      break;
    }
    for (j = 0; j < scattering->nb_output_dims / 2; j++) {
      int v = osl_int_get_si(scattering->precision,
                             scattering->m[row_indices->data[i]][2 + 2*j]);
      if (v != output->data[j]) {
        error = 2;
        break;
      }
    }
    for (j = 0; j < scattering->nb_input_dims; j++) {
      int v = osl_int_get_si(scattering->precision,
                    scattering->m[row_indices->data[i]][1 + scattering->nb_output_dims + j]);
      if (v != input->data[j]) {
        error = 3;
        break;
      }
    }
    for (j = 0; j < scattering->nb_parameters; j++) {
      int v = osl_int_get_si(scattering->precision,
        scattering->m[row_indices->data[i]][1 + scattering->nb_output_dims + scattering->nb_input_dims
                                              + scattering->nb_local_dims + j]);
      if (v != parameters->data[j]) {
        error = 4;
        break;
      }
    }
    if (osl_int_get_si(scattering->precision,
             scattering->m[row_indices->data[i]][scattering->nb_columns - 1])
         != constant->data[0]) {
      error = 5;
    }

    if (error) {
      break;
    }
  }
  if (error) {
    clay_list_free(found_betas);
    clay_array_free(row_indices);
    clay_list_free(result);
    return NULL;
  }

  return result;
}

int chlore_extract_stripmine_size_impl(osl_scop_p scop, clay_array_p beta, int depth,
                                       int pseudo_linearizable) {
  clay_list_p found_betas = clay_list_malloc();
  clay_array_p row_indices = clay_array_malloc();
  osl_statement_p statement;
  osl_relation_p scattering;
  osl_int_t factor;
  int i;
  int size;
  int precision;

  if (chlore_linearizable_lines_impl(scop, beta, depth, found_betas, row_indices, pseudo_linearizable) !=
        CLAY_SUCCESS) {
    clay_list_free(found_betas);
    clay_array_free(row_indices);
    return -1;
  }
  if (found_betas->size == 0 || row_indices->size == 0) {
    clay_list_free(found_betas);
    clay_array_free(row_indices);
    return -2;
  }

  clay_beta_find_relation(scop->statement, found_betas->data[0],
                          &statement, &scattering);
  precision = scattering->precision;
  osl_int_init(precision, &factor);

  osl_int_assign(precision, &factor,
          scattering->m[row_indices->data[1]][scattering->nb_columns - 1]);

  for (i = 1; i < found_betas->size; i++) {
    clay_beta_find_relation(scop->statement, found_betas->data[i],
                            &statement, &scattering);
    if (!osl_int_eq(scattering->precision, factor,
                    scattering->m[row_indices->data[2*i + 1]][scattering->nb_columns - 1])) {
      clay_list_free(found_betas);
      clay_array_free(row_indices);
      osl_int_clear(scattering->precision, &factor);
      return -3;
    }
  }

  size = osl_int_get_si(precision, factor);

  osl_int_clear(precision, &factor);
  clay_list_free(found_betas);
  clay_array_free(row_indices);
  return size;
}

int chlore_extract_stripmine_size(osl_scop_p scop, clay_array_p beta, int depth) {
  return chlore_extract_stripmine_size_impl(scop, beta, depth, 0);
}

int chlore_extract_pseudo_stripmine_constant(osl_scop_p scop, clay_array_p beta, int depth) {
  return chlore_extract_stripmine_size_impl(scop, beta, depth, 1);
}

int chlore_extract_grain(osl_scop_p scop, clay_array_p beta, int depth) {
  clay_list_p found_betas = clay_list_malloc();
  clay_array_p grains = clay_array_malloc();
  int i, grain;

  if (chlore_densifiable(scop, beta, depth, found_betas, grains) !=
        CLAY_SUCCESS) {
    clay_list_free(found_betas);
    clay_array_free(grains);
    return -1;
  }
  if (found_betas->size == 0 || grains->size == 0) {
    clay_list_free(found_betas);
    clay_array_free(grains);
    return -2;
  }

  grain = grains->data[0];
  for (i = 1; i < grains->size; i++) {
    if (grain != grains->data[i]) {
      clay_list_free(found_betas);
      clay_array_free(grains);
      return -3;
    }
  }

  clay_list_free(found_betas);
  clay_array_free(grains);
  if (grain == 1) // no actual grain
    return -4;
  return grain;
}

template <typename T>
void vector_pair_remove_identical_items(std::vector<T> &v1, std::vector<T> &v2) {
  for (size_t i = 0; i < v1.size(); i++) {
    for (size_t j = 0; j < v2.size(); j++) {
      if (v1[i] == v2[j]) {
        v1.erase(v1.begin() + i);
        v2.erase(v2.begin() + j);
        --i; // May overflow, but is well-defined for unsigned integers.
        --j;
        break;
      }
    }
  }
}

static void chlore_negate_condition(clay_list_p condition) {
  assert(condition->size == 4);
  for (int i = 0; i < 3; i++) {
    for (int j = 0; j < condition->data[i]->size; j++) {
      condition->data[i]->data[j] = -condition->data[i]->data[j];
    }
  }
  condition->data[3]->data[0] = -condition->data[3]->data[0] - 1;
}

clay_list_p chlore_extract_iss_condition(osl_scop_p scop, clay_array_p beta) {
  clay_list_p found_betas = clay_list_malloc();
  clay_array_p row_indices = clay_array_malloc();
  clay_list_p condition = NULL;

  if (chlore_collapsing_lines(scop, beta, found_betas, row_indices) == CLAY_SUCCESS) {
    condition = chlore_extract_iss_line(scop, found_betas, row_indices);
    assert(condition);
    chlore_negate_condition(condition);
  }
  clay_list_free(found_betas);
  clay_array_free(row_indices);

  return condition;
}

optional<std::tuple<ClayArray, ClayList>>
lookup_iss_conditions(osl_scop_p scop, osl_statement_p statement,
                      std::vector<ChloreBetaTransformation> &commands, clay_options_p options) {
  clay_list_p found_betas = clay_list_malloc();
  clay_array_p row_indices = clay_array_malloc();

  clay_array_p beta = chlore_collapsing(scop, statement, commands, options, found_betas, row_indices);
//  chlore_collapsing_lines(scop, beta, found_betas, row_indices);
  clay_list_p condition = chlore_extract_iss_line(scop, found_betas, row_indices);

  if (condition) {
    // Negate condition because lexicographically first beta after iss in clay has a negated condition.
    chlore_negate_condition(condition);
  }

  clay_list_free(found_betas);
  clay_array_free(row_indices);
  if (condition) {
    return make_optional(std::make_tuple(ClayArray(clay_array_clone(beta)),
                         ClayList(condition)));
  } else {
    return optional_empty();
  }
}

optional<std::tuple<ClayArray, int, int>>
lookup_pseudo_stripmine_constants2(osl_scop_p scop, osl_statement_p statement,
                                  std::vector<ChloreBetaTransformation> &commands,
                                  clay_options_p options) {
  clay_list_p found_betas = clay_list_malloc();
  clay_array_p row_indices = clay_array_malloc();

  clay_array_p beta = chlore_linearizing(scop, statement, commands, options, found_betas, row_indices, 1);
  if (beta) {
    int size = chlore_extract_stripmine_size_impl(scop, beta, beta->size, 1);
    assert(size >= 0);
    return make_optional(std::make_tuple(ClayArray(beta), beta->size, size));
  } else {
    return optional_empty();
  }
}

std::vector<std::tuple<ClayArray, int, int>>
chlore_lookup_aii(osl_scop_p scop, osl_statement_p statement, bool loop_only,
                  int (*extractor)(osl_scop_p, clay_array_p, int)) {
  std::vector<std::tuple<ClayArray, int, int>> result;

  for (osl_relation_p scattering = statement->scattering; scattering != nullptr;
       scattering = scattering->next) {
    clay_array_p beta = clay_beta_extract(scattering);
    int limit_depth = beta->size;

    if (loop_only) {
      --limit_depth;
    }

    for (int depth = 1; depth <= limit_depth; depth++) {
      if (loop_only) { // FIXME: can we have beta->size x depths?
        beta->size = depth;
      }

      int partial_result = extractor(scop, beta, depth);
      if (partial_result >= 0) {
        result.push_back(std::make_tuple(ClayArray(clay_array_clone(beta)),
                                         depth, partial_result));
      }
    }
    clay_array_free(beta);
  }

  vector_remove_duplicates(result);

  return result;
}

const int TRANSFORMATION_NOT_FOUND = -1;
const int INTERCHANGE_REQUESTED = -2;

std::tuple<ClayArray, int, int, int, int>
chlore_skewed(osl_relation_p scattering) {
  osl_int_t lcm, factor_source, factor_target;
  assert(scattering != NULL);

  osl_int_init(scattering->precision, &lcm);
  osl_int_init(scattering->precision, &factor_source);
  osl_int_init(scattering->precision, &factor_target);

  clay_array_p beta = clay_beta_extract(scattering);

  // expects the relation to be normalized
  int nb_rows = 0;
  for ( ; nb_rows != scattering->nb_rows ; nb_rows++) {
    if (!osl_int_zero(scattering->precision, scattering->m[nb_rows][0]))
      break;
  }

  // expects the relation to have enough rows for all input dimensions (validity)
  assert(nb_rows >= scattering->nb_input_dims * 2 + 1);

  // beta-definition rows interleave alpha-definition rows
  for (int i = 0; i < scattering->nb_input_dims; i++) {
    for (int j = i + 1; j < scattering->nb_input_dims; j++) {
      int source_row = 2*i + 1;
      int target_row = 2*j + 1;
      int source_column = 1 + scattering->nb_output_dims + i;

      // no need for skewing away this value
      if (osl_int_zero(scattering->precision,
                       scattering->m[target_row][source_column])) {
        continue;
      }

      if (osl_int_zero(scattering->precision,
                       scattering->m[source_row][source_column])) {
        // interchange, target value is known to be non-zero by now.
        int depth_1 = -1;
        int depth_2 = -1;
        for (int k = 0; k < (scattering->nb_output_dims - 1) / 2; k++) {
          if (depth_1 == -1 &&
              !osl_int_zero(scattering->precision,
                            scattering->m[source_row][2 + 2*k])) {
            depth_1 = k + 1;
          }
          if (depth_2 == -1 &&
              !osl_int_zero(scattering->precision,
                            scattering->m[target_row][2 + 2*k])) {
            depth_2 = k + 1;
          }
        }
        assert(depth_1 != -1 && depth_2 != -1 && "relation seems invalid");
        return std::make_tuple(ClayArray(beta), INTERCHANGE_REQUESTED, -1, depth_1, depth_2);
      }

      osl_int_lcm(scattering->precision, &lcm,
                  scattering->m[source_row][source_column],
                  scattering->m[target_row][source_column]);

      osl_int_div_exact(scattering->precision, &factor_source,
                        lcm, scattering->m[source_row][source_column]);
      osl_int_div_exact(scattering->precision, &factor_target,
                        lcm, scattering->m[target_row][source_column]);

      int factor_i = osl_int_get_si(scattering->precision, factor_source);
      int factor_j = osl_int_get_si(scattering->precision, factor_target);

      osl_int_clear(scattering->precision, &lcm);
      osl_int_clear(scattering->precision, &factor_source);
      osl_int_clear(scattering->precision, &factor_target);
      return std::make_tuple(ClayArray(beta), i + 1, j + 1, factor_i, factor_j);
    }
  }

  osl_int_clear(scattering->precision, &lcm);
  osl_int_clear(scattering->precision, &factor_source);
  osl_int_clear(scattering->precision, &factor_target);
  clay_array_free(beta);
  return std::make_tuple(ClayArray(), TRANSFORMATION_NOT_FOUND, -1, 0, 0);
}

template <typename T, typename Comparator>
bool is_unique(const std::vector<T> &vector, Comparator comp) {
  for (size_t i = 0, ei = vector.size(); i < ei; ++i) {
    for (size_t j = i + 1; j < ei; j++) {
      if (comp(vector[i], vector[j])) {
        return false;
      }
    }
  }
  return true;
}

bool
chlore_explicit_dimensions_independent(osl_relation_p scattering,
                                       const std::vector<std::tuple<int, int, int>> &candidate_explicit_dimensions) {
  // Create a submatrix of input dimensions, check if has full rank.
  osl_relation_p submatrix = osl_relation_malloc(candidate_explicit_dimensions.size(),
                                                 scattering->nb_input_dims + 2);

  for (size_t i = 0; i < candidate_explicit_dimensions.size(); i++) {
    int row = std::get<1>(candidate_explicit_dimensions[i]);
    for (int j = 0; j < scattering->nb_input_dims; j++) {
      osl_int_assign(scattering->precision,
                     &submatrix->m[i][j],
                     scattering->m[row][1 + scattering->nb_output_dims + j]);
    }
  }

  // Sort rows to have non-zero main diagonal.
  for (size_t i = 0; i < std::min(candidate_explicit_dimensions.size(), (size_t)scattering->nb_input_dims); i++) {
    if (!osl_int_zero(submatrix->precision, submatrix->m[i][i]))
      continue;
    size_t row = candidate_explicit_dimensions.size();
    for (size_t j = 0; j < candidate_explicit_dimensions.size(); j++) {
      if (!osl_int_zero(submatrix->precision, submatrix->m[j][i])) {
        row = j;
        break;
      }
    }
    if (row == candidate_explicit_dimensions.size()) {
      continue;
    }
    for (int j = 0; j < scattering->nb_input_dims; j++) {
      osl_int_swap(submatrix->precision,
                   &submatrix->m[i][j], &submatrix->m[row][j]);
    }
  }

  // Perform Gauss elimination.
  osl_int_t i_multiplier;
  osl_int_t j_multiplier;
  osl_int_t value;
  osl_int_t factor;
  osl_int_init(submatrix->precision, &i_multiplier);
  osl_int_init(submatrix->precision, &j_multiplier);
  osl_int_init(submatrix->precision, &value);
  osl_int_init(submatrix->precision, &factor);
  for (int i = 0; i < scattering->nb_input_dims; i++) {
    for (size_t j = i + 1; j< candidate_explicit_dimensions.size(); j++) {
      if (osl_int_zero(submatrix->precision, submatrix->m[j][i]))
        continue;
      osl_int_lcm(submatrix->precision,
                  &factor,
                  submatrix->m[i][i],
                  submatrix->m[j][i]);

      if (osl_int_zero(submatrix->precision, factor))
        continue;

      osl_int_div_exact(submatrix->precision, &i_multiplier, factor, submatrix->m[i][i]);
      osl_int_div_exact(submatrix->precision, &j_multiplier, factor, submatrix->m[j][i]);
      for (int k = 0; k < scattering->nb_input_dims; k++) {
        osl_int_mul(submatrix->precision, &value, submatrix->m[i][k], i_multiplier);
        osl_int_mul(submatrix->precision, &submatrix->m[j][k], submatrix->m[j][k], j_multiplier);
        osl_int_sub(submatrix->precision, &submatrix->m[j][k], submatrix->m[j][k], value);
      }

    }
  }
  osl_int_clear(submatrix->precision, &i_multiplier);
  osl_int_clear(submatrix->precision, &j_multiplier);
  osl_int_clear(submatrix->precision, &value);
  osl_int_clear(submatrix->precision, &factor);


  // If there is one zero line, then linearly dependent.
  int all_zero_lines = 0;
  for (size_t i = 0; i < candidate_explicit_dimensions.size(); i++) {
    bool all_zeros = true;
    for (int j = 0; j < scattering->nb_input_dims; j++) {
      if (!osl_int_zero(submatrix->precision, submatrix->m[i][j])) {
        all_zeros = false;
        break;
      }
    }
    if (all_zeros) {
      ++all_zero_lines;
    }
  }

  osl_relation_free(submatrix);
  return all_zero_lines == 0;
}

std::pair<std::vector<std::tuple<int, int, int>>,
          std::vector<std::tuple<int, int, int>>>
chlore_dimension_definitions(osl_relation_p scattering) {
  clay_array_p beta = clay_beta_extract(scattering);
  ClayArray raiibeta(beta);

  std::vector<std::tuple<int, int, int>> candidate_explicit_dimensions;
  std::vector<std::tuple<int, int, int>> candidate_implicit_dimensions;
  for (int depth = 0; depth < beta->size - 1; depth++) {
    for (int row = 0; row < scattering->nb_rows; row++) {
      if (osl_int_zero(scattering->precision, scattering->m[row][2*depth + 2]))
        continue;
      //    bool is_explicit = false;
      if (osl_int_zero(scattering->precision, scattering->m[row][0])) { // explicit definition found
        candidate_explicit_dimensions.push_back(std::make_tuple(depth, row, -1));
      } else if (osl_int_one(scattering->precision, scattering->m[row][0])) {
        // Look for complementary inequality
        osl_int_t value;
        osl_int_init(scattering->precision, &value);
        osl_int_oppose(scattering->precision, &value, scattering->m[row][2*depth + 2]);

        bool found = false;
        for (int i = row + 1; i < scattering->nb_rows; i++) {
          if (osl_int_eq(scattering->precision, value, scattering->m[i][2*depth + 2]) &&
              osl_int_one(scattering->precision, scattering->m[i][0])) {
            candidate_implicit_dimensions.push_back(std::make_tuple(depth, row, i));
            found = true;
            break;
          }
        }
        osl_int_clear(scattering->precision, &value);
        if (found) // XXX: may not work with multiple implicit definitions...
          break;
      }
    }
  }

  // Remove explicit definitions linearly dependent on other definitions.
  std::vector<std::tuple<int, int, int>> explicit_candidate_subset;
  explicit_candidate_subset.reserve(candidate_explicit_dimensions.size());
  for (size_t i = 0; i < candidate_explicit_dimensions.size(); i++) {
    explicit_candidate_subset.push_back(candidate_explicit_dimensions[i]);
    bool linearly_dependent = !chlore_explicit_dimensions_independent(scattering, explicit_candidate_subset);
    if (linearly_dependent) {
      int dim = std::get<0>(candidate_explicit_dimensions[i]);
      auto dim_finder = [dim](const std::tuple<int, int, int> &element) {
                          return std::get<0>(element) == dim;
                        };
      // If this dimension is implicitly defined, it is safe to remove.
      if (std::find_if(std::begin(candidate_implicit_dimensions), std::end(candidate_implicit_dimensions),
                       dim_finder) != std::end(candidate_implicit_dimensions)) {
        explicit_candidate_subset.pop_back();
      // Otherwise look if it is possible to remove another implicitly defined dimension.
      } else {
        bool found = false;
        for (size_t j = 0; j < explicit_candidate_subset.size(); j++) {
          std::vector<std::tuple<int, int, int>> explicit_candidate_subsubset =
              std::vector<std::tuple<int, int, int>>(std::begin(explicit_candidate_subset),
                                                     std::end(explicit_candidate_subset));
          explicit_candidate_subsubset.erase(std::begin(explicit_candidate_subsubset) + j);
          int dim = std::get<0>(explicit_candidate_subset[j]);
          auto dim_finder = [dim](const std::tuple<int, int, int> &element) {
                              return std::get<0>(element) == dim;
                            };
          if (std::find_if(std::begin(candidate_implicit_dimensions), std::end(candidate_implicit_dimensions),
                           dim_finder) == std::end(candidate_implicit_dimensions)) {
            continue;
          }
          if (chlore_explicit_dimensions_independent(scattering, explicit_candidate_subsubset)) {
            explicit_candidate_subset.erase(std::begin(explicit_candidate_subset) + j);
            found = true;
            break;
          }
        }
        // If couldn't find such dimension, remove current.
        if (!found) {
          explicit_candidate_subset.pop_back();
        }
      }
    }
  }
  candidate_explicit_dimensions = explicit_candidate_subset;

#ifndef NDEBUG
  bool explicit_unique = is_unique(candidate_explicit_dimensions,
                                   [](const std::tuple<int, int, int> &a,
                                      const std::tuple<int, int, int> &b) {
    return std::get<0>(a) == std::get<0>(b);
  });
  bool implicit_unique = is_unique(candidate_implicit_dimensions,
                                   [](const std::tuple<int, int, int> &a,
                                      const std::tuple<int, int, int> &b) {
    return std::get<0>(a) == std::get<0>(b);
  });
  assert(explicit_unique);
  assert(implicit_unique);
#endif

  // Select the dimensions that are only explicitly or implicitly defined.
  std::vector<std::tuple<int, int, int>> explicit_dimensions;
  std::set_difference(std::begin(candidate_explicit_dimensions), std::end(candidate_explicit_dimensions),
                      std::begin(candidate_implicit_dimensions), std::end(candidate_implicit_dimensions),
                      std::back_inserter(explicit_dimensions),
                      [] (const std::tuple<int, int, int> &expl, const std::tuple<int, int, int> &impl) -> bool {
    return std::get<0>(expl) < std::get<0>(impl);
  });
  std::vector<std::tuple<int, int, int>> implicit_dimensions;
  std::set_difference(std::begin(candidate_implicit_dimensions), std::end(candidate_implicit_dimensions),
                      std::begin(candidate_explicit_dimensions), std::end(candidate_explicit_dimensions),
                      std::back_inserter(implicit_dimensions),
                      [] (const std::tuple<int, int, int> &expl, const std::tuple<int, int, int> &impl) -> bool {
    return std::get<0>(expl) < std::get<0>(impl);
  });

  std::vector<std::tuple<int, int, int>> undecided_dimensions;
  std::set_intersection(std::begin(candidate_implicit_dimensions), std::end(candidate_implicit_dimensions),
                        std::begin(candidate_explicit_dimensions), std::end(candidate_explicit_dimensions),
                        std::back_inserter(undecided_dimensions),
                        [] (const std::tuple<int, int, int> &expl, const std::tuple<int, int, int> &impl) -> bool {
    return std::get<0>(expl) < std::get<0>(impl);
  });
//  assert(explicit_dimensions.size() + implicit_dimensions.size() + undecided_dimensions.size() == (size_t) (scattering->nb_output_dims - 1) / 2);
  assert(explicit_dimensions.size() <= (size_t) scattering->nb_input_dims);
  assert(undecided_dimensions.size() >= (scattering->nb_input_dims - explicit_dimensions.size()));

  // Choose first doublly-defined dimensions as being explicitly defined
  // and the rest as implicitly defined.
  for (int i = explicit_dimensions.size(); i < scattering->nb_input_dims; i++) {
    const std::tuple<int, int, int> &implicit_def = undecided_dimensions.front();
    int dimension = std::get<0>(implicit_def);
    undecided_dimensions.erase(std::begin(undecided_dimensions));
    auto explicit_it = std::find_if(std::begin(candidate_explicit_dimensions),
                                    std::end(candidate_explicit_dimensions),
                                    [dimension](const std::tuple<int, int, int> &element) {
      return std::get<0>(element) == dimension;
    });
    assert(explicit_it != std::end(candidate_explicit_dimensions));
    explicit_dimensions.push_back(*explicit_it);
  }
  std::copy(std::begin(undecided_dimensions), std::end(undecided_dimensions),
            std::back_inserter(implicit_dimensions));

  return std::make_pair(explicit_dimensions, implicit_dimensions);
}

std::tuple<int, ClayArray, int>
chlore_shifted(osl_relation_p scattering) {
  clay_array_p current_parameters = clay_array_malloc();
  clay_array_p beta = clay_beta_extract(scattering);

  // If normalized form is not
  //  b a b a b a b a b a p p c
  // [0 1 0 0 0 0 0 x 0 x N M c]
  // [      1 0 0 0 x 0 x N M c]
  // [          1 0 x 0 x N M c]
  //                * no explicit definition line for implicit dimension
  // [                1 0 N M c]
  // there is not much we can do right now, but this should not happen for
  // valid scheduling realtions.

  std::vector<std::tuple<int, int, int>> explicit_dimensions, implicit_dimensions;
  std::tie(explicit_dimensions, implicit_dimensions) = chlore_dimension_definitions(scattering);

  for (int depth = 0; depth < beta->size - 1; depth++) {
    clay_array_clear(current_parameters);

    auto depth_compare = [depth](const std::tuple<int, int, int> &element) -> bool{
      return std::get<0>(element) == depth;
    };
    auto expl_it = std::find_if(std::begin(explicit_dimensions), std::end(explicit_dimensions),
                                depth_compare);
    auto impl_it = std::find_if(std::begin(implicit_dimensions), std::end(implicit_dimensions),
                                depth_compare);
    assert((expl_it == std::end(explicit_dimensions)) ^ (impl_it == std::end(implicit_dimensions)));

    // Check explicit dimension shift.
    if (expl_it != std::end(explicit_dimensions)) {
      bool shifted = false;
      clay_array_clear(current_parameters);
      int row = std::get<1>(*expl_it);

      for (int i = scattering->nb_columns - scattering->nb_parameters - 1;
           i < scattering->nb_columns - 1; i++) {
        int value = osl_int_get_si(scattering->precision, scattering->m[row][i]);
        clay_array_add(current_parameters, value);
        if (value != 0) {
          shifted = true;
        }
      }
      int constant  = osl_int_get_si(scattering->precision,
                                     scattering->m[row][scattering->nb_columns - 1]);
      if (constant != 0) {
        shifted = true;
      }

      if (shifted) {
        // return parameters and value
        return std::make_tuple(depth + 1,
                               ClayArray(current_parameters),
                               constant);
      }
    } else if (impl_it != std::end(implicit_dimensions)) {
      bool shifted = false;
      clay_array_clear(current_parameters);
      int row_1 = std::get<1>(*impl_it);
      int row_2 = std::get<2>(*impl_it);

      int factor_1 = osl_int_get_si(scattering->precision, scattering->m[row_1][2*depth + 2]);
      int factor_2 = osl_int_get_si(scattering->precision, scattering->m[row_2][2*depth + 2]);

      for (int i = scattering->nb_columns - scattering->nb_parameters - 1;
           i < scattering->nb_columns; i++) {
        int value_1 = osl_int_get_si(scattering->precision, scattering->m[row_1][i]);
        int value_2 = osl_int_get_si(scattering->precision, scattering->m[row_2][i]);

        if (((value_1 % factor_1) == 0) && ((value_2 % factor_2) == 0) &&
            (value_1 / factor_1 == value_2 / factor_2) && value_1 != 0) {
          clay_array_add(current_parameters, value_1 / -factor_1);
          shifted = true;
        } else {
          clay_array_add(current_parameters, 0);
        }
      }
      // Last value in current_parameters is actually a constant shift.
      int constant = current_parameters->data[current_parameters->size - 1];
      current_parameters->size -= 1;

      if (shifted) {
        return std::make_tuple(depth + 1,
                               ClayArray(current_parameters),
                               constant);
      }
    }
  }
  clay_array_free(beta);
  clay_array_free(current_parameters);

  return std::make_tuple(-1, ClayArray(), 0);
}

std::tuple<ClayArray, int, ClayArray, int>
lookup_shift(osl_statement_p statement) {
  for (osl_relation_p scattering = statement->scattering; scattering != NULL;
       scattering = scattering->next) {
    clay_array_p beta = clay_beta_extract(scattering);
    std::tuple<int, ClayArray, int> found = chlore_shifted(scattering);
    if (std::get<0>(found) != -1) {
      return std::tuple_cat(std::make_tuple(ClayArray(beta)), found);
    }
  }
  return std::make_tuple(ClayArray(), -1, ClayArray(), 0);
}

// TODO: generalize with lookup_shift
std::tuple<ClayArray, int, int, int, int>
lookup_skew(osl_statement_p statement) {
  for (osl_relation_p scattering = statement->scattering; scattering != NULL;
       scattering = scattering->next) {
    std::tuple<ClayArray, int, int, int, int> found = chlore_skewed(scattering);
    if (std::get<1>(found) != TRANSFORMATION_NOT_FOUND) {
      return found;
    }
  }
  return std::make_tuple(ClayArray(), -1, -1, 0, 0);
}

inline std::vector<std::tuple<ClayArray, int, int>>
lookup_stripmine_sizes(osl_scop_p scop, osl_statement_p statement) {
  return chlore_lookup_aii(scop, statement, true, chlore_extract_stripmine_size);
}

inline std::vector<std::tuple<ClayArray, int, int>>
lookup_grains(osl_scop_p scop, osl_statement_p statement) {
  return chlore_lookup_aii(scop, statement, false, chlore_extract_grain);
}

inline std::vector<std::tuple<ClayArray, int, int>>
lookup_pseudo_stripmine_consants(osl_scop_p scop, osl_statement_p statement) {
  return chlore_lookup_aii(scop, statement, true, chlore_extract_pseudo_stripmine_constant);
}

// assumes normalized
std::tuple<int, int, int>
chlore_reshaped(osl_relation_p relation) {
  std::vector<std::tuple<int, int, int>> explicit_dimensions, implicit_dimensions;
  std::tie(explicit_dimensions, implicit_dimensions) = chlore_dimension_definitions(relation);
  clay_array_p beta = clay_beta_extract(relation);
  ClayArray raiibeta(beta); // RAII

  for (int depth = 0; depth < beta->size - 1; depth++) {
    auto depth_compare = [depth](const std::tuple<int, int, int> &element) -> bool{
      return std::get<0>(element) == depth;
    };
    auto expl_it = std::find_if(std::begin(explicit_dimensions), std::end(explicit_dimensions),
                                depth_compare);
    auto impl_it = std::find_if(std::begin(implicit_dimensions), std::end(implicit_dimensions),
                                depth_compare);
    assert((expl_it == std::end(explicit_dimensions)) ^ (impl_it == std::end(implicit_dimensions)));

    if (expl_it != std::end(explicit_dimensions)) {
      int row = std::get<1>(*expl_it);

      for (int j = 0; j < relation->nb_input_dims; ++j) {
        if (j == depth)
          continue;
        int value = osl_int_get_si(relation->precision,
                                   relation->m[row][relation->nb_output_dims + 1 + j]);
        if (value != 0) {
          return std::make_tuple(depth + 1, j + 1, value);
        }
      }
    } else if (impl_it != std::end(implicit_dimensions)) {
      int row_1 = std::get<1>(*impl_it);
      int row_2 = std::get<2>(*impl_it);

      int factor_1 = osl_int_get_si(relation->precision, relation->m[row_1][2*depth + 2]);
      int factor_2 = osl_int_get_si(relation->precision, relation->m[row_2][2*depth + 2]);

      for (int j = 0; j < relation->nb_input_dims; ++j) {
        if (j == depth)
          continue;

        int value_1 = osl_int_get_si(relation->precision,
                                     relation->m[row_1][relation->nb_output_dims + 1 + j]);
        int value_2 = osl_int_get_si(relation->precision,
                                     relation->m[row_2][relation->nb_output_dims + 1 + j]);

        if (((value_1 % factor_1) == 0) && ((value_2 % factor_2) == 0) &&
            (value_1 / factor_1 == value_2 / factor_2) && value_1 != 0) {
          return std::make_tuple(depth + 1, j + 1, value_1 / -factor_1);
        }
      }
    }
  }

  return std::make_tuple(TRANSFORMATION_NOT_FOUND, -1, -1);
}

std::tuple<ClayArray, int, int, int>
lookup_reshape(osl_scop_p scop, osl_statement_p statement,
               std::vector<ChloreBetaTransformation> &commands, clay_options_p options) {
  for (osl_relation_p scattering = statement->scattering; scattering != NULL;
       scattering = scattering->next) {
    std::tuple<int, int, int> found = chlore_reshaped(scattering);
    if (std::get<0>(found) != TRANSFORMATION_NOT_FOUND) {
      clay_array_p beta = clay_beta_extract(scattering);
      int source, target, amount;
      std::tie(source, target, amount) = found;
      if (chlore_try_transformation(scop, clay_reshape, beta, source, target, amount, options)) {
        return std::tuple_cat(std::make_tuple(ClayArray(beta)), found);
      } else {
        clay_array_p split_beta = chlore_detach_statement_from_loop(scop, beta, commands, options);
        clay_array_add(split_beta, 0);
        clay_array_free(beta);
        clay_beta_normalize(scop);
        return std::tuple_cat(std::make_tuple(ClayArray(split_beta)), found);
      }
    }
  }
  return std::make_tuple(ClayArray(), TRANSFORMATION_NOT_FOUND, -1, -1);
}

// Assumes normalized relation
std::tuple<int, int, int>
chlore_implicitly_skewed(osl_relation_p relation) {
  int nb_explicit_dims = 0;

  for (int i = 0; i < relation->nb_rows; i++) {
    if (osl_int_zero(relation->precision, relation->m[i][0]))
      nb_explicit_dims++;
    else
      break;
  }
  nb_explicit_dims = (nb_explicit_dims - 1) / 2;  // do not count betas
//  assert(nb_explicit_dims == relation->nb_input_dims);

  int nb_implicit_dims = (relation->nb_output_dims - 1) / 2 - nb_explicit_dims;

  if (nb_implicit_dims == 0)
    return std::make_tuple(TRANSFORMATION_NOT_FOUND, -1, -1);

  for (int j = 0; j < nb_explicit_dims; j++) {
    int row = 2*j + 1;
    for (int i = 0; i < nb_implicit_dims; i++) {
      int column = 2 + 2 * (nb_explicit_dims + i);
      int value = osl_int_get_si(relation->precision, relation->m[row][column]);
      if (value != 0) {
        return std::make_tuple(j + 1, i + nb_explicit_dims + 1, value);
      }
    }
  }

  return std::make_tuple(TRANSFORMATION_NOT_FOUND, -1, -1);
}

std::tuple<ClayArray, int, int, int>
lookup_implicit_skew(osl_statement_p statement) {
  for (osl_relation_p scattering = statement->scattering; scattering != nullptr;
       scattering = scattering->next) {
    std::tuple<int, int, int> found = chlore_implicitly_skewed(scattering);
    if (std::get<0>(found) != TRANSFORMATION_NOT_FOUND){
      return std::tuple_cat(std::make_tuple(ClayArray(clay_beta_extract(scattering))), found);
    }
  }
  return std::make_tuple(ClayArray(), TRANSFORMATION_NOT_FOUND, -1, -1);
}

int chlore_unembeddable(osl_scop_p scop, clay_array_p beta) {
  osl_statement_p statement = NULL, stmt;
  osl_relation_p scattering = NULL, scat;
  int i, depth;
  int row_1, row_2;
  clay_array_p beta_prefix;

  if (!scop || !beta)
    return CLAY_ERROR_BETA_NOT_FOUND;

  if (beta->size <= 1)
    return CLAY_ERROR_DEPTH_OVERFLOW;

  depth = beta->size - 2;
  beta_prefix = clay_array_clone(beta);
  beta_prefix->size -= 1;

  for (stmt = scop->statement; stmt != NULL;
       stmt = stmt->next) {
    for (scat = stmt->scattering; scat != NULL;
         scat = scat->next) {
      clay_array_p scattering_beta = clay_beta_extract(scat);
      if (clay_beta_equals(scattering_beta, beta)) {
        statement = stmt;
        scattering = scat;
      }
      clay_array_free(scattering_beta);
    }
  }
  if (statement == NULL || scattering == NULL)
    return CLAY_ERROR_BETA_NOT_FOUND;

  if (beta->size != (scattering->nb_output_dims + 1) / 2)
    return CLAY_ERROR_NOT_BETA_STMT;

  row_1 = -1;
  row_2 = -1;
  for (i = 0; i < scattering->nb_rows; i++) {
    if (!osl_int_zero(scattering->precision, scattering->m[i][2 * depth + 2])) {
      if (row_1 == -1) {
        row_1 = i;
        continue;
      } else if (row_2 == -1) {
        row_2 = i;
        continue;
      } else {
        return CLAY_ERROR_WRONG_COEFF;
      }
    }
  }
  if (row_1 == -1 || row_2 == -1)
    return CLAY_ERROR_WRONG_COEFF;

  for (i = 1; i < scattering->nb_columns; i++) {
    if (i == 2 * depth + 2)

      continue;
    if (!osl_int_zero(scattering->precision, scattering->m[row_1][i]))
      return CLAY_ERROR_WRONG_COEFF;
    if (!osl_int_zero(scattering->precision, scattering->m[row_2][i]))
      return CLAY_ERROR_WRONG_COEFF;
  }
  if (!osl_int_one(scattering->precision, scattering->m[row_1][0]))
    return CLAY_ERROR_WRONG_COEFF;
  if (!osl_int_one(scattering->precision, scattering->m[row_2][0]))
    return CLAY_ERROR_WRONG_COEFF;

  for (stmt = scop->statement; stmt != NULL;
       stmt = stmt->next) {
    for (scat = stmt->scattering; scat != NULL;
         scat = scat->next) {
      if (clay_beta_check_relation(scat, beta_prefix)) {
        clay_array_p local_beta = clay_beta_extract(scat);
        if (!clay_beta_equals(beta, local_beta)) {
          clay_array_free(local_beta);
          return CLAY_ERROR_WRONG_BETA;
        }
        clay_array_free(local_beta);
      }
    }
  }

  return CLAY_SUCCESS;
}

int chlore_extract_embed(osl_scop_p scop, clay_array_p beta) {
  return chlore_unembeddable(scop, beta) == CLAY_SUCCESS;
}

optional<ClayArray>
chlore_unembedded(osl_scop_p scop, osl_statement_p stmt,
                  std::vector<ChloreBetaTransformation> &commands, clay_options_p options) {
  for (osl_relation_p scattering = stmt->scattering;
       scattering != NULL; scattering = scattering->next) {
    clay_array_p beta = clay_beta_extract(scattering);

    int r = chlore_unembeddable(scop, beta);
    if (r == CLAY_ERROR_WRONG_BETA) {
      clay_array_p split_beta = chlore_detach_statement_until_depth(scop, beta, beta->size - 1, commands, options);
      for (int i = split_beta->size; i < beta->size; i++)
        clay_array_add(split_beta, 0);
      assert(chlore_unembeddable(scop, split_beta) == CLAY_SUCCESS);
      clay_array_free(beta);
      return make_optional(ClayArray(split_beta));
    } else if (r == CLAY_SUCCESS) {
      return make_optional(ClayArray(beta));
    }

    clay_array_free(beta);
  }
  return optional_empty();
}


std::tuple<int, int>
chlore_fix_diagonal(osl_relation_p relation) {
  std::vector<std::tuple<int, int, int>> explicit_dimensions;
  std::tie(explicit_dimensions, std::ignore) = chlore_dimension_definitions(relation);

  for (int i = 0; i < relation->nb_input_dims; i++) {
    auto it = std::find_if(std::begin(explicit_dimensions), std::end(explicit_dimensions),
                           [i](const std::tuple<int, int, int> &element) {
      return std::get<0>(element) == i;
    });
    assert(it != std::end(explicit_dimensions) && "couldn't find a corresponding explicit dimension; relation is invalid");
    int row = std::get<1>(*it);
    int column = 1 + relation->nb_output_dims + i;
    int value = osl_int_get_si(relation->precision, relation->m[row][column]);
    assert(value != 0 && "input dimension part is suspicious, possibly invalid relation");
    if (value != 1) {
      return std::make_tuple(i + 1, value);
    }
  }
  return std::make_tuple(TRANSFORMATION_NOT_FOUND, -1);
}

std::tuple<ClayArray, int, int>
lookup_diagonal_elements(osl_statement_p statement) {
  for (osl_relation_p scattering = statement->scattering; scattering != nullptr;
       scattering = scattering->next) {
    std::tuple<int, int> found = chlore_fix_diagonal(scattering);
    if (std::get<0>(found) != TRANSFORMATION_NOT_FOUND) {
      return std::tuple_cat(std::make_tuple(ClayArray(clay_beta_extract(scattering))), found);
    }
  }
  return std::make_tuple(ClayArray(), TRANSFORMATION_NOT_FOUND, -1);
}

static optional<std::pair<ClayArray, ClayArray>> chlore_find_first_beta_mismatch(
    osl_scop_p original, osl_scop_p transformed, clay_array_p prefix) {
  osl_statement_p original_stmt = original->statement;
  osl_statement_p transformed_stmt = transformed->statement;

  int nb_stmts = 0;
  for (osl_statement_p s = original->statement; s != NULL; s = s->next) {
    ++nb_stmts;
  }

  clay_array_p candidate_original_beta = NULL;
  clay_array_p candidate_transformed_beta = NULL;

  for (int i = 0; i < nb_stmts; i++) {
    int nb_scatterings = 0;
    for (osl_relation_p r = original_stmt->scattering; r != NULL; r = r->next)
      ++nb_scatterings;

    osl_relation_p original_rel = original_stmt->scattering;
    osl_relation_p transformed_rel = transformed_stmt->scattering;
    for (int j = 0; j < nb_scatterings; j++) {

      if (clay_beta_check_relation(transformed_rel, prefix)) {
        clay_array_p original_beta = clay_beta_extract(original_rel);
        clay_array_p transformed_beta = clay_beta_extract(transformed_rel);
        assert(transformed_beta->size >= prefix->size);
        assert(original_beta->size >= prefix->size);
        // Too long for a prefix
        if (transformed_beta->size == prefix->size) {
          clay_array_free(original_beta);
          clay_array_free(transformed_beta);
          continue;
        }
        for (int k = 0; k < prefix->size + 1; k++) {
          if (transformed_beta->data[k] != original_beta->data[k]) {
            if (candidate_original_beta) {
              int unused;
              if (clay_beta_compare(transformed_beta, candidate_transformed_beta, &unused) > 0) {
                clay_array_free(candidate_original_beta);
                clay_array_free(candidate_transformed_beta);
                candidate_original_beta = original_beta;
                candidate_transformed_beta = transformed_beta;
              }
            } else {
              candidate_original_beta = original_beta;
              candidate_transformed_beta = transformed_beta;
            }
//            return make_optional(std::make_pair(ClayArray(original_beta), ClayArray(transformed_beta)));
          }
        }
        // Full prefix match, location is already correct at this depth
      }

      original_rel = original_rel->next;
      transformed_rel = transformed_rel->next;
    }

    original_stmt = original_stmt->next;
    transformed_stmt = transformed_stmt->next;
  }

  if (candidate_original_beta) {
    return make_optional(std::make_pair(ClayArray(candidate_original_beta),
                                        ClayArray(candidate_transformed_beta)));
  } else {
    return optional_empty();
  }
}

static clay_array_p chlore_find_first_split_away(
    osl_scop_p original, osl_scop_p transformed, clay_array_p prefix) {
  osl_statement_p original_stmt = original->statement;
  osl_statement_p transformed_stmt = transformed->statement;

  int nb_stmts = 0;
  for (osl_statement_p s = original->statement; s != NULL; s = s->next) {
    ++nb_stmts;
  }

  for (int i = 0; i < nb_stmts; i++) {
    int nb_scatterings = 0;
    for (osl_relation_p r = original_stmt->scattering; r != NULL; r = r->next)
      ++nb_scatterings;

    osl_relation_p original_rel = original_stmt->scattering;
    osl_relation_p transformed_rel = transformed_stmt->scattering;
    for (int j = 0; j < nb_scatterings; j++) {

      if (clay_beta_check_relation(original_rel, prefix)) {
        if (!clay_beta_check_relation(transformed_rel, prefix)) {
          return clay_beta_extract(original_rel);
        }
      }

      original_rel = original_rel->next;
      transformed_rel = transformed_rel->next;
    }

    original_stmt = original_stmt->next;
    transformed_stmt = transformed_stmt->next;
  }

  return NULL;
}

static bool chlore_has_match_at_prefix(
    osl_scop_p original, osl_scop_p transformed, clay_array_p prefix, clay_array_p transfomed_prefix, clay_array_p active_beta) {
  osl_statement_p original_stmt = original->statement;
  osl_statement_p transformed_stmt = transformed->statement;

  int nb_stmts = 0;
  for (osl_statement_p s = original->statement; s != NULL; s = s->next) {
    ++nb_stmts;
  }

  for (int i = 0; i < nb_stmts; i++) {
    int nb_scatterings = 0;
    for (osl_relation_p r = original_stmt->scattering; r != NULL; r = r->next)
      ++nb_scatterings;

    osl_relation_p original_rel = original_stmt->scattering;
    osl_relation_p transformed_rel = transformed_stmt->scattering;
    for (int j = 0; j < nb_scatterings; j++) {

      if (clay_beta_check_relation(original_rel, prefix)) {
        if (clay_beta_check_relation(transformed_rel, transfomed_prefix)) {
          int unused;
          clay_array_p original_beta = clay_beta_extract(original_rel);
          if (clay_beta_compare(original_beta, active_beta, &unused) != 0) {
            clay_array_free(original_beta);
            return true;
          }
          clay_array_free(original_beta);
        }
      }

      original_rel = original_rel->next;
      transformed_rel = transformed_rel->next;
    }

    original_stmt = original_stmt->next;
    transformed_stmt = transformed_stmt->next;
  }
  return false;
}

void chlore_fix_beta_at_dept2(osl_scop_p original, osl_scop_p transformed,
                              std::vector<ChloreBetaTransformation> &commands, clay_options_p options,
                              clay_array_p prefix) {
  while (true) {
    clay_array_p original_beta, transformed_beta;
    optional<std::pair<ClayArray, ClayArray>> mismatch
        = chlore_find_first_beta_mismatch(original, transformed, prefix); // prefix [], depth 1.
    if (!mismatch) {
      break;
    }
    original_beta = static_cast<std::pair<ClayArray, ClayArray> &>(mismatch).first;
    transformed_beta = static_cast<std::pair<ClayArray, ClayArray> &>(mismatch).second;

    clay_array_p split_beta = chlore_detach_statement_until_depth(original, original_beta, prefix->size + 1, commands, options);

    int last_original_child_beta = chlore_last_statement_beta_dim(original, prefix);

    // If there is a statement with the same prefix at position already, fuse with it.
    assert(split_beta->size != 0);
    assert(split_beta->size > prefix->size);

    clay_array_p fusion_target = clay_array_clone(prefix);
    clay_array_add(fusion_target, transformed_beta->data[prefix->size]);
    clay_array_p transformed_fusion_target = clay_array_clone(fusion_target);
    // If split at the current level happend before fusion target beta, all statements that were in the
    // old target were offset by +1, for which we have to check.
    if (split_beta->data[prefix->size] <= fusion_target->data[prefix->size]) {
      fusion_target->data[prefix->size] += 1;
    }

    if (chlore_has_match_at_prefix(original, transformed, fusion_target, transformed_fusion_target, split_beta)) {
      assert(transformed_beta->data[prefix->size] <= last_original_child_beta); // if not, just put the statement last in the loop...
      if (split_beta->data[prefix->size] != fusion_target->data[prefix->size] + 1) { // Do not reorder if already there
        int old_size = split_beta->size;
        split_beta->size = prefix->size + 1; // find_first_mismatch returns only beta-vectors for which prefix is shorter than the vector, this is safe + assertion above
        chlore_put_statement_after(original, fusion_target->data[prefix->size], split_beta, commands, options);
        split_beta->size = old_size;
      }

      ChloreBetaTransformation fusion;
      fusion.kind   = ChloreBetaTransformation::FUSE;
      fusion.target = ClayArray(transformed_fusion_target);
      // no need to compute undo statements here, spare computation.
      // fusion.first_loop_size = chlore_last_statement_beta_dim(scop, fusion_target);
      commands.push_back(fusion);
      clay_fuse(original, transformed_fusion_target, options);

      clay_array_free(split_beta);
      split_beta = clay_array_clone(transformed_fusion_target);
    } else {
    // Otherwise just put at position.
      if (split_beta->data[prefix->size] != transformed_beta->data[prefix->size]) {
        int old_size = split_beta->size;
        split_beta->size = prefix->size + 1;
        if (transformed_beta->data[prefix->size] == 0) {
          chlore_put_statement_first(original, split_beta, commands, options);
        } else {
          if (transformed_beta->data[prefix->size] < split_beta->data[prefix->size]) {
            chlore_put_statement_after(original, transformed_beta->data[prefix->size] - 1,
                split_beta, commands, options);
          } else {
            chlore_put_statement_after(original, transformed_beta->data[prefix->size],
                split_beta, commands, options);
          }
        }
        split_beta->data[split_beta->size - 1] = transformed_beta->data[prefix->size];
        split_beta->size = old_size;
      }
      clay_array_free(fusion_target);
    }

    // Split away everything that has prefix in original, but not in transformed.
    // If this is done outside the main loop, it may lead to mutually undoing reorders on two loops.
    while (true) {
      clay_array_p split_away_beta = chlore_find_first_split_away(original, transformed, split_beta);
      if (!split_away_beta) {
        break;
      }
      chlore_detach_statement_until_depth(original, split_away_beta, prefix->size + 1, commands, options);
      clay_array_free(split_away_beta);
    }
    clay_array_free(split_beta);

    // beta-vectors might have changed, so we must restart the inner loop

  }
}


static void chlore_match_betas_r(osl_scop_p original, osl_scop_p transformed,
                                 std::vector<ChloreBetaTransformation> &commands,
                                 clay_options_p options, clay_array_p prefix) {
  int nb_children = chlore_last_statement_beta_dim(transformed, prefix) + 1;
  clay_array_p child_prefix = clay_array_clone(prefix);
  clay_array_add(child_prefix, -1);
  for (int i = 0; i < nb_children; i++) {
    child_prefix->data[child_prefix->size - 1] = i;

//    chlore_fix_beta_at_depth(original, transformed, commands, options, child_prefix, prefix);

    chlore_fix_beta_at_dept2(original, transformed, commands, options, child_prefix);

    chlore_match_betas_r(original, transformed, commands, options, child_prefix);
  }
  clay_array_free(child_prefix);
}

void chlore_match_betas(osl_scop_p original, osl_scop_p transformed,
                        std::vector<ChloreBetaTransformation> &commands, clay_options_p options) {

  clay_array_p empty_prefix = clay_array_malloc();
  chlore_fix_beta_at_dept2(original, transformed, commands, options, empty_prefix);

  chlore_match_betas_r(original, transformed, commands, options, empty_prefix);
  clay_array_free(empty_prefix);
}

// Find first explicitly-defined dimension.
int chlore_find_first_explicit(osl_statement_p stmt, clay_array_p beta) {
  int explicit_dim = -1;
  osl_relation_p scattering;
  osl_statement_p unused;
  clay_beta_find_relation(stmt, beta, &unused, &scattering);
  for (int i = 1; i < scattering->nb_output_dims; i += 2) {
    for (int j = 0; j < scattering->nb_rows; j++) {
      if (!osl_int_zero(scattering->precision, scattering->m[j][0]))
        continue;
      if (!osl_int_zero(scattering->precision, scattering->m[j][1 + i])) {
        explicit_dim = (i + 1) / 2;
        break;
      }
    }
  }
  assert(explicit_dim != -1);

  return explicit_dim;
}

void chlore_add_commands(std::deque<std::string> &first,
                         std::vector<ChloreBetaTransformation> &original_commands) {
  std::stringstream ss;
  for (auto cmd : original_commands) {
    ss << cmd;
    first.push_back(ss.str());
    ss.str("");
  }

  original_commands.clear();
}

void chlore_add_inverted_commands(std::deque<std::string> &last,
                                  std::vector<ChloreBetaTransformation> &transformed_commands) {
  std::stringstream ss;
  std::deque<ChloreBetaTransformation> inverted_commands =
      chlore_complementary_beta_transformation(transformed_commands);
  for (auto it = inverted_commands.rbegin(), eit = inverted_commands.rend(); it != eit; ++it) {
    ss << *it;
    last.push_front(ss.str());
    ss.str("");
  }

  transformed_commands.clear();
}

std::string chlore_find_sequence(osl_scop_p original, osl_scop_p transformed) {
  osl_statement_p stmt, original_stmt, transformed_stmt;
  int nb_stmts = 0;
  int i;

  std::deque<std::string> first, last;

  clay_options_p options = clay_options_malloc();
  options->normalize = 1;

  if (!chlore_check_compatible(original, transformed)) {
    fprintf(stderr, "NO SEQUENCE\n");
  }

  clay_scop_normalize(original);
  clay_scop_normalize(transformed);

  for (stmt = original->statement; stmt != NULL; stmt = stmt->next) {
    nb_stmts++;
  }

  original_stmt = original->statement;
  transformed_stmt = transformed->statement;
  for (i = 0; i < nb_stmts; i++) {

    while (1) {
      std::vector<ChloreBetaTransformation> original_commands, transformed_commands;

      optional<ClayArray> original_embed = chlore_unembedded(original, original_stmt,
                                                             original_commands, options);
      optional<ClayArray> transformed_embed = chlore_unembedded(transformed, transformed_stmt,
                                                                transformed_commands, options);
      if (original_embed) {
        ClayArray beta = static_cast<ClayArray>(transformed_embed);

        std::stringstream ss;
        ss << "unembed(" << beta << ");\n";
        first.push_back(ss.str());

        clay_unembed(original, beta, options);
      }

      if (transformed_embed) {
        ClayArray beta = static_cast<ClayArray>(transformed_embed);
        clay_array_p cbeta = static_cast<clay_array_p>(beta);
        cbeta->size -= 1;

        chlore_add_inverted_commands(last, transformed_commands);

        std::stringstream ss;
        ss << "embed(" << beta << ");\n";
        last.push_front(ss.str());

        cbeta->size += 1;
        clay_unembed(transformed, beta, options);
      }

      if (original_embed || transformed_embed) {
        continue;
      }

      // Try for iss
      optional<std::tuple<ClayArray, ClayList>> original_iss =
        lookup_iss_conditions(original, original_stmt, original_commands, options);

      // TODO: we also have to try finding all possible isses, not only one? ++ if on both sides, do not include; -- requires multiple calls for reorder with hardly predictable effect on beta-vectors.

      optional<std::tuple<ClayArray, ClayList>> transformed_iss =
        lookup_iss_conditions(transformed, transformed_stmt, transformed_commands, options);

      if (original_iss) {
        auto original_tuple = static_cast<std::tuple<ClayArray, ClayList>>(original_iss);

        ClayArray beta;
        std::tie(beta, std::ignore) = original_tuple;

        chlore_add_commands(first, original_commands);

        std::stringstream ss;
        ss << "collapse(" << beta << ");\n";
        first.push_back(ss.str());

        clay_collapse(original, beta, options);

      }

      if (transformed_iss) {
        auto transformed_tuple = static_cast<std::tuple<ClayArray, ClayList>>(transformed_iss);

        ClayArray beta;
        ClayList condition;
        std::tie(beta, condition) = transformed_tuple;

        chlore_add_inverted_commands(last, transformed_commands);

        std::stringstream ss;
        ss << "iss(" << beta << ", " << condition << ");\n";
        last.push_front(ss.str());
        clay_collapse(transformed, beta, options);
      }

      if (original_iss || transformed_iss) {
        continue;
      }

      // TODO: stripmine/linearize are loop transormations and may be blocked if this loop
      // was fused with non-stripmined loop.  Use the same separation technique as in
      // iss/collapse to ensure it is always found.

      // Check for stripmine/linearize
      std::vector<std::tuple<ClayArray, int, int>> original_sizes =
          lookup_stripmine_sizes(original, original_stmt);
      std::vector<std::tuple<ClayArray, int, int>> transformed_sizes =
          lookup_stripmine_sizes(transformed, transformed_stmt);

      vector_pair_remove_identical_items(original_sizes, transformed_sizes);

      for (auto const &data : original_sizes) {
        ClayArray beta;
        int depth;
        std::tie(beta, depth, std::ignore) = data;

        std::stringstream ss;
        ss << "linearize(" << beta << ", " << depth << ");\n";
        first.push_back(ss.str());

        clay_linearize(original, beta, depth, options);
      }

      for (auto const &data : transformed_sizes) {
        ClayArray beta;
        int depth;
        int size;
        std::tie(beta, depth, size) = data;

        std::stringstream ss;
        ss << "stripmine(" << beta << ", " << depth << ", " << size << ");\n";
        last.push_front(ss.str());

        clay_linearize(transformed, beta, depth, options);
      }

      if (transformed_sizes.size() != 0 ||
          original_sizes.size() != 0) {
        continue;
      }


      // Check for pseudo-stripmine (cx >= 0, cx <= 0)
      // requires skewing to denormalized form.

      optional<std::tuple<ClayArray, int, int>> original_pseudo_sm =
          lookup_pseudo_stripmine_constants2(original, original_stmt, original_commands, options);
      optional<std::tuple<ClayArray, int, int>> transformed_pseudo_sm =
          lookup_pseudo_stripmine_constants2(transformed, transformed_stmt, transformed_commands, options);

      // TODO: create sequence for original

      if (transformed_pseudo_sm) {
        ClayArray beta;
        int depth;
        auto data = static_cast<std::tuple<ClayArray, int, int>>(transformed_pseudo_sm);
        std::tie(beta, depth, std::ignore) = data;

        int explicit_dim = chlore_find_first_explicit(transformed_stmt, beta);
        assert(explicit_dim != depth);

        chlore_add_inverted_commands(last, transformed_commands);

        std::stringstream ss;
        int target_depth;
        if (explicit_dim < depth) {
          int current = depth;
          while (current != explicit_dim) {
            ss << "interchange(" << beta << ", " << depth - current + explicit_dim
               << ", " << depth - (current - 1) + explicit_dim << ", 0);\n";
            last.push_front(ss.str());
            ss.str("");
            clay_interchange(transformed, beta, current, current - 1, 0, options);
            --current;
          }
          target_depth = explicit_dim;
        } else {
          int current = depth;
          while (current + 1 != explicit_dim) {
            ss << "interchange(" << beta << ", " << (depth + explicit_dim - 1 - current)
               << ", " << (depth + explicit_dim - 2 - current) << ", 0);\n";
            last.push_front(ss.str());
            ss.str("");
            clay_interchange(transformed, beta, current, current + 1, 0, options);
            ++current;
          }
          target_depth = explicit_dim - 1;
        }

        ss << "skew(" << beta << ", " << target_depth << ", " << target_depth + 1 << ", 1);\n";
        last.push_front(ss.str());
        ss.str("");

        ss << "stripmine(" << beta << ", " << target_depth << ", 1);\n";
        last.push_front(ss.str());
        ss.str("");

        clay_skew(transformed, beta, target_depth, target_depth + 1, -1, options);

        // If the beta that is removed during linearization is not zero, split away first.
        clay_array_p cbeta = static_cast<clay_array_p>(beta);
        if (target_depth < cbeta->size && cbeta->data[target_depth] != 0) {
          transformed_commands.clear();
          beta = ClayArray(chlore_detach_statement_until_depth(transformed,
                                      beta, target_depth, transformed_commands, options));
          chlore_add_inverted_commands(last, transformed_commands);
        }

        clay_linearize(transformed, beta, target_depth, options);
      }


      if (transformed_pseudo_sm) {
        continue;
      }


      // Check for grain/densify
      std::vector<std::tuple<ClayArray, int, int>> original_grains =
          lookup_grains(original, original_stmt);
      std::vector<std::tuple<ClayArray, int, int>> transformed_grains =
          lookup_grains(transformed, transformed_stmt);

      vector_pair_remove_identical_items(original_grains, transformed_grains);

      for (auto const &data : original_grains) {
        ClayArray beta;
        int depth;
        std::tie(beta, depth, std::ignore) = data;

        std::stringstream ss;
        ss << "densify(" << beta << ", " << depth << ");\n";
        first.push_back(ss.str());

        clay_densify(original, beta, depth, options);
      }

      for (auto const &data : transformed_grains) {
        ClayArray beta;
        int depth;
        int size;
        std::tie(beta, depth, size) = data;

        std::stringstream ss;
        ss << "grain(" << beta << ", " << depth << ", " << size << ");\n";
        last.push_front(ss.str());

        clay_densify(transformed, beta, depth, options);
      }

      if (original_grains.size() != 0 || transformed_grains.size() != 0) {
        continue;
      }

      clay_scop_normalize(original);
      clay_scop_normalize(transformed);


      // Shifts
      std::tuple<ClayArray, int, ClayArray, int> potential_shift =
          lookup_shift(original_stmt);
      if (std::get<1>(potential_shift) != -1) {
        ClayArray beta, parameters;
        int depth;
        int constant;
        std::tie(beta, depth, parameters, constant) = potential_shift;

        // Negate everything.
//        clay_array_p c_parameters = static_cast<clay_array_p>(parameters);
//        for (int k = 0; k < c_parameters->size; k++) {
//          c_parameters->data[k] = -c_parameters->data[k];
//        }
//        constant = -constant;

        std::stringstream ss;
        ss << "shift(" << beta << ", " << depth << ", "
           << parameters << ", " << constant << ");\n";
        first.push_back(ss.str());

        clay_shift(original, beta, depth, parameters, constant, options);

        continue;
      }

      potential_shift = lookup_shift(transformed_stmt);
      if (std::get<1>(potential_shift) != -1) {
        ClayArray beta, parameters;
        int depth;
        int constant;
        std::tie(beta, depth, parameters, constant) = potential_shift;

        std::stringstream ss;
        ss << "shift(" << beta << ", " << depth << ", "
           << parameters << ", " << constant << ");\n";
        last.push_front(ss.str());

        // Negate everything.
//        clay_array_p c_parameters = static_cast<clay_array_p>(parameters);
//        for (int k = 0; k < c_parameters->size; k++) {
//          c_parameters->data[k] = -c_parameters->data[k];
//        }
//        constant = -constant;

        clay_shift(transformed, beta, depth, parameters, constant, options);

        continue;
      }



      // Skew
      std::tuple<ClayArray, int, int, int, int> potential_skew =
          lookup_skew(original_stmt);
      if (std::get<1>(potential_skew) == INTERCHANGE_REQUESTED) {
        ClayArray beta;
        int depth_1, depth_2;
        std::tie(beta, std::ignore, std::ignore, depth_1, depth_2) = potential_skew;

        std::stringstream ss;
        ss << "interchange(" << beta << ", " << depth_1 << ", " << depth_2 << ", 0);\n";
        first.push_back(ss.str());

        clay_interchange(original, beta, depth_1, depth_2, 0, options);
        osl_statement_p unused_statement;
        osl_relation_p scattering;
        clay_beta_find_relation(original_stmt, beta, &unused_statement, &scattering);
        clay_relation_normalize_alpha(scattering);
        continue;
      } else if (std::get<1>(potential_skew) != TRANSFORMATION_NOT_FOUND) {
        ClayArray beta;
        int source, target, source_grain, target_grain;
        std::tie(beta, source, target, source_grain, target_grain) = potential_skew;
        std::stringstream ss;

        // TODO: use skew with non-one parameter instead of this.
        if (source_grain > 1) {
          ss << "grain(" << beta << ", " << source << ", " << source_grain << ");\n";
          clay_grain(original, beta, source, source_grain, options);
        } else if (source_grain < 0) {
          source_grain = -source_grain;
          ss << "reverse(" << beta << ", " << source << ");\n";
          ss << "grain(" << beta << ", " << source << ", " << source_grain << ");\n";
          clay_reverse(original, beta, source, options);
          clay_grain(original, beta, source, source_grain, options);
        }

        if (target_grain > 1) {
          ss << "grain(" << beta << ", " << target << ", " << target_grain << ");\n";
          clay_grain(original, beta, target, target_grain, options);
        } else if (target_grain < 0) {
          target_grain = -target_grain;
          ss << "reverse(" << beta << ", " << target << ");\n";
          clay_reverse(original, beta, target, options);
          if (target_grain != 1) {
            ss << "grain(" << beta << ", " << target << ", " << target_grain << ");\n";
            clay_grain(original, beta, target, target_grain, options);
          }
        }

        ss << "skew(" << beta << ", " << source << ", " << target << ", 1);\n";
        clay_skew(original, beta, target, source, 1, options);

        osl_statement_p unused_statement;
        osl_relation_p scattering;
        clay_beta_find_relation(original_stmt, beta, &unused_statement, &scattering);
        clay_relation_normalize_alpha(scattering);

        first.push_back(ss.str());
        continue;
      }

      potential_skew = lookup_skew(transformed_stmt);
      if (std::get<1>(potential_skew) == INTERCHANGE_REQUESTED) {
        ClayArray beta;
        int depth_1, depth_2;
        std::tie(beta, std::ignore, std::ignore, depth_1, depth_2) = potential_skew;

        std::stringstream ss;
        ss << "interchange(" << beta << ", " << depth_1 << ", " << depth_2 << ", 0);\n";
        last.push_front(ss.str());

        clay_interchange(transformed, beta, depth_1, depth_2, 0, options);
        osl_statement_p unused_statement;
        osl_relation_p scattering;
        clay_beta_find_relation(transformed_stmt, beta, &unused_statement, &scattering);
        clay_relation_normalize_alpha(scattering);
        continue;
      } else if (std::get<1>(potential_skew) != TRANSFORMATION_NOT_FOUND) {
        ClayArray beta;
        int source, target, source_grain, target_grain;
        std::tie(beta, source, target, source_grain, target_grain) = potential_skew;
        std::stringstream ss;

        if (source_grain > 1) {
          ss << "grain(" << beta << ", " << source << ", " << source_grain << ");\n";
          clay_grain(transformed, beta, source, source_grain, options);
        } else if (source_grain < 0) {
          source_grain = -source_grain;
          ss << "reverse(" << beta << ", " << source << ");\n";
          ss << "grain(" << beta << ", " << source << ", " << source_grain << ");\n";
          clay_reverse(transformed, beta, source, options);
          clay_grain(transformed, beta, source, source_grain, options);
        }

        if (target_grain > 1) {
          ss << "grain(" << beta << ", " << target << ", " << target_grain << ");\n";
          clay_grain(transformed, beta, target, target_grain, options);
        } else if (target_grain < 0) {
          target_grain = -target_grain;
          ss << "reverse(" << beta << ", " << target << ");\n";
          clay_reverse(transformed, beta, target, options);
          if (target_grain != 1) {
            ss << "grain(" << beta << ", " << target << ", " << target_grain << ");\n";
            clay_grain(transformed, beta, target, target_grain, options);
          }
        }

        ss << "skew(" << beta << ", " << source << ", " << target << ", -1);\n";
        clay_skew(transformed, beta, source, target, 1, options);
        clay_relation_normalize_alpha(transformed_stmt->scattering);

        osl_statement_p unused_statement;
        osl_relation_p scattering;
        clay_beta_find_relation(transformed_stmt, beta, &unused_statement, &scattering);
        clay_relation_normalize_alpha(scattering);
        last.push_front(ss.str());
        continue;
      }

      // Skew for implicitly-defined dimensions
      std::tuple<ClayArray, int, int, int> potential_iskew =
          lookup_implicit_skew(original_stmt);
      if (std::get<1>(potential_iskew) != TRANSFORMATION_NOT_FOUND) {
        ClayArray beta;
        int source, target, coefficient;
        std::tie(beta, source, target, coefficient) = potential_iskew;

        std::stringstream ss;
        ss << "skew(" << beta << ", " << source << ", "
           << target << ", " << coefficient << ");\n";
        first.push_back(ss.str());

        clay_skew(original, beta, source, target, coefficient, options);
        continue;
      }

      potential_iskew = lookup_implicit_skew(transformed_stmt);
      if (std::get<1>(potential_iskew) != TRANSFORMATION_NOT_FOUND) {
        ClayArray beta;
        int source, target, coefficient;
        std::tie(beta, source, target, coefficient) = potential_iskew;

        std::stringstream ss;
        ss << "skew(" << beta << ", " << source << ", "
           << target << ", " << -coefficient << ");\n";
        last.push_front(ss.str());

        clay_skew(transformed, beta, source, target, coefficient, options);
        continue;
      }



      // Reshape
      std::tuple<ClayArray, int, int, int> potential_reshape =
          lookup_reshape(original, original_stmt, original_commands, options);
      if (std::get<1>(potential_reshape) != TRANSFORMATION_NOT_FOUND) {
        ClayArray beta;
        int dim, input, coefficient;
        std::tie(beta, dim, input, coefficient) = potential_reshape;

        chlore_add_commands(first, original_commands);

        std::stringstream ss;
        ss << "reshape(" << beta << ", " << dim << ", "
           << input << ", " << coefficient << ");\n";
        first.push_back(ss.str());

        clay_reshape(original, beta, dim, input, -coefficient, options);
        continue;
      }

      potential_reshape = lookup_reshape(transformed, transformed_stmt, transformed_commands, options);
      if (std::get<1>(potential_reshape) != TRANSFORMATION_NOT_FOUND) {
        ClayArray beta;
        int dim, input, coefficient;
        std::tie(beta, dim, input, coefficient) = potential_reshape;

        chlore_add_inverted_commands(last, transformed_commands);

        std::stringstream ss;
        ss << "reshape(" << beta << ", " << dim << ", "
           << input << ", " << -coefficient << ");\n";
        last.push_front(ss.str());

        clay_reshape(transformed, beta, dim, input, coefficient, options);
        continue;
      }


      // Grain and reverse on the diagonal
      std::tuple<ClayArray, int, int> diagonal_element =
          lookup_diagonal_elements(original_stmt);
      if (std::get<1>(diagonal_element) != TRANSFORMATION_NOT_FOUND) {
        ClayArray beta;
        int dim;
        int amount;
        std::tie(beta, dim, amount) = diagonal_element;

        std::stringstream ss;

        if (amount < 0) {
          ss << "reverse(" << beta << ", " << dim << ");\n";

          clay_reverse(original, beta, dim, options);
          amount = -amount;
        }
        ss << "densify(" << beta << ", " << dim << ");\n";

        clay_densify(original, beta, dim, options);
        continue;
      }

      diagonal_element = lookup_diagonal_elements(transformed_stmt);
      if (std::get<1>(diagonal_element) != TRANSFORMATION_NOT_FOUND) {
        ClayArray beta;
        int dim;
        int amount;
        std::tie(beta, dim, amount) = diagonal_element;

        std::stringstream ss;

        if (amount < 0) {
          ss << "reverse(" << beta << ", " << dim << ");\n";

          clay_reverse(transformed, beta, dim, options);
          amount = -amount;
        }
        ss << "grain(" << beta << ", " << dim << ", " << amount << ");\n";

        clay_densify(transformed, beta, dim, options);
        continue;
      }


      // Can't do anything
      break;
    }

    original_stmt = original_stmt->next;
    transformed_stmt = transformed_stmt->next;
  }

  // At this point, all relations should be in the minimal form with the smallest possible number of values.
  // The only difference is in their beta-vectors, which may be fixed by split/fuse/reorder.
  if (!chlore_check_structure_compatible(original, transformed)) {
    fprintf(stderr, "Failed to recover alpha dimensions\n");
    return "<failed>";
  }

  std::vector<ChloreBetaTransformation> commands;
  chlore_match_betas(original, transformed, commands, options);

  std::stringstream ss;
  for (const std::string &s : first) {
    ss << s;
  }
  for (const ChloreBetaTransformation &transformation : commands) {
    ss << transformation;
  }
  for (const std::string &s : last) {
    ss << s;
  }
  return ss.str();
}

void chlore_relation_replace_extra_dimensions(osl_relation_p relation) {
  // Find normalized form.
  clay_relation_normalize_alpha(relation); // XXX: this may not be necessary

  std::vector<std::tuple<int, int, int>> explicit_definitions;
  std::tie(explicit_definitions, std::ignore) = chlore_dimension_definitions(relation);

  assert(explicit_definitions.size() == (size_t) relation->nb_input_dims && "some input dimensions are unused or conflicted, scheduling is invalid");

  for (int i = 0; i < relation->nb_rows; i++) {
    if (!osl_int_zero(relation->precision, relation->m[i][0]))
      continue;
    if (clay_util_is_row_beta_definition(relation, i))
      continue;
    auto explicit_it = std::find_if(std::begin(explicit_definitions), std::end(explicit_definitions),
                                    [i](const std::tuple<int, int, int> &element) {
      return std::get<1>(element) == i;
    });
    if (explicit_it != std::end(explicit_definitions))
      continue;

    // turn it into an a pair of complementary inequalities.
    osl_int_set_si(relation->precision,
                   &relation->m[i][0], 1);
    osl_relation_insert_blank_row(relation, -1);
    osl_int_set_si(relation->precision,
                   &relation->m[relation->nb_rows - 1][0], 1);
    // Negate by hand instead of using "negate_row" to ensure x >= 0, x <= 0 situation.
    for (int j = 1; j < relation->nb_columns; j++) {
      osl_int_oppose(relation->precision,
                     &relation->m[relation->nb_rows - 1][j],
                     relation->m[i][j]);
    }
  }

  // TODO: check if there is no explicit definition duplications or clashes.


  // Expect scheduling to have the input part with full column rang (global validity)
  // Only fix extra rows that may have been added by an optimizer.


  // Extract definitions in terms of input of explicitly-defined dimensions.

  // Check if has linearly dependent explicitly defined dimensions.
  // If it does have n, replace the last n explicit definitions by pairs
  // of inequalities turning them into implicit definitions.

  // Do the same for scalar alpha dimensions.
}

void chlore_scop_replace_extra_dimensions(osl_scop_p scop) {
  for (osl_statement_p stmt = scop->statement;
       stmt != NULL; stmt = stmt->next) {
    for (osl_relation_p scattering = stmt->scattering;
         scattering != NULL; scattering = scattering->next) {
      chlore_relation_replace_extra_dimensions(scattering);
    }
  }
}

void chlore_whiteboxing(osl_scop_p original, osl_scop_p transformed) {
  chlore_find_betas(original);
  chlore_scop_replace_extra_dimensions(original);
  chlore_find_betas(transformed);
  chlore_scop_replace_extra_dimensions(transformed);
  std::string sequence = chlore_find_sequence(original, transformed);
  osl_clay_p extension = osl_clay_malloc();
  extension->script = strdup(sequence.c_str());
  if (osl_generic_lookup(original->extension, OSL_URI_CLAY)) {
    osl_generic_remove(&original->extension, OSL_URI_CLAY);
  }
  osl_generic_add(&original->extension,
                  osl_generic_shell(extension, osl_clay_interface()));
}
