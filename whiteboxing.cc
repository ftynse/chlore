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

#include "beta.h"

// chunky loop optimization revealer ||
// chunku loop optimizer reverse engineering
// ChLORe

template <typename T>
class optional {
private:
  bool has_value;
  T value;
public:
  optional(const T &t) : has_value(true), value(t) {}
  optional() : has_value(false) {}

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

  operator bool () const {
    return value & 0x1;
  }

  operator T* () {
    return value & ~0x1;
  }

  operator const T* () const {
    return value & ~0x1;
  }
};

template <typename T>
optional<T> make_optional(T t) {
  return optional<T>(t);
}

template <typename T>
optional<T> make_empty() {
  return optional<T>();
}

char *clay_array_string(clay_array_p array);
char *clay_list_string(clay_list_p list);
int clay_list_equal(clay_list_p l1, clay_list_p l2);

template <typename T, T *(creator)(), void (deleter)(T *),
          T *(cloner)(T *), int (equality)(T *, T *), char *(printer)(T *)>
class OSLContainer {
public:
  OSLContainer() {
    object = creator();
  }

  OSLContainer(T *other) {
    object = other;
  }

  static OSLContainer copy(T *other) {
    T *clone = cloner(other);
    return OSLContainer(clone);
  }

  OSLContainer(const OSLContainer &other) {
    object = cloner(other.object);
  }

  OSLContainer(T &&other) {
    object = other.object;
    other.object = nullptr;
  }

  ~OSLContainer() {
    deleter(object);
  }

  OSLContainer &operator = (const OSLContainer &other) {
    deleter(object);
    object = cloner(other.object);
    return *this;
  }

  bool operator == (const OSLContainer &other) const {
    return equality(object, other.object);
  }

  bool operator != (const OSLContainer &other) const {
    return !equality(object, other.object);
  }

  operator T *() {
    return object;
  }

  operator T &() {
    return *object;
  }

  friend std::ostream &operator <<(std::ostream &out, const OSLContainer &container) {
    char *cstring = printer(container.object);
    out << cstring;
    free(cstring);
    return out;
  }

private:
  T *object;
};

typedef OSLContainer<clay_array_t, clay_array_malloc, clay_array_free, clay_array_clone, clay_array_equal, clay_array_string> ClayArray;
typedef OSLContainer<clay_list_t, clay_list_malloc, clay_list_free, clay_list_clone, clay_list_equal, clay_list_string> ClayList;


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
    out << "fuse " << transformation.target;
    break;

  case ChloreBetaTransformation::SPLIT:
    out << "split " << transformation.target << " @" << transformation.depth;
    break;

  case ChloreBetaTransformation::REORDER:
    out << "reorder " << transformation.target << " " << transformation.order;
  }
  out << "\n";
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


// TODO: move to clay
int clay_list_equal(clay_list_p l1, clay_list_p l2) {
  int i;

  if (l1->size != l2->size)
    return 0;

  for (i = 0; i < l1->size; i++) {
    if (!clay_array_equal(l1->data[i], l2->data[i]))
      return 0;
  }

  return 1;
}

template <typename Func, typename... Args>
int chlore_try_transformation(osl_scop_p scop, Func transformation, Args... arguments) {
  osl_scop_p copy = osl_scop_clone(scop);

  int result = transformation(scop, arguments...);
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


// TODO: move to clay
void clay_beta_find_relation(osl_statement_p start, clay_array_p beta,
                             osl_statement_p *stmt, osl_relation_p *scattering) {
  if (!stmt || !scattering)
    return;

  *stmt = NULL;
  *scattering = NULL;

  if (!start) {
    return;
  }

  osl_relation_p scat;
  *stmt = clay_beta_find(start, beta);
  if (!stmt)
    return;

  for (scat = (*stmt)->scattering; scat != NULL; scat = scat->next) {
    if (clay_beta_check_relation(scat, beta)) {
      *scattering = scat;
      return;
    }
  }
}

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

char *clay_list_string(clay_list_p list) {
  char **array_strings = (char **) malloc(list->size * sizeof(char *));
  int i;
  int length = 0;
  int watermark;
  char *string;
  char *start;

  for (i = 0; i < list->size; i++) {
    array_strings[i] = clay_array_string(list->data[i]);
    length += strlen(array_strings[i]);
  }

  length += 2 + list->size;
  string = (char *) malloc(length);
  start = string;
  watermark = length;

  snprintf(string, watermark, "{");
  string += 1;
  watermark -= 1;
  for (i = 0; i < list->size - 1; i++) {
    int current_length = strlen(array_strings[i]);
    snprintf(string, watermark, "%s,", array_strings[i]);
    watermark -= current_length;
    string += current_length;
    free(array_strings[i]);
  }
  if (list->size != 0) {
    int current_length = strlen(array_strings[list->size - 1]);
    snprintf(string, watermark, "%s}", array_strings[list->size - 1]);
    watermark -= current_length;
    string += current_length;
    free(array_strings[list->size - 1]);
  }

  return start;
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
  for (int i = 0; i < last_statement_beta_dim; i++) {
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

void chlore_put_statement_after(osl_scop_p scop, int location, clay_array_p beta,
                                std::vector<ChloreBetaTransformation> &commands, clay_options_p options) {
  int statement_beta_dim = beta->data[beta->size - 1];
  beta->size -= 1;
  int last_statement_beta_dim = chlore_last_statement_beta_dim(scop, beta);
  beta->size += 1;

  if (statement_beta_dim > location) {
    clay_array_p new_beta = clay_array_clone(beta);
    std::swap(new_beta->data[new_beta->size - 1], location);
    chlore_put_statement_after(scop, location, new_beta, commands, options);
    clay_array_free(new_beta);
    return;
  }

  clay_array_p reorder_list = clay_array_malloc();
  for (int i = 0; i <= last_statement_beta_dim; i++) {
    clay_array_add(reorder_list, 0);
  }

  for (int i = 0; i <= last_statement_beta_dim; i++) {
    clay_array_add(reorder_list, i);
    if (i > statement_beta_dim && i <= location) {
      reorder_list->data[i] = i - 1;
    } else if (i == statement_beta_dim) {
      reorder_list->data[i] = location;
    } else {
      reorder_list->data[i] = i;
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

clay_array_p chlore_detach_statement_from_loop(osl_scop_p scop, clay_array_p beta,
                                               std::vector<ChloreBetaTransformation> &commands, clay_options_p options) {
  clay_array_p current_beta = clay_array_clone(beta);
  int statement_beta_dim = current_beta->data[current_beta->size - 1];
  int last_statement_beta_dim;
  current_beta->size -= 1;
  last_statement_beta_dim = chlore_last_statement_beta_dim(scop, current_beta);
  current_beta->size += 1;

  // already last, no need to do anything
  if (statement_beta_dim != last_statement_beta_dim) {
    // put last
    chlore_put_statement_last(scop, last_statement_beta_dim, current_beta, commands, options);

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
  clay_array_p current_beta = clay_array_clone(beta);
  while (current_beta->size > depth) {
    clay_array_p old_pointer = current_beta;
    current_beta = chlore_detach_statement_from_loop(scop, current_beta, commands, options);
    clay_array_free(old_pointer);
  }
  return current_beta;
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
int chlore_linearizable_lines(osl_scop_p scop, clay_array_p beta, int depth,
                              clay_list_p found_betas, clay_array_p row_indices) {
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
      if (!clay_beta_check_relation(scattering, beta)) {
        scattering = scattering->next;
        continue;
      }
      // Get the maximum number of output dimensions in all matching scatterings
      if (scattering->nb_output_dims > nb_output_dims) {
        nb_output_dims = scattering->nb_output_dims;
      }
      if ((scattering->nb_output_dims - 1) / 2 < depth + 1) { // Check depth.
        clay_array_free(candidate_rows_lower);
        clay_array_free(candidate_rows_upper);
        return CLAY_ERROR_DEPTH_OVERFLOW;
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
        if (osl_int_zero(precision, scattering->m[row][0])) {
          continue;
        }

        for (col = 1; col < scattering->nb_columns - 1; col++) {
          if (col == 2*depth || col == 2*depth + 2) {
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
            osl_int_zero(precision, scattering->m[row][2*depth + 2])) {
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

        if (!positive_at_depth && one_at_next && constant_zero) {
          clay_array_add(candidate_rows_lower, row);
        } else if (positive_at_depth && mone_at_next && !constant_zero) {
          clay_array_add(candidate_rows_upper, row);
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
    while (scattering != NULL) {
      if (!clay_beta_check_relation(scattering, beta)) {
        scattering = scattering->next;
        continue;
      }
      CLAY_BETA_CHECK_DEPTH(beta, depth, scattering);

      factor = clay_relation_gcd(scattering, depth);
      if (osl_int_zero(precision, factor))
        continue;

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
      scattering = scattering->next;
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
    fprintf(stderr, "%d # ", error);
    clay_list_free(found_betas);
    clay_array_free(row_indices);
    clay_list_free(result);
    return NULL;
  }

  return result;
}

int chlore_extract_stripmine_size(osl_scop_p scop, clay_array_p beta, int depth) {
  clay_list_p found_betas = clay_list_malloc();
  clay_array_p row_indices = clay_array_malloc();
  osl_statement_p statement;
  osl_relation_p scattering;
  osl_int_t factor;
  int i;
  int size;
  int precision;

  if (chlore_linearizable_lines(scop, beta, depth, found_betas, row_indices) !=
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
      return -2;
    }
  }

  size = osl_int_get_si(precision, factor);

  osl_int_clear(precision, &factor);
  clay_list_free(found_betas);
  clay_array_free(row_indices);
  return size;
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

optional<std::tuple<ClayArray, ClayList>>
lookup_iss_conditions(osl_scop_p scop, osl_statement_p statement,
                      std::vector<ChloreBetaTransformation> &commands, clay_options_p options) {
  clay_list_p found_betas = clay_list_malloc();
  clay_array_p row_indices = clay_array_malloc();

  clay_array_p beta = chlore_collapsing(scop, statement, commands, options, found_betas, row_indices);
//  chlore_collapsing_lines(scop, beta, found_betas, row_indices);
  clay_list_p condition = chlore_extract_iss_line(scop, found_betas, row_indices);

  clay_list_free(found_betas);
  clay_array_free(row_indices);
  if (condition) {
    return make_optional(std::make_tuple(ClayArray(clay_array_clone(beta)),
                         ClayList(condition)));
  } else {
    return make_empty<std::tuple<ClayArray, ClayList>>();
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
      if (partial_result > 0) {
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
  assert(nb_rows == scattering->nb_input_dims * 2 + 1);

  // beta-definition rows interleave alpha-definition rows
  for (int i = 0; i < scattering->nb_input_dims; i++) {
    for (int j = i + 1; j < scattering->nb_input_dims; j++) {
      int source_row = 2*i + 1;
      int target_row = 2*j + 1;
      int source_column = 1 + scattering->nb_output_dims;

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

std::tuple<int, ClayArray, int>
chlore_shifted(osl_relation_p scattering) {
  clay_array_p current_parameters = clay_array_malloc();
  clay_array_p beta = clay_beta_extract(scattering);

  // If normalized form is not
  //  b a b a b a b a a p p c
  // [0 1 0 0 0 0 0 x x N M c]
  // [      1 0 0 0 x x N M c]
  // [          1 0 x x N M c]
  // there is not much we can do right now, but this should not happen for
  // valid scheduling realtions.

  for (int depth = 0; depth < beta->size - 1; depth++) {
    clay_array_clear(current_parameters);

    bool shifted = false;
    clay_array_clear(current_parameters);
    for (int i = scattering->nb_columns - scattering->nb_parameters - 1;
         i < scattering->nb_columns - 1; i++) {
      int value = osl_int_get_si(scattering->precision, scattering->m[2*depth + 1][i]);
      clay_array_add(current_parameters, value);
      if (value != 0) {
        shifted = true;
      }
    }
    int constant  = osl_int_get_si(scattering->precision,
                                   scattering->m[2*depth + 1][scattering->nb_columns - 1]);
    if (constant != 0) {
      shifted = true;
    }

    if (shifted) {
      // return parameters and value
      return std::make_tuple(depth + 1,
                             ClayArray(current_parameters),
                             constant);
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

// assumes normalized
std::tuple<int, int, int>
chlore_reshaped(osl_relation_p relation) {
  for (int i = 1; i < relation->nb_rows; i += 2) { // ignore beta definitions
    for (int j = 0; j < relation->nb_input_dims; j++) {
      if ((i - 1) / 2 == j) {
        continue;
      }

      int value =  osl_int_get_si(relation->precision,
                              relation->m[i][relation->nb_output_dims + 1 + j]);
      if (value != 0) {
        return std::make_tuple((i + 1) / 2, j + 1, value);
      }
    }
  }
  return std::make_tuple(TRANSFORMATION_NOT_FOUND, -1, -1);
}

std::tuple<ClayArray, int, int, int>
lookup_reshape(osl_statement_p statement) {
  for (osl_relation_p scattering = statement->scattering; scattering != NULL;
       scattering = scattering->next) {
    std::tuple<int, int, int> found = chlore_reshaped(scattering);
    if (std::get<0>(found) != TRANSFORMATION_NOT_FOUND) {
      return std::tuple_cat(std::make_tuple(ClayArray(clay_beta_extract(scattering))), found);
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
  assert(nb_explicit_dims == relation->nb_input_dims);

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

std::tuple<int, int>
chlore_fix_diagonal(osl_relation_p relation) {
  for (int i = 0; i < relation->nb_input_dims; i++) {
    int row = 1 + 2*i;
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
            return make_optional(std::make_pair(ClayArray(original_beta), ClayArray(transformed_beta)));
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

  return make_empty<std::pair<ClayArray, ClayArray>>();
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

void chlore_fix_beta_at_depth(osl_scop_p original, osl_scop_p transformed,
                              std::vector<ChloreBetaTransformation> &commands, clay_options_p options,
                              clay_array_p child_prefix, clay_array_p prefix) {
  while (true) {
    clay_array_p original_beta;
    optional<std::pair<ClayArray, ClayArray>> mismatch = chlore_find_first_beta_mismatch(original, transformed, child_prefix);
    if (!mismatch) {
      break;
    }
    std::tie(original_beta, std::ignore) = static_cast<std::pair<ClayArray, ClayArray>>(mismatch);

    chlore_detach_statement_until_depth(original, original_beta, child_prefix->size, commands, options); // TODO check depth is correct or needs -1

    int nb_original_children = chlore_last_statement_beta_dim(original, prefix);
    assert (nb_original_children >= original_beta->data[prefix->size]);
    if (nb_original_children != original_beta->data[prefix->size]) {
      int old_size = original_beta->size;
      original_beta->size = child_prefix->size;
      chlore_put_statement_after(original, child_prefix->data[child_prefix->size - 1], original_beta, commands, options);
      original_beta->size = old_size;

      // TODO: is fusion always necessary?
      ChloreBetaTransformation fusion;
      fusion.kind = ChloreBetaTransformation::FUSE;
      fusion.target = ClayArray::copy(child_prefix);
      // no need to compute undo statements here
      //        fusion.first_loop_size = chlore_last_statement_beta_dim(scop, child_prefix);
      commands.push_back(fusion);
      clay_fuse(original, child_prefix, options);
    }

    // beta-vectors might have changed, so we must restart the inner loop
  }

  // Split away everything that has child_prefix in original, but not in transformed.
  while (true) {
    clay_array_p split_away_beta = chlore_find_first_split_away(original, transformed, child_prefix);
    if (!split_away_beta) {
      break;
    }
    chlore_detach_statement_until_depth(original, split_away_beta, child_prefix->size, commands, options); // TODO: check depth is correct or needs -1
  }
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

    clay_array_p split_beta = chlore_detach_statement_until_depth(original, original_beta, prefix->size, commands, options);

    int last_original_child_beta = chlore_last_statement_beta_dim(original, prefix);
    int last_transformed_child_beta = chlore_last_statement_beta_dim(transformed, prefix);

    // Reorder after the target position and fuse (something already has the required beta-prefix;
    // if it is not used after, it will be split away).
    if (last_transformed_child_beta > split_beta->data[prefix->size]) {
      assert(transformed_beta->data[prefix->size] <= last_original_child_beta); // if not, just put the statement last in the loop...
      if (split_beta->data[prefix->size] != transformed_beta->data[prefix->size] + 1) { // Do not reorder if already there
        int old_size = split_beta->size;
        split_beta->size = prefix->size + 1; //  find_first_mismatch returns only beta-vectors for which prefix is shorter than the vector, this is safe
        chlore_put_statement_after(original, transformed_beta->data[prefix->size], split_beta, commands, options);
        split_beta->size = old_size;
      }

      clay_array_p fusion_target = clay_array_clone(prefix);
      clay_array_add(fusion_target, transformed_beta->data[prefix->size]);
      ChloreBetaTransformation fusion;
      fusion.kind   = ChloreBetaTransformation::FUSE;
      fusion.target = ClayArray(fusion_target);
      // no need to compute undo statements here, spare computation.
      // fusion.first_loop_size = chlore_last_statement_beta_dim(scop, fusion_target);
      commands.push_back(fusion);
      clay_fuse(original, fusion_target, options);
    } else if (last_transformed_child_beta == split_beta->data[prefix->size]){ // No need to fuse (remainigs will be split away if necessary)
      if (split_beta->data[prefix->size] != transformed_beta->data[prefix->size]) {
        int old_size = split_beta->size;
        split_beta->size = prefix->size + 1;
        if (transformed_beta->data[prefix->size] == 0) {
          chlore_put_statement_first(original, split_beta, commands, options);
        } else {
          chlore_put_statement_after(original, transformed_beta->data[prefix->size] - 1,
            split_beta, commands, options);
        }
        split_beta->size = old_size;
      }
    } else {
      chlore_info_message("don't know what to with the beta, non-contiguous with the transformed scop betas");
      assert(false);
    }

    clay_array_free(split_beta);

    // beta-vectors might have changed, so we must restart the inner loop
  }

  // Split away everything that has prefix in original, but not in transformed.
  while (true) {
    clay_array_p split_away_beta = chlore_find_first_split_away(original, transformed, prefix);
    if (!split_away_beta) {
      break;
    }
    chlore_detach_statement_until_depth(original, split_away_beta, prefix->size, commands, options);
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

void chlore_find_sequence(osl_scop_p original, osl_scop_p transformed) {
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
      // Try for iss
      std::vector<ChloreBetaTransformation> original_commands, transformed_commands;
      optional<std::tuple<ClayArray, ClayList>> original_iss =
        lookup_iss_conditions(original, original_stmt, original_commands, options);

      // TODO: we also have to try finding all possible isses, not only one? ++ if on both sides, do not include; -- requires multiple calls for reorder with hardly predictable effect on beta-vectors.

      optional<std::tuple<ClayArray, ClayList>> transformed_iss =
        lookup_iss_conditions(transformed, transformed_stmt, transformed_commands, options);

      if (original_iss) {
        auto original_tuple = static_cast<std::tuple<ClayArray, ClayList>>(original_iss);

        ClayArray beta;
        std::tie(beta, std::ignore) = original_tuple;

        std::stringstream ss;
        for (const ChloreBetaTransformation &command : original_commands) {
          ss << command;
          first.push_back(ss.str());
          ss.str("");
        }

        ss << "collapse " << beta << "\n";
        first.push_back(ss.str());

        clay_collapse(original, beta, options);

      }

      if (transformed_iss) {
        auto transformed_tuple = static_cast<std::tuple<ClayArray, ClayList>>(transformed_iss);

        ClayArray beta;
        ClayList condition;
        std::tie(beta, condition) = transformed_tuple;

        std::stringstream ss;
        std::deque<ChloreBetaTransformation> inverted_commands = chlore_complementary_beta_transformation(transformed_commands);
        for (auto it = inverted_commands.rbegin(), eit = inverted_commands.rend(); it != eit; ++it) {
          ss << *it;
          last.push_front(ss.str());
          ss.str("");
        }

        ss << "iss " << beta << " " << condition << "\n";
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
        ss << "linearize " << beta << " @" << depth << "\n";
        first.push_back(ss.str());

        clay_linearize(original, beta, depth, options);
      }

      for (auto const &data : transformed_sizes) {
        ClayArray beta;
        int depth;
        int size;
        std::tie(beta, depth, size) = data;

        std::stringstream ss;
        ss << "stripmine " << beta << " @" << depth << " " << size << "\n";
        last.push_front(ss.str());

        clay_linearize(transformed, beta, depth, options);
      }


      if (transformed_sizes.size() != 0 ||
          original_sizes.size() != 0) {
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
        ss << "densify " << beta << " @" << depth << "\n";
        first.push_back(ss.str());

        clay_densify(original, beta, depth, options);
      }

      for (auto const &data : transformed_grains) {
        ClayArray beta;
        int depth;
        int size;
        std::tie(beta, depth, size) = data;

        std::stringstream ss;
        ss << "grain " << beta << " @" << depth << " " << size << "\n";
        last.push_front(ss.str());

        clay_densify(transformed, beta, depth, options);
      }

      if (original_grains.size() != 0 || transformed_grains.size() != 0) {
        continue;
      }

      osl_scop_normalize_scattering(original);
      osl_scop_normalize_scattering(transformed);

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
        ss << "shift " << beta << " @" << depth << " "
           << parameters << " " << constant << "\n";
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
        ss << "shift " << beta << " @" << depth << " "
           << parameters << " " << constant << "\n";
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
        ss << "interchange " << beta << " @" << depth_1 << " with @" << depth_2 << "\n";
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
          ss << "grain " << beta << " @" << source << " " << source_grain << "\n";
          clay_grain(original, beta, source, source_grain, options);
        } else if (source_grain < 0) {
          source_grain = -source_grain;
          ss << "reverse " << beta << " @" << source << "\n";
          ss << "grain " << beta << " @" << source << " " << source_grain << "\n";
          clay_reverse(original, beta, source, options);
          clay_grain(original, beta, source, source_grain, options);
        }

        if (target_grain > 1) {
          ss << "grain " << beta << " @" << target << " " << target_grain << "\n";
          clay_grain(original, beta, target, target_grain, options);
        } else if (target_grain < 0) {
          target_grain = -target_grain;
          ss << "reverse " << beta << " @" << target << "\n";
          clay_reverse(original, beta, target, options);
          if (target_grain != 1) {
            ss << "grain " << beta << " @" << target << " " << target_grain << "\n";
            clay_grain(original, beta, target, target_grain, options);
          }
        }

        ss << "skew " << beta << " @" << source << " by 1x@" << target << "\n";
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
        ss << "interchange " << beta << " @" << depth_1 << " with @" << depth_2 << "\n";
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
          ss << "grain " << beta << " @" << source << " " << source_grain << "\n";
          clay_grain(transformed, beta, source, source_grain, options);
        } else if (source_grain < 0) {
          source_grain = -source_grain;
          ss << "reverse " << beta << " @" << source << "\n";
          ss << "grain " << beta << " @" << source << " " << source_grain << "\n";
          clay_reverse(transformed, beta, source, options);
          clay_grain(transformed, beta, source, source_grain, options);
        }

        if (target_grain > 1) {
          ss << "grain " << beta << " @" << target << " " << target_grain << "\n";
          clay_grain(transformed, beta, target, target_grain, options);
        } else if (target_grain < 0) {
          target_grain = -target_grain;
          ss << "reverse " << beta << " @" << target << "\n";
          clay_reverse(transformed, beta, target, options);
          if (target_grain != 1) {
            ss << "grain " << beta << " @" << target << " " << target_grain << "\n";
            clay_grain(transformed, beta, target, target_grain, options);
          }
        }

        ss << "skew " << beta << " @" << source << " by -1x@" << target << "\n";
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
        ss << "skew " << beta << " @" << source << " by "
           << coefficient << "x@" << target << "\n";
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
        ss << "skew " << beta << " @" << source << " by "
           << -coefficient << "x@" << target << "\n";
        last.push_front(ss.str());

        clay_skew(transformed, beta, source, target, coefficient, options);
        continue;
      }



      // Reshape
      std::tuple<ClayArray, int, int, int> potential_reshape =
          lookup_reshape(original_stmt);
      if (std::get<1>(potential_reshape) != TRANSFORMATION_NOT_FOUND) {
        ClayArray beta;
        int dim, input, coefficient;
        std::tie(beta, dim, input, coefficient) = potential_reshape;

        std::stringstream ss;
        ss << "reshape " << beta << " @" << dim << " by "
           << coefficient << "x@" << input << "\n";
        first.push_back(ss.str());

        clay_reshape(original, beta, dim, input, coefficient, options);
      }

      potential_reshape = lookup_reshape(transformed_stmt);
      if (std::get<1>(potential_reshape) != TRANSFORMATION_NOT_FOUND) {
        ClayArray beta;
        int dim, input, coefficient;
        std::tie(beta, dim, input, coefficient) = potential_reshape;

        std::stringstream ss;
        ss << "reshape " << beta << " @" << dim << " by "
           << -coefficient << "x@" << input << "\n";
        first.push_back(ss.str());

        clay_reshape(transformed, beta, dim, input, coefficient, options);
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
          ss << "reverse " << beta << " @" << dim << "\n";

          clay_reverse(original, beta, dim, options);
          amount = -amount;
        }
        ss << "grain " << beta << " @" << dim << " " << amount << "\n";

        clay_grain(original, beta, dim, amount, options);
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
          ss << "reverse " << beta << " @" << dim << "\n";

          clay_reverse(transformed, beta, dim, options);
          amount = -amount;
        }
        ss << "grain " << beta << " @" << dim << " " << amount << "\n";

        clay_grain(transformed, beta, dim, amount, options);
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
    return;
  }

  std::vector<ChloreBetaTransformation> commands;
  chlore_match_betas(original, transformed, commands, options);

  for (const std::string &s : first) {
    std::cout << s;
  }
  for (const ChloreBetaTransformation &transformation : commands) {
    std::cout << transformation;
  }
  for (const std::string &s : last) {
    std::cout << s;
  }
}

void chlore_usage(const char *name) {
  fprintf(stderr, "%s <original.scop> <transformed.scop>\n", name);
}

int main(int argc, char **argv) {
  osl_scop_p original, transformed;

  if (argc != 3) {
    chlore_usage(argv[0]);
    return 0;
  }

  FILE *f1 = fopen(argv[1], "r");
  FILE *f2 = fopen(argv[2], "r");

  if (!f1) {
    fprintf(stderr, "Can't open the original file %s\n", argv[1]);
    return -1;
  }
  if (!f2) {
    fprintf(stderr, "Can't open the transformed file %s\n", argv[2]);
    fclose(f1);
    return -2;
  }
  original = osl_scop_read(f1);
  transformed = osl_scop_read(f2);
  fclose(f1);
  fclose(f2);

  if (!original) {
    fprintf(stderr, "Can't read the original SCoP from file %s\n", argv[1]);
    return -3;
  }
  if (!transformed) {
    fprintf(stderr, "Can't read the transformed SCoP from file %s\n", argv[2]);
    return -4;
  }

  chlore_find_sequence(original, transformed);

  return 0;
}


