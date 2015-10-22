#include <set>
#include <tuple>
#include <vector>

#include <osl/osl.h>

#include <clay/transformation.h>
#include <clay/beta.h>
#include <clay/relation.h>
#include <clay/errors.h>

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>


// chunky loop optimization revealer
// ChLORe

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

// FIXME: this is almost a copy of clay_collapse()
int chlore_collapsing_lines(osl_scop_p scop, clay_array_p beta,
                            clay_list_p found_betas, clay_array_p row_indices) {
  int i, row, col, row_1, row_2;
  int candidate_row_1, candidate_row_2;
  int nb_pairs;
  clay_array_p first_beta, second_beta, max_beta;
  clay_array_p matched_rows_2;
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

    // Check scattering parameters are compatible.
    if (!s1 || !s2 ||
        s1->nb_rows != s2->nb_rows ||
        s1->nb_input_dims != s2->nb_input_dims ||
        s1->nb_output_dims != s2->nb_output_dims ||
        s1->nb_local_dims != s2->nb_local_dims ||
        s1->nb_parameters != s2->nb_parameters) {
      clay_list_free(matching_betas);
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
          clay_list_free(matching_betas);
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
          clay_list_free(matching_betas);
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
      clay_list_free(matching_betas);
      return CLAY_ERROR_WRONG_COEFF;
    }

    // Check if unmatched rows differ up to negation.
    clay_util_relation_negate_row(s2, candidate_row_2);
    for (col = 0; col < s1->nb_columns; col++) {
      if (osl_int_ne(s1->precision, s1->m[candidate_row_1][col],
                                    s2->m[candidate_row_2][col])) {
        clay_list_free(matching_betas);
        return CLAY_ERROR_WRONG_COEFF;
      }
    }
    clay_util_relation_negate_row(s2, candidate_row_2);

    // All preconditions are met, now we may remove the inequality and the
    // second relation.

    clay_list_add(found_betas, clay_beta_extract(s1));
    clay_array_add(row_indices, candidate_row_1);
  }

  clay_list_free(matching_betas);
  return CLAY_SUCCESS;
}

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

clay_list_p chlore_extract_iss_line(osl_scop_p scop, clay_array_p beta) {
  int i, j;
  clay_list_p found_betas  = clay_list_malloc();
  clay_list_p result = clay_list_malloc();
  clay_array_p output = clay_array_malloc();
  clay_array_p input = clay_array_malloc();
  clay_array_p parameters = clay_array_malloc();
  clay_array_p constant = clay_array_malloc();
  clay_array_p row_indices = clay_array_malloc();
  osl_statement_p statement;
  osl_relation_p scattering;
  int error = 0;

  chlore_collapsing_lines(scop, beta, found_betas, row_indices);

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
    clay_list_free(result);
    return NULL;
  }

  clay_list_free(found_betas);
  clay_array_free(row_indices);
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

template <typename T, T *(creator)(), void (deleter)(T *),
          T *(cloner)(T *), int (equality)(T *, T *)>
class OSLContainer {
public:
  OSLContainer() {
    object = creator();
  }

  OSLContainer(T *other) {
    object = other;
  }

  OSLContainer(const OSLContainer &other) {
    object = cloner(other.object);
  }

  OSLContainer(T &&other) {
    object = other.object;
    other.object = NULL;
  }

  ~OSLContainer() {
    deleter(object);
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

private:
  T *object;
};

typedef OSLContainer<clay_array_t, clay_array_malloc, clay_array_free, clay_array_clone, clay_array_equal> ClayArray;
typedef OSLContainer<clay_list_t, clay_list_malloc, clay_list_free, clay_list_clone, clay_list_equal> ClayList;

std::vector<std::tuple<ClayArray, ClayList>>
lookup_iss_conditions(osl_scop_p scop, osl_statement_p statement) {
  osl_relation_p scattering;
  std::vector<std::tuple<ClayArray, ClayList>> collapsing;

  for (scattering = statement->scattering; scattering != NULL;
       scattering = scattering->next) {
    clay_array_p beta = clay_beta_extract(scattering);
    int limit_depth = beta->size - 1;

    for (int depth = 1; depth <= limit_depth; depth++) {
      beta->size = depth;

      // Check for betas at all depths.
      clay_list_p condition = chlore_extract_iss_line(scop, beta);
      if (condition) {
        collapsing.push_back(std::make_tuple(ClayArray(clay_array_clone(beta)),
                                             ClayList(condition)));
      }
    }
    clay_array_free(beta);
  }

  std::set<size_t> to_remove;
  for (size_t i = 0, ei = collapsing.size(); i < ei; i++) {
    for (size_t j = i + 1, ej = collapsing.size(); j < ej; j++) {
      if (collapsing[i] == collapsing[j]) {
        to_remove.insert(j);
      }
    }
  }

  for (auto it = to_remove.rbegin(), eit = to_remove.rend(); it != eit; it++) {
    collapsing.erase(collapsing.begin() + *it);
  }

  return collapsing;
}

void chlore_find_sequence(osl_scop_p original, osl_scop_p transformed) {
  osl_statement_p stmt, original_stmt, transformed_stmt;
  int nb_stmts = 0;
  int i;

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
      std::vector<std::tuple<ClayArray, ClayList>> original_iss =
        lookup_iss_conditions(original, original_stmt);
      std::vector<std::tuple<ClayArray, ClayList>> transformed_iss =
        lookup_iss_conditions(transformed, transformed_stmt);

      // If same condition is present on both sides, it is not a part of
      // transformation sequence.
      for (size_t i = 0; i < original_iss.size(); i++) {
        for (size_t j = 0; j < transformed_iss.size(); j++) {
          if (original_iss[i] == transformed_iss[j]) {
            original_iss.erase(original_iss.begin() + i);
            transformed_iss.erase(transformed_iss.begin() + j);
            --i; // May overflow, but is well-defined for unsigned integers.
            --j;
          }
        }
      }

      for (auto &data : original_iss) {
        ClayArray beta;
        std::tie(beta, std::ignore) = data;
        fprintf(stdout, "collapse ");
        clay_array_print(stdout, beta, 1);

        clay_collapse(original, beta, options);
      }
      for (auto &data : transformed_iss) {
        ClayArray beta;
        ClayList condition;
        std::tie(beta, condition) = data;
        fprintf(stdout, "iss ");
        clay_array_print(stdout, beta, 0);
        fprintf(stdout, " ");
        clay_list_print(stdout, condition);
        fprintf(stdout, "\n");

        clay_collapse(transformed, beta, options);
      }

      if (original_iss.size() != 0 ||
          transformed_iss.size() != 0) {
        continue;
      }

      // Can't do anything
      break;
    }

    original_stmt = original_stmt->next;
    transformed_stmt = transformed_stmt->next;
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


