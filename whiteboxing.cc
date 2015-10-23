#include <deque>
#include <iostream>
#include <set>
#include <sstream>
#include <tuple>
#include <vector>

#include <osl/osl.h>

#include <clay/transformation.h>
#include <clay/beta.h>
#include <clay/relation.h>
#include <clay/errors.h>
#include <clay/util.h>

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>


// chunky loop optimization revealer ||
// chunku loop optimizer reverse engineering
// ChLORe

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
    clay_list_free(found_betas);
    clay_array_free(row_indices);
    clay_list_free(result);
    return NULL;
  }

  clay_list_free(found_betas);
  clay_array_free(row_indices);
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
          T *(cloner)(T *), int (equality)(T *, T *), char *(printer)(T *)>
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

  vector_remove_duplicates(collapsing);

  return collapsing;
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

inline std::vector<std::tuple<ClayArray, int, int>>
lookup_stripmine_sizes(osl_scop_p scop, osl_statement_p statement) {
  return chlore_lookup_aii(scop, statement, true, chlore_extract_stripmine_size);
}

inline std::vector<std::tuple<ClayArray, int, int>>
lookup_grains(osl_scop_p scop, osl_statement_p statement) {
  return chlore_lookup_aii(scop, statement, false, chlore_extract_grain);
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
      std::vector<std::tuple<ClayArray, ClayList>> original_iss =
        lookup_iss_conditions(original, original_stmt);
      std::vector<std::tuple<ClayArray, ClayList>> transformed_iss =
        lookup_iss_conditions(transformed, transformed_stmt);

      // If same condition is present on both sides, it is not a part of
      // transformation sequence.
      vector_pair_remove_identical_items(original_iss, transformed_iss);

      for (auto const &data : original_iss) {
        ClayArray beta;
        std::tie(beta, std::ignore) = data;

        std::stringstream ss;
        ss << "collapse " << beta << "\n";
        first.push_back(ss.str());

        clay_collapse(original, beta, options);
      }
      for (auto const &data : transformed_iss) {
        ClayArray beta;
        ClayList condition;
        std::tie(beta, condition) = data;

        std::stringstream ss;
        ss << "iss " << beta << " " << condition << "\n";
        last.push_front(ss.str());

        clay_collapse(transformed, beta, options);
      }

      if (original_iss.size() != 0 ||
          transformed_iss.size() != 0) {
        continue;
      }


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

      // Can't do anything
      break;
    }

    original_stmt = original_stmt->next;
    transformed_stmt = transformed_stmt->next;
  }

  for (const std::string &s : first) {
    std::cout << s;
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


