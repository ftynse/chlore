#ifndef CHLORE_H
#define CHLORE_H

#include <osl/scop.h>

#include <clay/array.h>
#include <clay/list.h>

#include <string>

int         chlore_extract_stripmine_size(osl_scop_p scop, clay_array_p beta, int depth);
int         chlore_extract_grain(osl_scop_p scop, clay_array_p beta, int depth);
clay_list_p chlore_extract_iss_condition(osl_scop_p scop, clay_array_p beta);
int         chlore_extract_embed(osl_scop_p scop, clay_array_p beta);

void chlore_scop_replace_extra_dimensions(osl_scop_p scop);
std::string chlore_find_sequence(osl_scop_p original, osl_scop_p transformed);
void chlore_find_betas(osl_scop_p scop);

void chlore_whiteboxing(osl_scop_p original, osl_scop_p transformed);

#endif // CHLORE_H

