#ifndef CHLORE_H
#define CHLORE_H

#include <osl/scop.h>

#include <clay/array.h>
#include <clay/list.h>

#include <string>

int chlore_densifiable(osl_scop_p scop, clay_array_p beta, int depth,
                       clay_list_p found_betas, clay_array_p grains);

void chlore_scop_replace_extra_dimensions(osl_scop_p scop);
std::string chlore_find_sequence(osl_scop_p original, osl_scop_p transformed);
void chlore_find_betas(osl_scop_p scop);

void chlore_whiteboxing(osl_scop_p original, osl_scop_p transformed);

#endif // CHLORE_H

