#include "chlore.h"

#include <osl/scop.h>
#include <osl/extensions/clay.h>

#include <iostream>
#include <string>

struct chlore_options {
  bool normalize_original;
  bool normalize_transformed;
  bool output_extension;

  chlore_options() {
    normalize_original = true;
    normalize_transformed = true;
    output_extension = false;
  }
};

static chlore_options chlore_parse_options(int &argc, char **&argv) {
  if (!argv) {
    return chlore_options();
  }
  chlore_options options = chlore_options();
  for (int i = 1; i < argc; i++) {
    if (strcmp(argv[i], "--nonormalize-original") == 0) {
      options.normalize_original = false;
    } else if (strcmp(argv[i], "--normalize-original") == 0) {
      options.normalize_original = true;
    } else if (strcmp(argv[i], "--nonormalize-transformed") == 0) {
      options.normalize_transformed = false;
    } else if (strcmp(argv[i], "--normalize-transformed") == 0) {
      options.normalize_transformed = true;
    } else if (strcmp(argv[i], "--output-extension") == 0) {
      options.output_extension = true;
    } else {
      continue;
    }
    for (int j = i + 1; j < argc; j++) {
      argv[j - 1] = argv[j];
    }
    --argc;
    --i;
  }
  return options;
}

static void chlore_usage(const char *name) {
  fprintf(stderr, "Usage: %s <options>... <original.scop> <transformed.scop>\n\n", name);
  fprintf(stderr, "Options:\n"
                  "  --help                         Show this message\n"
                  "  --[no]normalize-original       Recover dimension structure in the original\n"
                  "                                 SCoP before processing [default=on]\n"
                  "  --[no]normalize-transformed    Recover dimension structure in the transformed\n"
                  "                                 SCoP before processing [default=on]\n"
                  "  --output-extension             Put the script in a Clay extension of\n"
                  "                                 the original scop instead of printing it\n");
}

int main(int argc, char **argv) {
  osl_scop_p original, transformed;

  if (argc < 3) {
    chlore_usage(argv[0]);
    return 0;
  }

  chlore_options options = chlore_parse_options(argc, argv);

  if (argc != 3) {
    chlore_usage(argv[0]);
    return 1;
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

  if (options.normalize_original) {
    chlore_find_betas(original);
    chlore_scop_replace_extra_dimensions(original);
  }
  if (options.normalize_transformed) {
    chlore_find_betas(transformed);
    chlore_scop_replace_extra_dimensions(transformed);
  }
  std::string sequence = chlore_find_sequence(original, transformed);

  if (options.output_extension) {
    osl_clay_p extension = osl_clay_malloc();
    extension->script = strdup(sequence.c_str());
    if (osl_generic_lookup(original->extension, OSL_URI_CLAY)) {
      fprintf(stderr, "The original scop already contains clay extension!\n");
      return 1;
    }
    osl_generic_add(&original->extension, osl_generic_shell(extension, osl_clay_interface()));
    osl_scop_print(stdout, original);
  } else {
    std::cout << sequence << std::endl;
  }

  return 0;
}
