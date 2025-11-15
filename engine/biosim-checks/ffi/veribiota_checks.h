#pragma once

#include <stdbool.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct {
  double t;
  const long long *counts;
  size_t counts_len;
  const double *conc;
  size_t conc_len;
} VeribiotaSnapshot;

typedef struct {
  double t;
  bool any_neg;
  bool violated;
  double max_abs_drift;
  double max_rel_drift;
} VeribiotaOutcome;

// sig_mode: 0=unsigned, 1=signed-soft, 2=signed-enforced
int veribiota_checks_init(const char *jwks_json,
                          const char *checks_json,
                          int sig_mode);

// Returns 0 on success, 2 on invariant violation, -1 on internal errors.
int veribiota_checks_eval(const VeribiotaSnapshot *snap,
                          VeribiotaOutcome *out);

void veribiota_checks_free(void);

#ifdef __cplusplus
}
#endif

