#include <stdbool.h>
#include <stddef.h>

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

#ifdef __cplusplus
extern "C" {
#endif

int veribiota_checks_init(const char *jwks_json, const char *checks_json, int sig_mode);
int veribiota_checks_eval(const VeribiotaSnapshot *snap, VeribiotaOutcome *out);
void veribiota_checks_free(void);

#ifdef __cplusplus
}
#endif
