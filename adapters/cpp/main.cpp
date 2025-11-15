#include "../../engine/biosim-checks/ffi/veribiota_checks.h"

#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

namespace {

std::string read_file(const std::string &path) {
  std::ifstream in(path, std::ios::binary);
  if (!in) {
    throw std::runtime_error("failed to open " + path);
  }
  return std::string(std::istreambuf_iterator<char>(in), std::istreambuf_iterator<char>());
}

void engine_step_update(std::vector<double> &counts) {
  // Replace this stub with your simulator's update logic.
  for (double &v : counts) {
    v -= 0.1;  // fake drift
  }
}

}  // namespace

int main(int argc, char **argv) {
  if (argc < 2) {
    std::cerr << "usage: streaming_adapter <checks.json>\n";
    return 1;
  }
  std::string checks = read_file(argv[1]);
  if (veribiota_checks_init(nullptr, checks.c_str(), 0) != 0) {
    std::fprintf(stderr, "veribiota_checks_init failed\n");
    return 1;
  }

  const size_t species = 3;
  std::vector<double> conc(species, 1000.0);
  VeribiotaOutcome outcome{};
  bool failed = false;

  for (int step = 0; step < 10; ++step) {
    double t = step * 0.1;
    engine_step_update(conc);

    VeribiotaSnapshot snap{};
    snap.t = t;
    snap.conc = conc.data();
    snap.conc_len = conc.size();
    if (veribiota_checks_eval(&snap, &outcome) == 2 || outcome.violated) {
      std::fprintf(stderr,
                   "[FAIL] t=%.3f max_abs_drift=%.3e max_rel_drift=%.3e\n",
                   t, outcome.max_abs_drift, outcome.max_rel_drift);
      failed = true;
      break;
    }
  }

  veribiota_checks_free();
  if (failed) {
    return 2;
  }
  std::cout << "Simulation respected all invariants" << std::endl;
  return 0;
}
