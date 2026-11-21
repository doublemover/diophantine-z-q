// Exact complete rational prime divisibility up to a supplied bound.
#include <algorithm>
#include <cstdint>
#include <gmpxx.h>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

int main(int argc, char **argv) {
  if (argc != 2) return 2;
  uint64_t max = std::stoull(argv[1]);
  if (max < 2 || max > 150000000) return 2;
  std::string decimal;
  std::cin >> decimal;
  mpz_class n(decimal);
  if (n <= 1) return 2;

  uint64_t r = 1;
  while ((r + 1) * (r + 1) <= max) ++r;
  std::vector<bool> composite(r + 1);
  std::vector<uint64_t> small;
  for (uint64_t p = 2; p <= r; ++p) {
    if (composite[p]) continue;
    small.push_back(p);
    for (uint64_t k = p * p; k <= r; k += p) composite[k] = true;
  }
  constexpr uint64_t window = 1 << 20;
  std::vector<uint8_t> marked(window);
  uint64_t tested = 0;
  bool first = true;
  std::cout << R"({"factors":[)";
  for (uint64_t lo = 2; lo <= max; lo += window) {
    uint64_t hi = std::min(max, lo + window - 1);
    std::fill(marked.begin(), marked.begin() + (hi - lo + 1), 0);
    for (uint64_t p : small) {
      if (p * p > hi) break;
      uint64_t z = std::max(p * p, ((lo + p - 1) / p) * p);
      for (; z <= hi; z += p) marked[z - lo] = 1;
    }
    for (uint64_t p = lo; p <= hi; ++p) {
      if (marked[p - lo]) continue;
      ++tested;
      unsigned e = 0;
      while (mpz_divisible_ui_p(n.get_mpz_t(), p)) {
        mpz_divexact_ui(n.get_mpz_t(), n.get_mpz_t(), p);
        ++e;
      }
      if (e) {
        if (!first) std::cout << ",";
        first = false;
        std::cout << "[" << p << "," << e << "]";
      }
    }
  }
  std::cout << "],\"maximum\":" << max << ",\"prime_tests\":" << tested
            << ",\"remaining\":\"" << n << "\"}\n";
}
