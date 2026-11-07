# Actual tame involution invariant quotient

Three modules, 16 public theorems and 23 recursively audited declarations, pass a fresh strict kernel replay. Only propext, Classical.choice and Quot.sound occur.

For an actual formal power series F over a field k, with constant coefficient zero, F composed with F equal to X, F not equal to X, and 2 nonzero in k, `InvolutionQuotient318.exists_normalized_quotient` constructs an actual normalized parameter H. It proves:

- H has constant coefficient zero and linear coefficient one;
- H composed with F is minus H;
- every actual F-invariant formal power series is uniquely a series g composed with H squared;
- H squared has exact formal order two;
- its actual formal derivative has exact order one.

The tangent-minus-one conclusion is derived from the actual finite-order averaging theorem, not supplied. The invariant statement is proved first by actual coefficient expansion for X mapped to minus X, then transported through the actual compositional inverse of H. It does not assume an invariant-ring description or a quotient-coordinate formula.

## Boundary

This proves the formal-coordinate invariant quotient. It does not yet construct an actual completed curve local ring or identify its action with this formal model. It does not claim mixed-characteristic shifted-constant linearization. The derivative-order theorem is not presented as an independent proof identifying the arithmetic different ideal. Finite freeness and that ideal identification are separate next work.

Run `bash run.sh` for the three-module strict rebuild and exhaustive module declaration audit. The frozen two-module TameCoordinate318/TameLinearization318 dependency is imported, not freshly rebuilt by this script.
