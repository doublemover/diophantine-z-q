# Constructive norm descent ingredients

Two independent, native-Mathlib-only source modules are added. SqrtTwoNormDivision318 constructs an integer quotient pair by rounding the rational coefficients and proves its absolute norm remainder strictly smaller than a nonzero divisor norm. SqrtTwoInertPrime318 proves that an inert prime dividing an integral norm divides both coordinates, and hence its square divides that norm.

These are concrete descent lemmas, not a rational local-global theorem. No EuclideanDomain instance, split-prime norm producer, full factorization criterion, auxiliary k/ell selection, actual prepared anchor or simultaneous elliptic-twist realization is claimed. The only hypotheses are the literal nonzero divisor norm and the inert-prime nonsquare condition for the corresponding statements. No axiom or assumed existence principle is added.

All1325 predecessor sources and their relative order are retained exactly, including all119 arithmetic and11 pure checked sources and the independent64 topology repair. A two-root selected hosted check suffices for these modules because their imports are only native Mathlib. Source/API review and symbolic identity checks are not Lean acceptance. No local Lean was run.
