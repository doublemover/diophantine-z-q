# Actual monic specialization root: exact r2 compiler repair

Source-only successor to official 44932479404. The only diagnosed owner had
two function pointwise-op transparency mismatches in a private auxiliary proof.
Use the literally identical pinned Mathlib Polynomial.continuous theorem
(Topology.Algebra.Polynomial, line 54) instead. The bound, both public theorem
statements, and the unattempted matrix source are unchanged. No raised limits.
