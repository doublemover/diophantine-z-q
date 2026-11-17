# Generic finite-order integral-closure bridge

All 209 KS62 sources retain exact bytes and order. The sole addition is FiniteOrderIntegralClosureMap318, a generic Mathlib-only result for a finite R-algebra B and its supplied injective R-algebra map into a field L. It constructs the same-element map into the R-integral closure and derives integrality over B iff integrality over R for that exact action. The literal R-integral closure is therefore an integral closure of B in L. No domain/normality or fraction-field premise is added.

The focused target has one draft root and no project baseline imports. Actual reciprocal-field and normalization wrappers are deliberately excluded; KS61 and KS62 pending sources remain unchanged. No closure finiteness, global properness, regularity or KS conclusion is asserted. Source/API and static checks are not Lean acceptance; no local Lean has run.

Only this new packet and registry slot62to63 change. All predecessor evidence, including the old target closure, is preserved.
