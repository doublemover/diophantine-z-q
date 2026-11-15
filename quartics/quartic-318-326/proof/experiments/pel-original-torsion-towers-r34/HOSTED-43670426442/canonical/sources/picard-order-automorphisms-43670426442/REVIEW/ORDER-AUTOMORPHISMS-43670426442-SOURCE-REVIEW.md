# Independent source review: actual order automorphism sign wrappers

Verdict: the typed equality repair addresses the exact observed wrapper boundary without changing the original automorphism problem. Suitable for future hosted checking only. No local Lean or kernel acceptance.

APPLICATION 4ef242e543956dd03d99f1aef7408fa784e1d124080b7f5c656fbcf5fab404db; all15 bindings independently checked.
Candidate FourRootActualOrderAutomorphisms318 153dd2bf81fadaaf03feec226ea1b7259bb0f04942256a5c6e6c27ac0aa04fa9.
Actual zero52 receipt has43 successful modules then this module FAIL5.830s. The earlier finiteEnd mismatch is absent, but the module has not passed. Sole current99:2 mismatch retains FourRootAutomorphisms.signEquiv in hx versus FourRootOrderSigns.signEquiv in the goal, with L/Raw aliases.

I read the exact before/after delta, both complete native sign constructors and relevant carrier/action definitions. Both maps use the same four native RootRing tensor factors, identical bit choices, the same negate AdjoinRoot lift and its induced equivalence, and the same Algebra.TensorProduct.congr nesting. New field_sign_eq unfolds these precise eight exposed definitions to derive the equality, not assume it. The actual field/base instances are unchanged; no alternate Field structure or root-sign hypothesis is introduced. Final hx is explicitly changed to the native common carrier, then genericAutomorphism, signPattern hg, and the proved wrapper equality are rewritten before exact hx.

The existing full-domain surjectivity proof still extends every original polynomial-order automorphism through the actual fraction field and recovers every original sign. Original hb and local facts, all scalar maps, the four signs and cardinality consumer remain. There is one new derived helper; all pre-existing public statements/options are unchanged. No finite-point sample or new nonvanishing restriction replaces the full order. The nine current obligations and own failure classification are consistent.

Definitional matching of exposed constructor instances and final native carrier coercions still require hosted elaboration. The source identity is justified by its actual constructors, not by assuming identical printed terms imply equality. No all-copy propagation or successor acceptance is claimed here.
