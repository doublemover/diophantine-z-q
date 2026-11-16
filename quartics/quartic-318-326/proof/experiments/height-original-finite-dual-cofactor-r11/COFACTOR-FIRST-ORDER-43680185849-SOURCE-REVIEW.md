# Cofactor first-order current source review

Verdict: PASS for bounded source/API/current-contract review, not Lean or kernel acceptance. No local Lean was run.

## Exact binding
- Envelope: geometry-20261115/finite-dual-repairs-43680185849.
- SOURCE-APPLICATION.json: 00f0b65cb8527e5548207338eef4c09b15821bf7910890743cba19396a97780f.
- Before NormalizedCofactorFirstOrder318: dc0bcf36927ebf0193daff603ac03a16ec2fee40322f202d9a19b75f9f4a8444.
- Candidate: 124f197327ced7cc3b8247df16c1210c08e7bd037e1207e9f89c711f07ef2d40.
- All 11 declared bindings independently hash-checked; all match.

## Actual failure and proposed change
Own run 43680185849 at 4ce7eda322f507e43be0c9be1be2e97449e82189 accepted 12 draft modules before this module failed in 3.422 seconds; four later draft modules remained unreached, with 19 baseline dependencies reused. New complete module passes are DVRNormalizedFiniteOrder (1.718s), NormalizedOrderFiniteDual (1.769s), and RingValuedCotangentEvaluation (1.267s). RESULT 945d6c19e3b4104a7d44a6e694bf32145ff5042b5752b556fc9dfade2c6014be and failure log 3e86decea9c09900bdb4493f44db25391e7025e50ed670ddd3bd2721c2442e12 match the independently inspected collector. The first errors are unknown f.toRingHom and missing Algebra V[X] V; downstream free-variable/rewrite and error-recovery sorry warnings are not successful acceptance.

The candidate explicitly binds the existing f, hf, hr on projection, evaluation, evaluation_dT, and evaluation_dRoot, in the intended existing argument order. AlgHom.toRingHom f fixes the literal projection. projection locally installs the actual evaluation algebra (Polynomial.evalRingHom T).toAlgebra. This supplies the retained coefficient-target Algebra instance on four_ringHom_ext without adding an arbitrary external algebra assumption. The pinned native evalRingHom signature and the actual passed IntegralRootPointMaps extensionality theorem support this use. Its coefficient/root hypotheses prove equality on the whole order, not just generators treated as a replacement domain.

## Scope and scalar audit
The complete source was read. factor, rootJacobian, determinant, slope, cofactor_relation, parameter, rootJet, root_relation, lift, lift_polynomial and lift_root are unchanged. The integral scalar remains the literal product of 2*z_i; neither it nor twists/roots/2 are inverted. Arbitrary CommRing V and every characteristic remain. The public cotangent-fiber types retain the same explicit point-action letI induced by f. Native integralFiberMap and its differential theorem are used with K=V; the fieldPoint is the same self-algebra composite. No substituted coordinate/free cotangent object or new unit/domain hypothesis is introduced.

The nine local obligations accurately distinguish explicit intended telescopes from the predecessor's failed elaboration: this is not a claim that a malformed predecessor had a successfully elaborated identical signature. Imports/options/resources and downstream source bodies are not changed. No intrinsic dualizing, maximal-model, all-place, or downstream evaluator acceptance follows. Candidate elaboration and any additional later errors remain for the bounded hosted replay.
