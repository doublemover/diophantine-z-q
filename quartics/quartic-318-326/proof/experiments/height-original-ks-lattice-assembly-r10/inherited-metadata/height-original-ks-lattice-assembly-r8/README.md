# Exact hosted geometry replay repair

Successor of `height-original-ks-lattice-assembly-r7` at `56773da3e1a8045d885059ae17053fcbf0af6067`. The predecessor is frozen. Hosted run [43503478144](https://github.com/doublemover/diophantine-z-q/actions/runs/43503478144) is failure evidence, not acceptance.

## Observed failures and bounded changes

The center packet compiled 41 modules, then failed in `IntegralRationalInfinityMap318` at the inverse-root map coercion and concrete coordinate/generator endpoint matching. The lattice packet compiled 52 modules, then failed only at `IntegralOriginalInfinityEmbedding318`'s ambiguous `(U : Set _)` coercion. These counts do not establish packet acceptance or a recursive axiom audit.

This successor changes exactly `IntegralOriginalInfinityEmbedding318.lean`, `IntegralRationalInfinityMap318.lean`. Rational infinity repair exposes the given hom applications before rewriting, uses the actual two-stage localized coordinate in its private extensionality helper, and unfolds only the named original embedding for its generator equation. The embedding repair, when present, uses native `Opens.carrier` rather than an ambiguous set coercion.

## Application contract

1. **Required inputs:** Same commutative-ring, localization, ring-equivalence and original field inputs. No new public hypothesis or trusted premise.
2. **Constructed objects:** Same original integral infinity order, overlap and Kummer field. The private helper's nested coordinate is exactly `IntegralInfinityChart318.coordinate`, not another coordinate.
3. **Coverage:** Rational-constant uniqueness, polynomial X, the full principal-localized base and every `j : Fin 3` remain required and consumed.
4. **Transitions:** The original infinityMap, originalFieldEmbedding, rationalOrderEquiv and originalEmbedding are unchanged. Only the form in which their applications are exposed changes.
5. **Scalars and signs:** The same signed pivot root, inverse unit, ordered quotient roots and scalar actions remain. No equality is weakened to an equality of squares.
6. **Consumer identity:** `field_restriction` still identifies the exact full ring maps; `infinity_restriction` still uses original open-field injectivity. The spectrum range is still the original denominator basic open.
7. **Exceptional cases:** No field or nonvanishing assumption is added to the generic spectrum-localization theorem. No index or prime is removed.
8. **Downstream preservation:** Full predecessor source order is copied. Every unlisted Lean file is byte-identical; existing public signatures, imports and options are unchanged. Metadata copied under `inherited-metadata` and older hosted folders remains historical.
9. **Verification boundary:** Candidate source review is separate from hosted elaboration and recursive axiom audit. No local Lean/Lake command ran and no new packet was pushed. Exact failure logs, before/diff files and native primary definitions are bound. New hosted verification is pending; no arithmetic-theorem or manuscript acceptance is claimed.
