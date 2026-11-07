# Independent actual Kähler-frame and fraction derivation review

Accepted. The five original sources were copied byte-for-byte, independently read and rebuilt with strict kernel checking. A fresh exhaustive recursive axiom audit passed 84 declarations across five modules; only propext, Classical.choice and Quot.sound occur. No upstream file was edited.

## Mathematical checks

1. The integral Kähler frame is an actual linear equivalence Ω(B/R)≃B. Its dual is the genuine universal derivation functional. The normalized-generator identity forces compatibility on every integral differential, rather than assuming preservation of B by the resulting field derivation. A differential that generates Ω(B/R) has a unit coefficient by an explicit inverse equation.
2. The square-zero jet is b↦(b,db), with the base inclusion and second-coordinate orientation correct. Every nonzero denominator has a unit jet because its first coordinate is nonzero in the actual fraction field. Localization produces the extension algebra map. Localization uniqueness makes its first coordinate the identity, so its second coordinate satisfies the genuine Leibniz rule. Agreement, quotient rule and uniqueness follow without a hidden invertibility or representative-choice hypothesis. The quotient rule also holds at zero denominators under the field's totalized inverse convention.
3. The universal generic differential functional agrees with the integral frame on the actual differential map. It sends the mapped integral generator to one, proving nonvanishing. The fraction quotient rule places every generic differential in that generator's span. The functional is consequently bijective and produces the generic frame, rather than assuming it.
4. The newer source adapters really remove the supplied generic frame, mapped-generator nonvanishing, field derivation and preservation premises. They still use the actual integral frame. Horizontal finite branch, infinity and regular cases retain their genuine local Q-algebra coordinates, unit-twisted equations and differential generation. Vertical integrality retains an actual DVR and an irreducible rational prime, representing the reduced-component/unramified condition.

## Scope

No mismatch was found. Actual source local rings, integral frames, coordinate/branch classification, frame-overlap and global affine/sheaf/stack realization are not constructed here. The earlier packet's generic-frame/nonvanishing inputs are correctly removed by the fraction-field packet; neither packet alone proves the full geometric realization. The already-reviewed unit-ramified and vertical integrality dependencies are imported, not newly reviewed in this replay.
