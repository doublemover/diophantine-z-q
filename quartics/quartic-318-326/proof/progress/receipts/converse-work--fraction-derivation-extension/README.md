# Actual derivation localization and generic Kähler frame

Three modules, 20 public theorems, six constructed maps, and 49 exhaustively
checked declarations pass the strict kernel and standard-axiom audit.

## Constructed objects

`FractionDerivation318.extend` extends an actual relative integral derivation
B→B to the actual fraction field K. The proof constructs the square-zero jet
b↦(b,db) in K[epsilon]/epsilon², proves that every nonzero denominator maps to
a unit, and applies the actual localization universal property. Its first
component is proved to be the identity by localization uniqueness; its second
component satisfies the genuine derivation laws. Agreement on B, preservation,
the exact quotient rule and uniqueness are all proved. No chosen fraction
representation, field derivation or preservation conclusion is an input.

`FractionKaehlerFrame318` starts with an actual rank-one frame Ω(B/R)≃B.
The localized dual derivation gives a functional on actual Ω(K/R), and
universal differential generation proves its compatibility with the integral
frame. It sends the mapped integral generator to one, so that generator is
nonzero. The quotient rule shows that all generic differentials are in the
span of that generator. Consequently the functional is bijective and constructs
the actual generic Kähler frame. Neither a generic frame nor nonvanishing nor
a general Kähler-localization isomorphism is assumed.

`FractionSourceSections318` applies the constructed derivation to the literal
J²-scaled source coefficients. The vertical theorem consumes an actual DVR
whose rational prime is irreducible. The horizontal theorems consume actual
local Q-algebra coordinates, differential generation, and the unit-twisted
branch or infinity equation. Both literal coefficients are integral, and one
horizontal coefficient is a unit. The old generic-frame and mapped-generator
premises are removed without changing frozen earlier packets.

## Exact remaining boundary

Existence of the actual source integral rank-one Kähler frame, actual completed
local rings/coordinates and their identification with the differential frame
are still geometric inputs. The vertical reduced-component condition is still
represented by the actual rational prime being a uniformizer. Derivations
constructed from different integral frames are not silently identified; their
actual unit transition is handled by the preceding overlap packet. Actual
source affine atlas, bicanonical sheaf, stack and metric/frame realization are
not asserted here. This does not prove the global GeometricRealization.

Replay: `bash verify.sh`. Lean 4.35.0, pinned Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679, debug.skipKernelTC=false.
No repository/Git or frozen dependency was changed.
