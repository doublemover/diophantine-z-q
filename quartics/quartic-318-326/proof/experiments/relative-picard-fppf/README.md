# Genuine associated fppf line-class sheaf

Three new sources construct the associated group sheaf of the original
relative line-class presheaf on the actual big fppf site over the original
base. They prove its universal property, local representatives by original
line sheaves on full fiber products, and local equality detection. All five
original completed quotient maps induce the exact associated-sheaf pullbacks.

The complete nine-source closure passes strict Lean 4.35.0 checks and a
private-inclusive recursive audit of **149 declarations**, with only
`propext`, `Classical.choice`, and `Quot.sound`. Six sources are byte-identical
copies from the independently accepted relative-picard-pullback packet,
included for closure against the pinned 1,837-module baseline. They are not
six additional results. The 471 baseline predecessors were reused from
source/dependency/toolchain/hash-verified artifacts, not freshly rebuilt.

This is an actual fppf group sheaf. It is not yet a representing scheme or
algebraic space, a degree-zero component, a Jacobian, or an isogeny. Effective
descent of chosen line objects and their morphisms is a further comparison,
distinct from the proved associated-sheaf local interpretation.

`APPLICATION.md` records the exact nine-obligation application contract.
`NEXT-PREREQUISITES.md` records bounded library support and the concrete
degree-zero/representability work still needed. `validation/receipt.json`
binds the sources, strict compiler logs, and recursive audit. Independent
source acceptance and any coordinated admission are separate evidence.
