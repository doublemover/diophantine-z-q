# Reconstructed five-pullback differential basis

This packet reconstructs the reported five-form basis result from the published
`5e483a2b186a83500f4b603f3ddfc514ae84a393` checkpoint. It is an alternative proof,
not recovered original source bytes. The historical packet named
`actual-five-differential-basis` and reported receipt SHA-256
`e384519c52280a1d974837d24a95980bba233dc068f411e6519c6634f40a3432`
were not found in the checked-out preservation archives. The older report and
review do not constitute acceptance of this reconstruction.

## Exact result

`ActualFiveDifferentialBasis318.basis` is a `Module.Basis (Option (Fin 4)) ℚ G`,
where `G` is the genuine global intrinsic differential space of the original
complete source `ContactGlobalSmooth318.Model SourceTwistArithmetic318.units`.
Its entries are the original four completed complementary elliptic pullbacks
and the original fifth elliptic pullback. `basis_apply` proves these identities
without changing their normalization. `finrank_eq_five` gives dimension five
for the explicit structural rational scalar action.

The rational action is only restriction of scalars along the original source
structure morphism. It is made explicit by `rationalModule` and used locally;
this packet does not silently replace an ambient scalar structure.

## Alternative proof

1. In an algebra whose actual extension to an algebraic closure is a domain,
   every integral element is a base scalar. The proof splits the integral
   element in the algebraic closure and descends the tensor equality through
   a base-linear functional taking 1 to 1.
2. Properness makes every source global function integral over ℚ. Restricting
   to the actual whole finite source chart and using its proved scalar-
   extension domain shows that every global function is the original
   structural rational constant.
3. The existing omitted-branch divisibility argument only needs invariance
   under the single omitted root flip. Together with the other three branch
   charts and the entire infinity chart, it makes every such invariant form
   a global regular-function multiple of its original elliptic pullback.
   Step 2 makes that multiple rational.
4. For each root flip, the +1 projection is therefore in the corresponding
   elliptic line. Subtract all four projections. The complementary sign
   identities show that the remainder is anti-invariant under every root
   flip. Exact composition of the original whole-scheme sign maps gives the
   full-root character for all sixteen signs.
5. In particular the remainder is fixed by exactly the eight signs defining
   the existing fifth invariant-line theorem. That theorem places it in the
   original fifth pullback line. The previously proved five-pullback
   independence then constructs the basis and its dimension.

No Fourier16 or low-support-vanishing source from the missing packet is used.
No Jacobian, represented Picard scheme, polarization, PEL identification,
Kodaira–Spencer, metric, height theorem or all-integer witness result follows
from this packet alone. A dimension statement here is not a separately
formalized genus theorem.

## Validation

See `receipt.json` for final status, source bindings, strict compiler evidence,
and the private-inclusive recursive axiom audit. A passed axiom audit checks
only the stated dependency roots. Independent review and hosted integration
are separate statuses and must not be inferred from compilation.

`check.sh` rebuilds all seven packet sources in `MODULE_ORDER.txt`, with kernel
checking enabled, and runs `Audit.lean`. Supply Lean 4.35.0, the pinned Mathlib
revision, and a source/dependency-verified progress snapshot in `LEAN_PATH`.
The script does not fetch dependencies and does not claim a fresh rebuild of
the 1,837 predecessor modules. Only the standard `propext`, `Classical.choice`
and `Quot.sound` roots are permitted.
