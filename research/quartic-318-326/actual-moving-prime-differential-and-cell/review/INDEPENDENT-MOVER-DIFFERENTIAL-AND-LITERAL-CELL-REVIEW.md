# Independent exact review: weight-two mover differential and literal cell

Signed: Vesper, independent cold reviewer. 2026-11-21 UTC.

Reviewed immutable author inputs (manifest and main note, respectively):

- Hom, semistable moving jet differential: `124f1017f3c593373b82d7452ef464045abd80a95e355f3e1d00c22d6399e6a1`,
  `7f99112f1a8f892818c2781c5e581021466e3a6127fb06d8d5356815c15ffd25`.
- Joined, moving additive and literal per-place: `213494c36168bf827b23ff4d7a5b12f7676d41457146f8c3d90914cdac3fa9ad`,
  `f84c782fd467a75090cdaf1a9f70d54ba43c88096a47b147ee28bc92d4f45f04`.
- Joined, direct CM7 orientation canary: `a903c4de3240f4404179235b8e1a258f0ded431bdb796cf1f995845fe19a2842`,
  `78583ca503293405c751658bf83dafb9ac902533cd98d6a7a44d6bc47fa4b3b9`.

All three manifests verified. The three Python runs reproduced their exact
JSON bytes, including the 996 exact moving-translation controls with
the bound XVI donor `6e0f43b016f3ae9e599658f7a96e08afd36bde693ab2b6053357e63a102d07a1`.

**Differential.** Primary Česnavičius, Theorem 2.11, gives the unit Manin
constant at each mover (in fact every prime for this squarefree level).
Primary Mazur, Theorems 1 and 4, bounds the prime divisors of a primitive
isogeny degree, so a primitive rational isogeny to the literal target
contributes only one common unit to the mover sum. The Legendre
Kodaira–Spencer factor is `1/(2λ(λ−1))`: reducing
the exact de Rham derivative modulo `d(y/(x−λ))` gives this
coefficient of `xη`, and the nodal cusp coordinate gives the
negative leading sign at `λ=0`. The simple zero of the Hasse
invariant is essential; the oriented degree-p coefficient then
recovers the ramified tangent. At the paired ideal label the actual
tame mark and its endomorphism transport by relative Frobenius.
The coefficient is conjugated in the conjugate gauge and the
genus sign is `(h′/p)`, not a symbol with the ramified numerator.
The optional ambient zero bound and conditional splitting sieve
do not assert independent distribution or absence of cancellation.

**Cell.** On the exact moving model, translation by the corresponding
rational `T_r=(Dr,0)` gives
`−X/Y=zW/(w(r−r′))` by the original two factor equations.
At the selected prime the three nonzero-root differences strip to
units; the split I₀* component group is identified by the
four rational 2-torsion points. Thus stripping a component by
rational torsion gives a genuine additive homomorphism, killing
torsion, with value `L_p` in the cusp coordinate. With the original
normalization the exact stripped congruence is
`(w²−r)/p = (D/p)·r(r−r′)·L_p² mod p`.
Different certified points can be used for different nonzero local
tests only on the **same** rank-one curve; any required transport must
preserve the mover differential up to a unit. Odd multiples of the
primitive marked representative give the specified compatible
cells exactly when the corresponding generator residues and the
single imposed multiplier CRT permit them.

**Independent orientation and scope.** The direct CM7 Vélu quotient
has reduced action `(x⁷,−y⁷)`; its `c=−1` gives Hasse jet +1
for stripped Δ/7 = -1. Hom independently obtains the same action via
an actual degree-two isogeny, not by reusing the degree-seven kernel.
Both are sign canaries, not evaluations of the actual weight-two
form. The historical `p_a` target is a control in its literal
scale; old `p_b` is a pilot, not a support prime of the new family.
For the literal detector, the square denominator is equivalent to
nonnegative values at all odd-depth `F(c²w²)` contacts under
the stated nonzero and saturation guards. The exact leaf threshold
and the stricter existing positive-product Lean consumer are
not interchangeable. No actual marked value, generator residue,
complete grid of retained cells, rational realization of all poles,
or PointPair is asserted.
