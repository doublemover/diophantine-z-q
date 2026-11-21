# The same D=210 point on the genuine U(3)/U(11) fine atlases

## One underlying polarized object, one overlap

Retain the already fixed original noncontact argument t=32u/v, its
chosen geometric point, and its same polarized O-surface A with the
fixed Rosati datum. No change of coarse coordinate, Atkin–Lehner sheet,
arithmetic root constants (-14,-6,42,-21), or ambient cyclotomic
embedding is made. The construction here takes place only in the
height branch of the same-surface comparison.

Use the principal-level moduli in [Yuan v2 §2.1, pp. 4–5](https://arxiv.org/pdf/2205.11334#page=5):
for N=3,11,33 the genuine fine X_N is proper, regular and semistable
over Z[1/N], with the universal abelian surface and its canonical
compatible principal polarization for the fixed mu. Here these are
quaternionic schemes, not the elliptic modular curves of these levels.
On Z[1/33], the correct fiber product is over the *maximal PEL stack*,
not its coarse curve:

    X_33 = X_3 ×_{X_max} X_11  on Spec Z[1/33].

The identification uses full principal markings only. An object on
the right includes an isomorphism of the underlying O-objects; using
this isomorphism to place the two markings on a single A preserves
the polarization by uniqueness. Merely matching a coarse rational
point over a field would not give that isomorphism (quadratic twists
can obscure it).

The explicit CRT map on A[33], as fppf group functors, is
P -> ([22]P,[12]P). The inverse sends (P_3,P_11) to P_3+P_11.
Indeed 22=1 mod 3,0 mod 11 and 12=0 mod 3,1 mod 11;
22+12=1 mod 33. The same central integer operations give the
decomposition of O/33 into O/3 and O/11 as rings, even for a
noncommutative O. The point-functor identities therefore give a
scheme-level isomorphism of the two torsion kernels by Yoneda,
and assemble the exact two full O-linear markings into the
single full 33-marking. The preexisting eta_3 is unchanged:
using [11] rather than [22] would wrongly negate it. There is no
separately imposed symplectic marking in this PEL level convention.

Over the actual marked 3-point, the generic 11-torsion is the regular
left M2(F11)-module. At every prime where p does not divide 11 the
same assertion holds on geometric fibres of the existing fine
abelian scheme: the two matrix idempotents give isomorphic
two-dimensional summands of its four-dimensional etale torsion.
Change of 11-marking is by an O-linear unit, so over the overlap
the projection X_33 -> X_3 is finite etale, and has degree
|GL2(F11)|=(121-1)(121-11)=13200 over the full 3-mark. If needed,
adjoining the actual 11-torsion after F_3 has degree at most 13200,
but no such height-extension degree enters the GR/modularity bound.
The other projection is similarly finite etale on the overlap.

For clarity, on one characteristic-zero maximal coarse sheet with
automorphism group exactly {+1,-1}, the level-3 skew residue model
has 72 units, and the combined simultaneous sign quotient has
72*13200/2=475200 points. The separate coarse product gives
(72/2)*(13200/2)=237600, losing the relative sign. These counts
are per coarse X_max sheet, not per original W-quotient coordinate
or a claim about connected components. No such coarse quotient
or count is needed for trait extension. The 13200 relative degree
does not divide by sign: the fixed full eta_3 has no residual sign.

## Proper extension and evaluation in the actual finite norm ring

Take one height number field L carrying both prescribed structures,
for example after adjoining the 11-torsion to a field defining
the selected fine 3-mark. The CRT lift supplies the single generic
33-point over L. For a finite place w write R=O_{L,w}; use the
actual finite-place prime in the ring of integers. Its fraction
field is L. The equality of subrings

    O_{L,w} = {x in L : w(x) <= 1}

is derived directly in the proposed Lean source from the
HeightOneSpectrum valuation and the increasing WithZeroMulInt
absolute-value realization at exactly w. This is the same subring
used by the existing finite norm consumer, not a completed or
normalized substitute.

For w above 3, 11 is a unit, using 4*3-11=1 in the original
prime ideal. Then use X_11. At all other w, 3 is a unit and use
X_3. These places give genuine maps from Spec R to the
appropriate Z[1/N] via its localization universal property.
The actual generic map extends uniquely to the chosen X_N by
properness. At w away from both 3 and 11, the single generic
33-point extends uniquely to X_33; its projections must be
those same X_3 and X_11 extensions by their uniqueness.
There is **no** 33-extension asserted at w over 3 or 11, nor
an extension of the wrong prime-level marking there.

The old finite-stencil evaluator is now produced from that actual
extension: take the stalk map at the closed point of Spec R, identify
the stalk of Spec R there with R by localizing at its units, and
compose with the canonical map into the norm-bounded subring.
On the 33-overlap, these actual evaluation maps commute with the
two forgetful stalk maps by the ordinary stalk-map composition law.
The actual map on the residue value t at the generic point remains
the supplied original point map by the upper triangle of the
valuative criterion.

The pulled-back universal abelian scheme is the good model of the
same generic A on each trait. On the overlap the universal families
pull back identically by the representing property just proved.
Even outside the overlap, each pulled-back good model is the
Neron model of the same A (the classical Neron mapping property
for abelian schemes over a DVR), hence induces the same stable
Hodge line where applicable. This does not assert that the base
changed arithmetic Shimura curve stays regular.

## Exact local reduced fiber on the overlap

The forgetful maps of fine charts above are etale, including at
the quaternion-bad primes 2,5,7 where the 33-overlap is valid.
Thus at compatible geometric closed points their strict henselian
local models identify; no changed horizontal shape or node
multiplicity is introduced by forgetting full prime-to-p marking.
At 3 use the true regular semistable X_11 fibre, and at 11 the
true regular semistable X_3 fibre.

Independently, the standard reduced semistable local model is
explicit. After splitting a branch pair by etale localization,
[Stacks 53.20–21](https://stacks.math.columbia.edu/tag/0C58)
gives the original completed nodal stalk with equation xy-h
over an unramified completed DVR. At a genuine node h is
nonunit; regularity forces v(h)=1, since otherwise p,x,y would
have independent classes in m/m^2 in dimension two. Absorb its
unit to write xy-p. Modulo p its polynomial chart has ring
k[x,y]/(xy) for the corresponding residue field k. The two
independent prime variables imply that if xy divides F^m then
xy divides F, which proves reducedness after every field
extension k'/k, including characteristic 2. At smooth points
reducedness is immediate. This model belongs to the original
regular atlas, not a ramified height-trait base change of it.
One can also directly use the reduced fibers in Yuan's stated
semistability, then localize them at a height-one vertical
generic point. The previous reduced-DVR source supplies
irreducibility of the actual p there, not an invented
uniformizer or a special-fibre squarefree assumption on torsion.

## Native scope and replay

The source contains the literal additive [22]/[12] projector
equivalence, the standard reduced two-axis fibre computation,
the exact original number-field norm-ring/level base map,
the proposed Native Mathlib valuative-criterion application and
compatibility of the resulting stalk evaluation. It does not
construct the PEL representing schemes, their universal abelian
schemes or the etale moduli comparison natively. Those come
from the classical moduli theorem and the CRT argument above.
The branch coordinate pole coefficients, Koszul cotangent maps
and Yuan determinant KS rows come from the separate exact
packets, not re-assumed as conclusions here. No native compile.

Run `sha256sum -c SHA256SUMS` here; run
`python3 check_original_fine_overlap.py | cmp - EXACT-FINE-OVERLAP-CONTROLS.json`
for exact CRT, marking residue, relative-sign and localization
unit controls. Validate `DONORS.sha256` from the workspace root.
Pinned primary Mathlib APIs used: v4.35 commit 56a005855ea17e0b0958f73ec801ae140b0a1679,
`ValuativeCriterion.lean`, `CommSq.lean`, `FinitePlace.lean`,
`AdicValuation.lean`, `ValuationSubring.lean`, `Int/WithZero.lean`,
`Localization/Away/Basic.lean`, and `AffineScheme.lean`.
