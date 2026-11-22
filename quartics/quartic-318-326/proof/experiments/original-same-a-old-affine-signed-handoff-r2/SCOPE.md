# One actual affine lift map for both ordered signed cocycles

Fix the old marked Cartesian fibre and the same smooth total family.
For the given affine opens U_j in the total family, put V_j=i⁻¹U_j;
we do not switch or refine the input family. In particular one can use
the exact affine-basis-indexed family in `original_additive_short_exact`.

`original_affine_sections_split` evaluates the existing geometric
splitting, not merely a stalkwise surjection, to get a right inverse
s_j of the actual old right arrow on sections of V_j. That exported
arrow strengthens the previous `original_affine_sections_surjective`,
which is retained as its consequence using the same evaluation.
`original_affine_cover_coeff` chooses this *family of right inverses*
once in the proof of an existential, before the section z and left map
λ are quantified. Its local lift is literally s_j(z|V_j), not a second
choice of preimage; the local lift equations follow from s_j g_j=id.
There is no claim that the geometric splitting itself is unique.
The existing `factor_cover_coeff` consumes these very lifts and both
the old coefficient and its image on exactly V_j∩V_l. It is reused
unchanged. The global `ShortExact` used here is the one from the same
old Cartesian input. Neither `hOld` nor the old lift equations are a
new hypothesis of the joined theorem.

## Two forms and the polarized lines on this cover (paper only)

The single family s_j applies to the given ordered forms z_1,z_2,
with separately evaluated sections t_{j,r}=s_j(z_r|V_j), in the same
order. One *identical section* t_j would not lift distinct global
forms on a covering family: applying the right arrow would identify
their restrictions, so sheaf separation would identify the forms.
Transport for each column retains right minus left; no order or sign
may be absorbed into the choice of a section.

Over the same finite separable field K of the Lan/Yuan comparison,
base extend these very affines. Each actual normalized infinitesimal
positive-translation line, which is marked trivial on the reduction,
has compatible-with-reduction local frames on those same affines of
the constant dual-number scheme. Indeed on an affine V=Spec B the
line is an invertible module M over B[ε]/ε² with specified reduction
M/ε M ≅ B. A lift of 1 generates M, since the cokernel vanishes modulo
the square-zero ideal. The resulting surjection from a free rank-one
module is an isomorphism, as checked after localizing where M is free.
This does not require the ample line representing the polarization
to have a frame on V, and does not produce such a frame.

The independently reviewed Lan/Yuan comparison proves equality of
classes, not of arbitrary local coefficients. On the same covering
family of affine opens of the separated A_K, all finite intersections
are affine and the quasi-coherent Čech computation in degree one
applies. Thus for each ordered column one can gauge its polarized
line frames to the old right-minus-left coefficient: if on an overlap
e_b=(1+ε f_pol_ab)e_a and f_pol_ab−f_old_ab=d_b−d_a, use
new frames (1−ε d_a)e_a. The two gauges are separate, applied in the
original order, and do not change the represented lines. This is an
existence conclusion, not an equality of independently framed
transition functions. It identifies no new special-fibre rank.

The variant requiring literal dlog of transitions of the ample line
itself must first choose a common affine cover also trivializing that
line. It can use the same old construction on that fixed starting
cover, but a given old family need not trivialize the ample line.

This packet has no native Picard, polarization or Čech-class comparison.
The latter, or an actual signed same-cover gauge from a normalized
positive-translation line on the fixed dual-number test, remains the
native geometric handoff for the two polarized columns. The native
candidate here removes old local lifts and their equations as premises;
it does not remove the classical ordered polarization comparison.

Source, pinned production parser/planner and exact dependency
checks only. No Lean compilation, staging, registry change or dispatch.
