# Independent cold review: the actual Abel map supplies its own pre-log derivative

**PASS**, exact paper and provenance, 21 November 2026. The display-corrected
paper SHA-256 is
`cc8a815829c4f666b7dd00d1f3a4976730f0d9ba889ff57ffb399fafb0d5091b`,
author checksum list
`35aed4b45ff44e67fb7f45da761eaa864dabfbd6c6cad4e531fe4a24e5cd5838`,
and matching provenance list
`ed8c5100103436d77198b4f5dceda7ae082c4730c1b2daf766123a746365efbf`.
All member checksums verified. I checked the display successor against
the earlier reviewed argument; the TeX repairs did not change its math.

* By [Milne, Jacobian Varieties, Proposition 2.2](https://jmilne.org/math/xnotes/JVs.pdf#page=6),
  pullback along this algebraic Abel map identifies actual invariant
  cotangent forms with regular differentials on the same original curve.
  The evaluations of their chosen ordered lifts give the tangent frame
  $E:T_0J_X\to V$. Thus $ED^{-1}(u-u(0))$ is a genuine normalized
  identity chart, and its composite with the actual exponential in that
  frame has identity *strict* derivative by finite-dimensional
  holomorphic regularity. [Milne, Abelian Varieties, Proposition 2.1](https://www.jmilne.org/math/CourseNotes/AV.pdf#page=17)
  is used for that same actual exponential, not to identify its kernel
  with an unproved lattice of Abel periods.
* Translation by $-a(z)$ carries the tangent at $a(z)$ back to the
  identity; invariance gives the signs and no matrix/conjugate factor.
  Therefore the centered chart derivative is the pullback of the same
  differential frame along the literal modular parameter. On the
  ordinary chart its evaluation is the strict hosted local Kähler readout
  times $J'$, without dividing by $J'$. The actual filled-curve
  comparison and holomorphic identity theorem extend the pulled forms
  to the omitted elliptic points instead of claiming $dJ$ remains a
  generator there.
* The inverse function theorem gives a single disk lift of the actual
  Abel value, since the local inverse composition and the desired
  translated value lie in the same injective chart. Recenter at each
  point using the increment of this lift; the same inverse at zero
  proves the required derivative everywhere on the disk. The normalized
  primitive differs from each local lift by a locally constant vector,
  so $q\Phi-a$ is locally constant on the connected upper half-plane
  and equals $-a(i)$. Equivariance then forces its actual period
  increments to land in $\ker q$.

This is the classical same-curve/same-Jacobian deduction, with independently
hosted local rational readout; it is not a hosted compile of the new identity
chart or global analytic geometry. The reverse inclusion in the period
lattice, arithmetic center regularity, the other direction's QM surface,
and the full quartic endpoints are outside this review.

Signed: independent mathematical and evidence reviewer.
