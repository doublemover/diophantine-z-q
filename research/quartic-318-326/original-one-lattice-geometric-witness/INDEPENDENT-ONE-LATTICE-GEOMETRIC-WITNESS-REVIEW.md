# Independent review: geometric witnesses for the original one-lattice height

Disposition: **PASS at paper scope**.
Reviewed exact manuscript `4fa7ab9d4e7b4bc85aee928e1397121698877460d8bdcfc0a1ca0a80abfcf499`.
The existing source-only 426-module target has intake SHA-256
`c27ee2f374518a6e2ddaf1ff695f1c442bb02a459472dcb1d605a2384177d477`
and selector SHA-256
`a811bbd1427be3591f20bda1c2afcdf8a9223cd48e29a6d10687dde8e0e67817`,
with 473 unchanged project-closure entries. The terminal
`SelectedOriginalOneLatticePeriodHeight318` source is
`81ae5faecfbbd4d08df853510d4ad8f16732ebe5cdcc044dd4ff7b29f92698f1`.
This is a reviewed witness map into the drafted theorem, not a
426-module Lean result.

* The original chart is chosen before L. The same full polynomial p,
  abscissa, sign, and coefficient J are retained over Q and L(J).
  The center splitting field and any required common height field
  may be included first. [Javanpeykar, Theorem 4.3.2](https://msp.org/ant/2014/8-1/ant-v8-n1-p04-s.pdf#page=31)
  gives a finite flat normalization and semistable minimal regular
  resolution after a further finite extension. This was checked on
  the primary statement, not inferred merely from good generic fibre.
* The single lattice H is the invariant differential module of the
  Néron model of the original modular Jacobian. Its generic Abel
  identification is independent of the marked base point by
  translation. Exact finite-place localization is (O_{L,v}otimes H);
  the same generic pure tensor recovers the same ordered coordinates.
  No equality with the full integral dualizing lattice is assumed.
* Each point over a height-one prime of the actual normal base chart
  has height one, so the resolution is unchanged there. Semistability
  gives smoothness at the vertical generic points. Shrinking the
  entire finite inverse image to one principal neighborhood gives a
  finite-type smooth source for the Néron extension. Finite duality
  and the generic [trace pairing](https://stacks.math.columbia.edu/tag/0BW0)
  then give the exact scalars (mathrm{Tr}_{F/L(J)}(a b)) on the
  same whole normalization, in the literal (dJ) coordinate.
  There is no branch-field trace or global proper-pushforward
  assertion. [Stacks 0AU3](https://stacks.math.columbia.edu/tag/0AU3)
  supplies the compatibility on the finite-type open.
* The same original basis and symplectic period columns supply both
  bilinear identities for the actual conjugate-first Petersson Gram.
  The normalized squared determinant norm is real period covolume
  divided by (pi^g), so the conversion adds (glog(pi)/2)
  in negative log norm. All embeddings and the degree average occur
  once; no independent period basis or compensating level scalar
  appears.

Thus the paper witnesses are the ones required for the bound on the
same modular Jacobian (J_X), not on the separate quaternionic surface
(A). Transport to (A) still uses the separately proved same-object
quotient/isogeny comparison. The source-side geometry, local trace and
period inputs are not removed by this review. No Lean run.

Signed: independent proof and source review, 2026-11-21.
