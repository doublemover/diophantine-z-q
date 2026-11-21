# One actual base twist: minimized split cover and exact Selmer lifts

This reproducible calculation fixes the exact one-I base q=119851 only.
It does not establish a rational point, either paired nonvanishing,
companion admissibility, or rank on the original four-pole family.

- **Result:** globally minimal integral equations for the common split
  cover, literal 2-cover map to its isogenous Jacobian J, and exact
  local Kummer witnesses showing that Sel₂(J) has dimension 3.
- **Lifts:** the accompanying proof uses the alternating Cassels–Tate
  pairing and Fisher's exact image criterion, without assuming finite
  Sha, to show that the marked class lifts to Sel₄, Sel₈, and every
  finite 2-power level. This is existence, not equations for later
  levels or rational points on the covers.
- **Prerequisites:** literal moduli and bounded marked-cover box,
  and the independent full determination of the two local split
  survivors, which the result identifies by an explicit Q-isomorphism.

Run from this directory with Python 3 and the usual sha256sum:

    sha256sum -c SHA256SUMS
    sh replay.sh

No large theta computation, external CAS, package installation, or
network access is needed. The three folder manifests record original
frozen sources.

The review directory holds the independent source review and
standalone rank-23 local-space replay. Neither rank computation
uses a finite-Sha hypothesis.
