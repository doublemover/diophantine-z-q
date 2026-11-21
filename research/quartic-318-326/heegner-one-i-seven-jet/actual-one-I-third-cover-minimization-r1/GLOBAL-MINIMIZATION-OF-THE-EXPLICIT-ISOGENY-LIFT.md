# The explicit relative lift has a globally minimal integral model

Keep the actual \(q=119851\) base and the selected
\(\xi=1066808945\) explicit relative-tangent lift. The same
degree-two map to its marked split cover is retained through
the displayed inverse coordinate changes. This construction is
only minimization; it proves no rational point or rank.

The new exact coefficient array is a pair of integral quadrics,
with full rational GL₂ row change and GL₄ variable change
certified against **the same** raw pair in
EXACT-THIRD-COVER-MINIMIZATION.json. For reproducibility the
checker finds the following simple transformations (the finite
search just locates the indicated common linear reductions,
while equality of the transformed polynomials is checked exactly).

1. Strip the two conic-seed divisors on their respective
   binary parameter blocks. For the first block take
   \(m=m'+r n'/u_0,\quad n=n'/u_0\),
   with \(r\equiv p y_0/(q x_0)\bmod u_0\) and
   \(u_0=90243\). For the second write \(v_0=3w\) with
   \(v_0=743003829\). Use
   \(r_{\mathrm{old}}=r'+t s'/w,\ s_{\mathrm{old}}=s'/(3w)\)
   with \(t\equiv p y_1/(q(x_1/3))\bmod w\).
   Both inverse denominators are units in the indicated rings.
   Total determinant from these two steps is \(1/(u_0v_0)\).
2. At 5 first scale both variables in the first block by 5
   and divide both quadrics by 5 (net determinant 1);
   then use the common line in the second binary block to
   shrink the level by 5. At 1861 and 114649 the common
   lines are already in the first binary block. For a common
   line spanned by \((r,1)\), substitute
   \((x,y)\leftarrow(\ell x+r y,y)\) at that block and
   divide both quadrics by \(\ell\); similarly for the
   other projective chart. This is certified integral and
   multiplies the level by \(1/\ell\).
3. Twice at 2 use a common plane of the pair modulo 2.
   Change coordinates so the plane is the reduction of the
   lattice with one coordinate scaled by 2; both quadrics
   are then coefficientwise divisible by 2. Dividing each
   by 2 gives net determinant \(1/2\) at each step.

Thus the full determinant factor is the inverse of
\(4\cdot90243\cdot743003829\cdot5\cdot1861\cdot114649
=286121976264002095593660\).
The checker independently recomputes the Hessian determinant
pencil and the standard [Cremona–Fisher–Stoll Definition
2.4 invariants](https://www.dpmms.cam.ac.uk/~taf1000/papers/minred-234.pdf).
The new invariant values are exactly \(c_4=16\cdot13d^2\),
\(c_6=-64\cdot35d^3\), and \(\Delta=2^8 3^2d^6\), those
of the literal original \(E_d\) with discriminant valuations
all less than 12. Thus this is a **globally minimal**
integral genus-one model, not just a partial removal of
extraneous seed factors. It remains a relative degree-two
stage, not equations for division by 4 on the Jacobian.

The absolute coefficient maximum drops from about
\(4.54\cdot 10^{24}\) to \(1.45\cdot10^{23}\).
No optimal archimedean lattice reduction is asserted.
The conductor of the underlying elliptic curve is the same
as before, and numerical search or genuine new nonvanishing
is still needed to produce a rational point.

    python3 -B check_third_cover_minimization.py | cmp - EXACT-THIRD-COVER-MINIMIZATION.json
