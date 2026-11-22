# Exact characteristic-zero models of the 32 fixed CM flags

This is an explicit realization of all the ordinary calibration points in the corrected eight-row real CM replacement. It supplies fixed source models for good-prime specialization; it does not compute any moving intersection, oriented ideal, cubic residue, rank or point. The coefficient field of the *real packet product* remains the smaller real field in the original calibration. The fields below realize individual flags.

## 1. Two shared fields and their residue degrees

Put
\[
 A^4+4A^2-1=0,\qquad s_5=A^2+2,\qquad
 L_2=\mathbb Q(i,A),\quad
 L_4=L_2(\sqrt2),\quad L_{12}=L_4(\sqrt3).
\]
The four roots are \(A,-A,i/A,-i/A\). The element \(s_5\) squares to \(5\); \(s_5-2\) is not a square in the real quadratic field, since it is negative at one real embedding. Thus \(A\) has degree four. Choose a real embedding of \(\mathbb Q(A)\) to see that adjoining \(i\) doubles the degree. The automorphisms \(A\mapsto i/A,\,i\mapsto i\) and \(A\mapsto A,\,i\mapsto-i\) are noncommuting involutions whose product has order four. This proves the dihedral group of order eight. Its three quadratic subfields are the fields of \(i,s_5,i s_5\). Consequently the two added radicals give independent degree-two extensions, and \(L_4,L_{12}\) have degrees \(16,32\).

The calibration quadratic field is \(K_*=\mathbb Q(i s_5)=\mathbb Q(\sqrt{-5})\). The product of the two displayed involutions fixes \(i s_5\); hence the Galois subgroup over \(K_*\) is the cyclic rotation subgroup, and the four lifts of the nontrivial quadratic automorphism are involutions. At every rational prime \(p\notin\{2,3,5\}\) inert in \(K_*\), all the residue fields of \(L_4,L_{12}\) have degree two. Here unramifiedness follows, for example, from the discriminants of the quartic polynomial and the three quadratic polynomials, which have support only at \(2,3,5\). Adjoining the last two radicals to a dihedral involution cannot increase its order beyond two. This does not select a place: the residue calculation must still use the globally compatible chosen place.

For orientation at 29 use the unramified field in the basis \(1,s\), \(s^2=2\), and the literal roots
\[
 A\equiv4,\quad i\equiv12,\quad \sqrt2\equiv s,\quad
 \sqrt3\equiv4s\pmod {29}.
\]
The four roots are simple. The resulting \(\sqrt{-5}=i(A^2+2)\) reduces to \(13\). For context, \(L_2\) also agrees with the conductor-two ring class field: over \(\mathbb Q(s_5)\) the degree-four class polynomial factors as \(Q(s_5)Q(-s_5)\), where
\[
 Q(v;X)=X^2+(-798588586000+357139677440v)X+
           1645850794472000-736046794080000v .
\]
The discriminant of \(Q(s_5)\) is \((388008836800-173522845600s_5)^2(2-s_5)\). These roots lie in \(L_2\); once \(K_*\) is included, the degree over \(K_*\) equals the class number four. This identification is not needed for the source replay.

## 2. Exact coordinates, both endpoints, and the named flag

The table reports \((X,Y,j_A,j_{A/C})\), each as rational coefficients in the basis
\[
 A^k i^{e_0}(\sqrt2)^{e_1}(\sqrt3)^{e_2},\qquad
 0\le k<4,\quad e_j\in\{0,1\}.
\]
Omit the last radical for \(L_4\). The machine order is \(1,\sqrt2\) first, then the remaining monomials ordered by \((e_0+2e_1+4e_2,k)\). The 16 flags of pair conductor four use \(L_4\); the 16 of pair conductor 12 use \(L_{12}\). All \(4X,Y,j_A,j_{A/C}\) are integral in the indicated power/order basis. Maximum numerator bit lengths are \(5,19,242,242\), respectively for the four vectors as printed, and their denominator lcms are \(4,1,1,1\).

The exact characteristic-zero calculation verifies on each row
\[
 Y^2=X^8+14X^4+1,\qquad
 j_{48}(X,Y)=j_A,\qquad
 j_{48}(w_{48}(X,Y))=j_{A/C}.
\]
Use \(t=X-2+6X/(Y+X^4+1)\), the three maps \(t\mapsto t^2/(t+2),t^2/(t+4),t^2/(t+16)\) with their **current** argument, then \(j=(t+256)^3/t^2\). Also
\[
 w_{48}(X,Y)=((X+1)/(X-1),4Y/(X-1)^4).
\]
Both Hilbert class polynomial equations for the actual two endpoint conductors are verified after clearing nonzero denominators. The degree assertion for each named ring class field follows without a new class-field generator theorem: the higher-conductor endpoint \(j\) already generates over \(K_*\) a field of degree \(h_f\) by the usual CM theorem, and the containing field \(L_f\) has exactly that degree over \(K_*\).

The table of exact complex points is not an unlabeled Hilbert root list. With the named place at 29, both coordinates reduce modulo \(29^6\) to the exact pointed lifts in the pinned characteristic-zero calibration donor (manifest 8b5ac3f57327a9f2faf03ae151ceaf0c1048633674bbf6059c28e499944bca3c). That donor checked the simple two-equation Jacobian and unique canonical CM flag in each disc. The source equation and the residue disc therefore identify the literal analytic flag; the exact target CM equation provides a second endpoint check. A rational LLL search found the small vectors, but is neither part of the replay nor required for their validation.

## 3. Local use and limit

A good-prime evaluator can now specialize the *actual, ordered* fixed points by small-field arithmetic even at an unrelated prospective intersection prime. The coordinate denominators are supported only at two, and at any inert collision prime the field degree remains two. The moduli flag is the specialization of the exact characteristic-zero point; if a particular formula for a rational modular parameter has a removable denominator at the new prime, use its regular geometric chart rather than discard the row. A fixed seed elliptic model, choice of a compatible local orientation, and transported torsion/isogeny data are still needed for the valuation algorithm. This paper does not fill the moving norm, equality, or nonvanishing step.

From the preserved source layout, run:

~~~sh
sha256sum -c SHA256SUMS
python3 -B check_exact_calibration_field.py | cmp - EXACT-CALIBRATION-REPLAY.txt
~~~

Replay uses only the Python standard library, exact rational arithmetic and the pinned class-polynomial/flag donor.
