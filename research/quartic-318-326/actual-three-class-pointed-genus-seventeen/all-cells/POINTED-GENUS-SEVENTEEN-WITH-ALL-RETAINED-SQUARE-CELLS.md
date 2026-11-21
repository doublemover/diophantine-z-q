# The genus-17 pullback can retain all prescribed local square cells

Use the same actual three-factor family 48ae5e44 and the pointed Selmer-four
theorem 4d43636f. The sixteen old contact balls and the added actual pilot
are retained at their **squared parameter** values on the selected 4-cover
pullback, in addition to the three newly selected primes' positive depth-one
square cells. This is a simultaneous local condition on one global cover,
not a single rational parameter, independent chosen w-signs of one rational
point, or complete support of the remaining factors.

## 1. An exact local square cell is a two-element target for a 4-class

At a fixed old incidence prime p not among the moving support of the
first two classes and not the third pilot (this is a subset of the
earlier sixteen), let \(w_p^2\) be the exact retained square value
in the chosen p² ball. Use the actual local point of the two-factor
curve C₂ at \(w_p\) supplied by the original a,b-square quotients.
Its projection \(Q_p\) on \(E_D\) has x-coordinate \(D w_p^2\).
It is nonexceptional because all three linear factors of \(x(Dw_p^2)\)
are units there. Its local 2-Kummer class is exactly \(\alpha_p\).

Inside \(H^1(\mathbf Q_p,E_D[4])\), prescribe the raw lifted 4-class
to lie in
\[
 \{\kappa_4(Q_p),\kappa_4(-Q_p)\}
   =\kappa_4(Q_p)+j\langle\alpha_p\rangle                       \tag{1}
\]
where \(j\) is coefficient inclusion. Indeed the Kummer identity
\(j\kappa_2(Q_p)=\kappa_4(2Q_p)\) gives the two values on
the right, since \(3Q_p\equiv -Q_p\bmod4E_D\).
The set can have cardinal one. It does not specify a sign of y
or of w.

A locally Kummer 4-class equal to \(\kappa_4(Q)\) has a local
point over Q: in the trivial genus-one torsor presentation its
covering map is [4] translated by Q (with the inverse convention
the sign is harmless here since both signs are permitted).
An isomorphism of the projected 2-cover to the literal C₂ is over
\(E_D\), so its point over \(\pm Q_p\) has the required \(w^2\).
Any deck ambiguity on C₂ leaves \(w^2\) unchanged. Thus (1)
suffices for the literal prescribed cell, not merely the local
isomorphism class of an abstract cover.

## 2. Add these actual local endpoints to the pointed obstruction

Keep the strict B places and the three unpointed exceptions from
4d43636f. At the fixed incidence primes in §1, the normalized
target \(\beta_p\) is now \(\kappa_4(Q_p+T)\) modulo
\(j\langle\alpha_p\rangle\), for the same marked rational t-root
torsion T. The preimage of the allowed difference is precisely
\[
 M_p=\kappa_2(E_D(\mathbf Q_p)[2])+\langle\alpha_p\rangle .
\]
This follows from exactness of the coefficient sequence (kernel
of \(j\)) and (1). Test the new global defect against \(M_p^\perp\)
at these p instead of the ordinary local subgroup. The dual
pairing still has a global cup primitive: at each of these p
the marked normalized class \(F_{*,p}=\alpha_p+\kappa_2(T)\)
belongs to \(M_p\). The other places are exactly those of the
already checked pointed argument. The local target representatives
remain ordinary Kummer lifts, so the defect functional still
restricts to the ordinary Cassels row on ordinary Sel₂; it still
vanishes on rational torsion and on the marked line.

Enlarge the fixed ramification set in §2 of 4d43636f by these
incidence primes. They are in the existing finite Gaussian
retained-prime ray, not new ramification outside its support.
The ratio of any two admissible \(q_b\)'s is a square at these
p because the exact original q_b unit-sign phases on those
balls already coincide. Scaling the old and new twists by a
local square root preserves \(w_p^2\) in the displayed literal
maps (the x-coordinate is multiplied by \(D'/D\), and the y
coordinate by a chosen \((D'/D)^{3/2}\)); the two possible signs
in (1) are preserved as a set. Choose the local pointed target
for the new twist by transporting the old Q_p, also transporting
the same labeled T. Thus the same direct Smith cochain variation
has no contribution at these new fixed test sites. It is still
the difference of the two governing Artin bits at \(q_b,q_b'\).
In particular the new local structure is fixed on the normalized
2-class space, not a different dual tester space at each prime.

The real/2/3/47 local rules and the two central inertia pivots
are unchanged (the additional incidences are >76176).
The annihilator is again exactly the marked line. Poitou--Tate
with these \(M_p\)'s therefore gives a single actual 4-class
satisfying all these target conditions at once. The existing
gcd-density tail is unchanged because the extra ramification
is at sites already included in the old ray. This does not
require proving that the fixed Sel₂ localization surjects
onto the extra cells; the pointed defect on its larger dual
space was genuinely included in the prime selection.

## 3. Attach the third factor and retain the checked scope

Select \(q_c\) afterwards, by 48ae5e44, without changing this
actual \(a,b\) curve or its pointed 4-class. At each §1 place
the third equation holds on the whole exact selected \(w^2\)
cell, by that proof's prescribed square quotient. Hence the
lifted point of §1 can satisfy the third equation there,
whichever sign in (1) is used. At the four moving places of a,b
use the ordinary deck argument of 534279af; at \(p_c,q_c\) use
its two sign-orbits argument. They retain the prescribed \(w^2\)
cells. At every other place use the already proved fixed strict
or automatic conditions of 4d43636f. The same genus-17 proof
and common h remain in force. No numerical q's, global point,
sign choice on all local representatives of w, or Lean result
is asserted.
