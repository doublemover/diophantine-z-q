# The remaining odd places of the exact alternate next cover

Retain \(D_\tau\), \(c=C/Z\), \(H=Z^2-\beta C^2\), and
\(L'=49\beta C^2-48Z^2\) from dfc383d9. The positive
squarefree representative \(\tau=B_*H_*\) uses the same
normalization \(B_*\mid\beta,\ H_*\mid\operatorname{rad}(H)\).
This note completes the local table outside \(2,3,\beta\)
when combined with cf7fb20c at the alternate \(L'\).
No global point is inferred.

For each local point of the base curve obtained below, one
has genuine conic parameter pairs by the exact conic
parametrization. Saying that the corresponding proportionality
has class \(\tau/Z\) means a local square rescaling realizes
that point on the particular \(D_\tau\).

## Good places, including primes of the denominator

Let \(p\nmid6\beta C H L'\). The two projected binary forms
of each parameter pair never vanish simultaneously modulo
\(p\). The block pencil determinant of \(D_\tau\) has four
distinct roots: \(\tau,H,C,L'\) are units at \(p\); the same
substitution in the second block's roots as in dfc383d9 works
even if \(Z\equiv0\bmod p\). Indeed in that case its first
block at such a root is \(-7\beta^2 C^2/4\); the only new
exception would be \(p=7\), but then \(L'\equiv0\bmod p\)
when \(Z\equiv0\bmod p\). At the actual 7, \(Z\) is a unit.
A simple determinant pencil gives a smooth genus-one special
fiber for each unit \(\tau\), so Hasse and smooth lifting
give a local point. In particular **all primes of the actual
denominator \(Z\)**, outside \(2,3,\beta\), are in this case:
\(C,H\) are units there by primitiveness and \(\beta\) being
a unit, and \(L'\) is a unit unless \(p=7\), already excluded.
There is no extra local test supported on such a prime of \(Z\).

## Primes of the scalar numerator

Let \(p\mid C,\ p\nmid6\beta\). Then \(Z,H\) are units,
\(\tau/Z\) is unit, and \(c\equiv0\bmod p\). The precise
local condition is that \(\tau/Z\) is in \(\{1,3\beta\}\)
in the local squareclass group (one or two unit classes).

For necessity only the case when \(3\beta\) is square needs
an argument: if it is nonsquare the displayed set is already
all unit classes. Take a unit square root \(\rho^2=3\beta\).
The transform \(X_2=X+cY,\ Y_2=Y+\beta cX\) is the
identity mod \(p\). At least one of the two lines
\(2Y\pm\rho X\) is unit on a primitive pair, and the
corresponding line on \((X_2,Y_2)\) has the same residue.
The conic parametrization expresses their quotient as the
proportionality \(\tau/Z\) times a square. Thus this class
must be square.

For sufficiency one can take \(x=0,Y=1\). Then \(U=\pm2\)
and \(V^2=4-3D\) is a unit square, choose \(V\equiv-2\bmod p\).
With \(U=-2\) the exact tangent numerator and denominator
both reduce to 4, yielding the unit class 1. Reversing one
original ordinate changes the class by \(3\beta\), giving
the other possible class when distinct. The use of \(x=0\)
over this local field does not contradict its separate
exclusion for rational points at the actual prime 13.

## Primes of the numerator of \(\delta\)

Let \(p\mid H,\ p\nmid6\beta\). Then \(C,Z\) are units
and \(\beta c^2\equiv1\). **All four local squareclasses**
of \(\tau/Z\) are possible; there is no local restriction
at this prime of \(H\). Here is a constructive proof, also
accounting for ramified classes.

Choose a unit root \(\sigma^2=\beta\) with
\(e=\sigma c\equiv1\bmod p\), and let
\(h=v_p(1-e)=v_p(H)>0\), since \(1+e\) and \(Z\) are units.
Write \(L_\pm=Y\pm\sigma X\). The actual transform is diagonal:
\[
     (L_{2,+},L_{2,-})=((1+e)L_+,(1-e)L_-).
\]
In these coordinates the conic square is
\((L_+^2+14 L_+ L_-+L_-^2)/4\).
Thus whenever exactly one of the two eigenline coordinates
is a unit and the other vanishes mod \(p\), its conic
ordinate can be chosen by unit Hensel. In the primitive
standard parametrization the relevant line forms are
\[
   L_\pm(P(r,s))=(\sigma r\pm s)(\sigma r\pm3s).
\]
At either coordinate direction one may choose the branch
\(\sigma r/s=+1\) when \(L_-=0\), and \(\sigma r/s=-1\)
when \(L_+=0\), modulo \(p\). The remaining coordinate in
that parametrization then has unit squareclass 8.
To see these are legitimate choices, use the two possible
signs of the original ordinate: the inverse conic maps have
slopes \(+1,+3\), or \(-1,-3\), after multiplication by
\(\sigma\) at the corresponding projective point. They are
distinct, \(s\) is unit, and the chosen residue slopes lift
with the appropriate exact square-root sign.

* For classes of even valuation, take the first primitive
  parameters with \(s=1\) and with \(L_+\) a unit of either
  Legendre sign. Both signs occur: the two factors in
  \(L_+\) have distinct roots, and the product character sum
  is \(-1\), whereas there are \(p-2>1\) nonzero values.
  The transformed \(L_{2,+}\) is unit and \(L_{2,-}\) is
  divisible by \(p\). Choose the second branch giving
  its canonical \(L'_+\) squareclass 8. The actual unit
  proportionality then has class \((1+e)L_+/8\), and this
  takes both unit signs.
* If \(h=1\), start instead from a second primitive pair
  with \(v=1\) and \(L'_-\) unit of either Legendre sign;
  the same character argument gives both. Pick the first
  raw projected coordinates by
  \(L_-=L'_-,\ L_+=(1-e)L'_+/(1+e)\).
  After forward transformation the raw pair is
  \((1-e)\) times the chosen second pair. The raw first
  point has a conic lift on the branch whose canonical
  \(L_-\) class is 8. Therefore, after normalizing that
  first parametrization, the proportionality class is
  \((1-e)\cdot8/L'_-\). Its valuation is odd and the
  unit sign ranges over both choices.
* If \(h\ge2\), use first raw lines \(L_-=1,\ L_+=p a\)
  for a unit \(a\) of either sign. Choose first conic branch
  whose canonical \(L_-\) class is 8. The transform divided
  by \(p\) has unit \(L_{2,+}/p=(1+e)a\) and other
  line divisible by \(p\). Choose the second branch whose
  canonical \(L'_+\) class is 8. Hence after including the
  first normalization the class is \(p(1+e)a\),
  again both odd-valuation possibilities.

These cases exhaust all four local classes, even when
\(v_p(H)\) is larger than one. They do not determine whether
the global product of such primes gives an admitted \(\tau\)
at each individual \(C\)- and \(L'\)-prime and at \(2,3,\beta\).

## Finite linear criterion for local solubility of this cover family

The small-place necessities in dfc383d9 are also sufficient
locally. At \(2\) take \(x=1\), whose two original squared
ordinates are units 1 mod 8. Their tangent ratio has one
of the two classes \(5,7\), and flipping a sign multiplies
that class by \(3\beta\equiv3\bmod8\), reaching the other.
At \(3\) and at every prime of \(\beta\) take \(x=0\)
and both ordinates negative in the indicated residue class,
giving class 1 before a sign flip; the flip realizes the
allowed class \(3\beta\). At the real place the original
two conics have common positive inequalities in a
neighborhood of \(x=0\), and any \(\tau>0\) gives the
required real square scale.

Consequently, for the normalized positive squarefree
\(\tau=B_*H_*\) the exact local criterion is the following
finite system of Legendre/Jacobi equations. It is linear in
the support bits once the actual support and residues are
known. All displayed Legendre arguments are units:
* \((-2/\tau)=-1\) and \((\tau/3)=(Z/3)\).
* For every \(p\mid\beta\), let \(b_p=1\) if \(p\mid B_*\)
  and 0 otherwise. Require
  \[
    \left(\frac{(\tau/p^{b_p})Z}{p}\right)
      =\left(\frac{3\beta/p}{p}\right)^{b_p}.
  \]
* For every \(p\mid C,\ p\nmid 6\beta\) with
  \((3\beta/p)=+1\), require \((\tau Z/p)=+1\).
* For every \(p\mid L',\ p\nmid 6\cdot7\beta\) with
  \(p\equiv1\bmod4\) or \(v_p(L')\) odd, require
  \((7\tau Z/p)=+1\).

There are no remaining local equations for this fixed scalar
(the actual 7 is good). In particular, unknown primes of
\(H\) provide variables but not their own local equations.
This is a local criterion on the displayed degree-two family,
not a rank computation or an assertion that it accounts
for every isogeny covering of the Jacobian. The actual
factor supports and reduced \(Z\) residue characters remain
uncomputed, so the system has not been solved globally.
