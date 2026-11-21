# The positive-root quotient's supported Cassels sign is absolute: the rigid clone passes, the altered clone fails

Keep the exact pointed three-factor family and the two genuine last-prime
phases of adb654f1. Write \(T=2399,\ u=1/T,\ t=u/c_2^2,\ \Delta=u-t\),
\(b=p_bq_b,\ c=p_cq_c,\ D=bc\).
On \(E^{tu}_D:y^2=x(x-Dt)(x-Du)\), use the two exact supported
classes
\[
 A=(D,c,b),\qquad F_{\rm raw}=(1,D,D).
\]
Then the exact **sign** of their Cassels--Tate pairing is
\[
 \boxed{(-1)^{\langle A,F_{\rm raw}\rangle}
           =\left(\frac{T}{b}\right)_4
              \left(\frac{T}{c}\right)_4.}                    \tag{1}
\]
Each quartic symbol is the product of the ordinary sign-valued
quartic characters at its two odd support primes, where T is a square.
Consequently the previous rigid Gaussian clone has pairing zero;
the norm-preserving changed residue has nonzero pairing. The latter
family is everywhere locally soluble with all specified squared cells,
but neither C₃ nor the genus-17 pullback has a rational point.
No full radical statement for E_bc, numeric new prime, or inference of
a rational point from the zero sign is made.

## 1. Use an actual global rational torsion lift on the untwisted model

Normalize both classes as in adb654f1:
\[
 A^*=(u,b\Delta,bu\Delta),\qquad F^*=(1,-T,-T).
\]
Subtracting rational torsion Kummer classes changes no pairing.
Reverse the two arguments; at two-torsion values the alternating
pairing is symmetric. The advantage is that on the untwisted
positive-root model
\(E^{tu}_1:y^2=x(x-t)(x-u)\), the class \(F^*\) is **literally**
the rational 2-Kummer class of \(T_0=(0,0)\):
\((tu,-t,-u)=(1,-T,-T)\) because t,u have class T.
Thus choose the actual global cocycle \(\beta_1=\kappa_4(T_0)\)
as a 4-lift of this first argument. We do not require the other
argument \(A^*\) to be Selmer on \(E^{tu}_1\), and we do not
apply an untwisted Selmer pairing to \(A^*\).

Transport this global cocycle by the quadratic twist isomorphism
\(\phi:E^{tu}_1\to E^{tu}_D\) over \(\mathbf Q(\sqrt D)\).
The elementary cochain identity from [Smith, proof of Theorem
3.2, (3.1)](https://arxiv.org/pdf/1607.07860) is
\[
 d(\phi\beta_1)=\chi_D\cup F^*.
\]
It follows just from the \([-1]\) twist on 4-torsion and
\([2]\beta_1=F^*\), so no Selmer hypothesis on the second
argument is needed for this identity. The Weil cup
\(F^*\cup_{e_2}A^*\) is exactly
\(\chi_{-T}(g)\chi_T(h)\); as in adb654f1 use the **unmodified**
quartic high-bit \(\Gamma\) on \(\mathbf Q(i,T^{1/4})\)
as its differential primitive (there is no orientation-swap
cochain in this argument). Therefore \(\chi_D\cup\Gamma\)
supplies a global primitive for the degree-three correction
in the ordinary actual pairing on \(E^{tu}_D\).
With \(\beta_v\) any genuine local 4-Kummer lift of \(F^*_v\)
on \(E^{tu}_D\), the local corrected cocycles are consequently
\[
  (\phi\beta_{1,v}-\beta_v)\cup_{e_2} A^*_v
                     \ \pm\ \chi_D\cup\Gamma_v.
\]
The signs of the two terms do not change their half-integral
invariants. This is the ordinary definition with an explicit
global 1-cochain lift and explicit correcting primitive, as
in the same Smith proof. All classical global and local
pairing hypotheses are on the actual target curve, where both
classes are honest Selmer classes.

## 2. Compute every possibly contributing place

At p dividing B and at infinity D is a local square. Use the
transport of the actual rational point class \(\kappa_4(T_0)\)
as the local \(\beta_v\) there. Both terms are zero. At all
odd p outside Bbc both curves are good, the cochain and
the chosen local lifts can be taken unramified, and the
corrected cocycle has zero invariant. This follows also
literally for the transported rational torsion Kummer lift
since its [4]-division fiber is finite étale in good odd
reduction; the correcting field is unramified there.

At all p dividing bc both t,u are square units and \(-1\)
is square (the actual pilot signs and 1 mod8). Thus \(F^*_v=0\);
take \(\beta_v=0\). At the two c primes, \(A^*_v=0\) too:
u is a square and \(b\Delta\) is a square there by the exact
opposite-factor phase. At the b primes the valuation vector
of \(A^*_v\) is 011, so its inertia is the root-zero point
\(T_0\). Over the untwisted local field, \(T_0\) has a rational
half \(Q_0\) since its 2-Kummer class is zero. More literally,
choose a fourth preimage used to represent the global
\(\kappa_4(T_0)\); its double is one of the local halves,
all locally rational because \(E[2]\) is rational.
The restriction of \(\beta_1\) already takes values in
\(E[2]\) and is precisely the 2-Kummer cocycle of that
half. The twist transport on \(E[2]\) is the identity.
This cocycle of \(Q_0\) is unramified at the good odd
prime on the untwisted curve. The local cup with
\(A^*_v\) therefore evaluates its Frobenius on \(T_0\),
which is the quadratic character of \(x(Q_0)\).
An actual half has \(x(Q_0)^2=tu\) by the duplication
numerator for \(x([2]Q_0)=0\). Thus the sign is
\((u/c_2\,/p)\); the alternative sign of the square root
is harmless at p congruent to 1 mod4.
The product of this term over the two b places is +
by quadratic reciprocity: \(u/c_2\) is supported on B
and sign, b is positive and square at all primes of B,
and its two primes are 1 mod8. This includes possible
rational denominators of \(u/c_2\).

The remaining correction \(\chi_D\cup\Gamma_v\) at each
p dividing bc has sign \((T/p)_4\): the two quadratic
characters \(\chi_T,\chi_{-T}\) are locally trivial, so
\(\Gamma_v\) is the unramified quartic high bit; \(\chi_D\)
has odd valuation. Multiplying over the four support
primes proves (1), with no missing reference value.

## 3. Use the actual clone residues

Euler's criterion gives
\((T/p_b)_4=-1\) for \(p_b=9807649\), and
\((T/p_c)_4=+1\) for \(p_c=6469193\).
Over \(\mathbf Q(i)\) the pure quartic field is cyclic,
with conductor exponent at most one at T and no
ramification outside 2,T. At 2 the conductor divides
the polynomial discriminant \(256T^3\), hence is already
covered by the enormous \(2\)-part of \(8B\)
(\(2^8\mid8B\) suffices). Thus a rigid clone has exactly
the quartic sign of its pilot prime; either conjugate
orientation gives the same sign because these primes
split in \(\mathbf Q(i,\sqrt T)\).
The pointed q_b refinement preserves its rigid Gaussian
ray and therefore preserves this sign. Hence the two b
signs are both −, and the two rigid c signs are both +,
giving (1) equal to + as claimed.

Changing the q_c residue by the norm-one
\((5+i)/(5-i)\) at 2399 has the already verified value
− in the quartic inertia and changes none of the
remaining selection conditions. In that branch (1) is
therefore exactly −. This is now an explicit choice of
ray branch, not just existence of some unspecified
nonzero Cassels pairing. A rational point on either
three-factor cover would give the exact rational Kummer
mark A on this quotient, which is impossible in this
branch. The rigid branch clears only the indicated
supported obstruction.
