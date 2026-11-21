# The alternate 107-lift has a full fixed-character crossed row

Keep exactly the [actual source retuned at 107](../../../rc-native-helper-20261120/ct-original-constant15-nonnorm-retune-107-r1/EXACT-ACTUAL-NONNORM-RETUNE-AT-107.md),
its \(c,\delta=1-\beta c^2,\theta=[\delta],d=\beta\theta\), and
\(K=1+2448\beta\) equal to its complete odd denominator
squareclass. Use the models and norm constants of
[the alternate-lift sign calculation](../constant15-retuned-107-alternate-lift-cross-r1/ACTUAL-RETUNED-107-ALTERNATE-LIFT-FISHER-SIGN.md),
SHA-256 fb1f231d7f6c051de0a9ccac0753f84a54f83db457b13e9544e0653379f92019.
In particular \(e=2952271997968816765\) and
\(a^2-\beta b^2=e z^2\) with the fixed exact \(a,b,z\).
Suppose the alternate full lift \((\theta,\theta e,e)\) is
locally admissible, namely that \(5e\) is square at every as-yet
unlisted \(\theta\)-prime. The retained visible conditions and
the exact 107 condition already hold.

We prove for **every** opposite test \(f\) in the actual
\(\psi\)-Selmer group:
\[
 \boxed{\displaystyle
 \Theta_2(\theta,f)=
       \left(\frac{K}{|f|}\right)
       \prod_{p\mid\theta}\left(\frac{10}{p}\right)^{v_p(f)}.}
 \tag{1}
\]
Here \(f\) is the signed squarefree scalar representative
(with no 2 or 3 factor by the known local table). In particular
no separate oriented Artin evaluation at an unlisted prime is
needed for this alternate crossed row. The entrywise signs
still use the true support, and the alternate lift is not now
proved admissible on the entire actual support.

## 1. Two exact square identities on the theta rows

Use the same tangents
\[
 L_1=aX-ezY-\beta bT,\qquad
 L_2=(a+\beta cb)X-9\beta(b+ca)T-e\delta zZ
\]
on \(X^2-eY^2=\beta T^2,\ X^2-81\beta T^2=e\delta Z^2\).
By the preceding proof \(L_1L_2/T^2\) is the \(T_0\)
pushout function. At any \(p\mid\theta\) take \(s=\sqrt\beta\)
with \(sc\equiv-1\bmod p\), and put \(t=sc,\ u=sb\).
In particular \(1-t\) has local squareclass 2.
Here \(p\nmid 2\cdot3\cdot5\cdot\beta\), and all assertions
about products below are in \(\mathbf Q_p\) before reduction.

If \(p\nmid e\), alternate admission gives \(k^2=5e\) for
some \(k\in\mathbf Q_p\). Take \(T=1,X=9s,Z=0,Y=4sk/e\).
Then
\[
 L_1=s(9a-u-4zk),\qquad L_2=9s(1-t)(a-u).
\]
The exact identity
\[
       (10(a-u)-4zk)^2=20(a-u)(9a-u-4zk)
\]
follows by substituting \(k^2=5e\) and \(ez^2=a^2-u^2\).
Thus \(L_1L_2\) has class \(9\beta(1-t)/20\), namely 10.
If the square factor is zero for one sign of \(k\), use the
other sign. This identity does not divide by the residue of
\(a-u\); it works also at a prime of the fixed \(z\).

If \(p\mid e\), it is one of the retained \(131,6551,2470991\)
in \(\theta\). The old local class of \(e\) is \(-d\) and
\((5/p)=+1\), so \(j^2=-5/(e\delta)\) is soluble.
Use \(T=1,X=s,Y=0,Z=4sj\). Let
\(\ell=(1-t)(a-u),\ m=(1+t)(a+u),\ \rho=z/j\).
We have \(\ell m=-5\rho^2\) and
\[
 L_1=s(a-u),\qquad
 L_2=s(5\ell-4m+20\rho),\qquad
 (5\ell+10\rho)^2=5\ell(5\ell-4m+20\rho).
\]
As \(\ell\ne0\), the product has class \(\beta/(5(1-t))\),
again 10. One of the signs of \(j\) gives a nonzero square
factor. The exact calculation also works when \(a-u\)
has positive depth, not just the unit case. The replay checks
the two actual vanishing-residue orientations at 131 and
2470991, as well as the unit orientation at 6551. Since the
class 10 is a unit at \(p\), the local symbol is
\((10/p)^{v_p(f)}\) in both branches.

## 2. All other local factors

At any \(\beta\)-prime the previous two recipes give a
square tangent product: if \(e\) is ramified, use the simultaneous
depth-one stripped values in ratio 9, and if \(e\) is a square
unit, use two equal nonzero residues. Those recipes apply to
every \(\beta\)-prime because the retained old \(\psi\)-conditions
for \(e\) hold there and the fixed \(z\) is prime to \(\beta\).
This is independent of the test \(f\). At 3 the scalar
\(\psi\)-image is trivial. At infinity use
\(X=1,T=0,Y=-1/\sqrt e,Z=-1/\sqrt{e\delta}\) to get two
positive tangents, even when \(f<0\).

At 2 use \(X=1,T=2\) as before. Since \(v_2(c)=2\), we have
\(\delta\equiv1\bmod16\), and the two odd square arguments of
\(Y,Z\) agree modulo 16 (the difference in the numerators is
\(320\beta\)). Choose their signs so that \(Y\equiv Z\bmod8\);
choose the common sign to make \(L_1\) have depth one. The
difference
\[
 L_2-L_1=\beta cb-16\beta b-18\beta ca+ez(Y-\delta Z)
\]
is zero modulo 8. Thus \(L_2\) has depth one and
\(L_1L_2/4\equiv1\bmod4\). This gives a trivial Hilbert symbol
against **any** odd test representative. The exact two possible
\(c\bmod16\) checks give \(L_1\equiv L_2\equiv6\bmod8\) for
the chosen common sign.

At all remaining odd places \(f\) is a unit. The good-conic
normalization from the preceding proof applies for this unit
test without any restriction on \(f\) beyond admissibility:
even depths strip away, except for exactly one factor of the
local pole depth of \(c\) in the \(L_2\) tangent. Hence the
product is \(\prod_{p\mid K}(f/p)=(K/|f|)\), because the
retune proved \(K\equiv1\bmod4\) is the full odd denominator
squareclass. This proves (1).

## 3. Full row-space interpretation

Use the exact actual matrix
\(A=M+(t_{\rm char}+r)r^{\mathsf T}\) of the
[transposed scalar Selmer calculation](../../../rc-native-helper-20261120/ct-original-constant15-transpose-selmer-r1/EXACT-TRANSPOSE-SELMER-ON-CONSTANT15.md),
where \(M\) is the true Legendre Laplacian, the
\(\psi\) masks are \(\ker A^{\mathsf T}\), and a mask's
entries are its prime valuations. In additive bits this
alternate cross row is the column vector
\[
          w_p=[K/p]+1_{p\mid\theta}[10/p].
\]
It annihilates the actual opposite tests iff \(w\in\operatorname{im} A\).
When this fails, the admitted alternate lift proves the mark is
not rational on this receiver. This does not certify another
receiver or any rational point.

Equivalently the first mark functional is represented by the vector
\(v_p=1_{p\mid\theta}[5/p]\); the alternate local lift admission
is precisely the equality \(A^{\mathsf T}a_e=v\) for the fixed
valuation mask \(a_e\) of \(e\). Indeed on retained rows the
difference already vanishes, and at each remaining \(\theta\)
prime \(e\) is a unit whose bit must match \(5\). This explains why
a true alternate lift provides the required vanishing of the
first test, without requiring \(e\) itself to be a global
\(\psi\)-Selmer element (it is not at 107).

For the admitted \(f=65029284442765\) of the previous paper,
\((10/p)=+1\) at both its \(\theta\)-primes \(6551,107\),
and \((K/f)=-1\), so (1) recovers exactly the previously
computed negative gate. The admission of this precise \(f\)
and the complete \(\theta\)-support remain conditional.

    python3 -B check_retuned_alternate_local_squareclasses.py | cmp - EXACT-ALTERNATE-LOCAL-SQUARECLASSES.json
    sha256sum -c SHA256SUMS
