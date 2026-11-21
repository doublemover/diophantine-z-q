# Ordinary genus characters cannot see the marked relative ideal class

For either original balanced selected twist, a specific class of order two in the relative CM sign problem is itself a square in the class group. This is forced by the literal local Kummer mark, not by a surrogate class-group statistic. On the first arm, where the actual sign can only be one of two classes, **every quadratic unramified Artin character identifies the two**. An uncomputed higher-order class character or exact class relation is still needed. No selected rank, sign, point or actual class group is computed here.

## 1. The fixed real quartic has class number one

Put \(F=\mathbf Q(\sqrt3,\sqrt{17})\), \(r=\sqrt3\), \(w=(1+\sqrt{17})/2\). Its integral basis is \(1,r,w,rw\) since the quadratic discriminants 12 and 17 are coprime, and the absolute discriminant is \(12\cdot17\cdot204=41616\). The degree-four totally real Minkowski bound is
\[
 \frac{4!}{4^4}\sqrt{41616}=\frac{153}{8}.
\]
The only prime ideal norms at most this bound are 2, 9, 13: at 2 there are two ramified degree-one primes, at 3 one ramified degree-two prime, and at 13 complete splitting. The other possible odd underlying rational primes \(5,7,11,17,19\) have residue degree two. Exact elements of absolute norm 2, 9 and 13 are respectively
\[
 -1+r(w-2),\qquad r,\qquad -2-2w+r(-1+2w).
\]
For example the first and third have quadratic norm from \(F\) to \(\mathbf Q(\sqrt{17})\) equal to \(-23+9w,\ -31+12w\), then absolute norm \(-2,\ 13\). The conjugates generate all primes above the corresponding rational prime. Thus every ideal class of \(F\) is trivial.

A finite presentation of all candidate quadratic characters below can use the unit generators
\[
 -1,\quad 2+r,\quad 4+\sqrt{17},\quad
 \epsilon_*=(1+r)(7+\sqrt{51})/2=2+3r+3w+rw.
\]
In fact the quadratic fundamental units are \(2+\sqrt3,\ 4+\sqrt{17},\ 50+7\sqrt{51}\). For the first and third norm \(-1\) is excluded modulo 3 and the displayed Pell solutions are the first by the positive radical coefficient; for the second check \((a+b\sqrt{17})/2,\ b=1,2\) (the first has no solution and \(b=2\) gives \(4+\sqrt{17}\)). For any quartic unit the square is a product of units in the three quadratic subfields, by multiplying its three quadratic norms and dividing by its absolute norm. The representatives among those products modulo their squares must be totally positive to be squares. Odd powers of \(4+\sqrt{17}\) have mixed signs, while the other two quadratic units are totally positive, so the only candidates are the four products of the latter two. The individual square roots require \(\sqrt2\notin F\), since they are \((1+\sqrt3)\sqrt2/2\) and \((7+\sqrt{51})\sqrt2/2\). Their product has square root \(\epsilon_*\) in \(F\). This gives the claimed unit group; the norm and multiplication statements have a small exact replay.

## 2. All quadratic unramified characters descend to this quartic

For either balanced \(n\), put \(D=-n\), \(L=F(\sqrt D)\), and \(c\) the CM conjugation. As in the relative-class criterion, the finite ramified primes of \(L/F\) are precisely those above \(p\mid n,\ p\ne17\). At \(2,3\) the rational \(K=\mathbf Q(\sqrt D)\) is split, and at \(17\) the field \(F\) contains both \(\sqrt{17}\) and an unramified quadratic extension, so \(D/17\) is a square there. Elsewhere the relative ramification follows directly from the squarefree \(D\).

Every quadratic unramified ideal-class character of \(L\) comes from an auxiliary quadratic \(F(\sqrt t)/F\) by base change. Indeed \(c\) acts by inversion on \(\mathrm{Cl}(L)\): an ideal times its conjugate extends the norm ideal of \(F\), and that is principal. Thus the kernel of any quadratic ideal-class character is invariant under \(c\). The corresponding unramified quadratic extension of \(L\) is Galois over \(F\), of degree four. Ordinary complex conjugation in a chosen complex embedding has order two and restricts nontrivially to \(L\), ruling out cyclic order four over \(F\); the degree-four group is biquadratic. It is therefore \(L(\sqrt t)\) for \(t\in F^\times\). This uses ordinary [ideal-class Artin reciprocity](https://www.math.utoronto.ca/~ila/Cox-Primes_of_the_form_x2%2Bny2.pdf), not a hypothesis of trivial class group of \(L\).

The element \(t\) has even valuation outside the relative ramified primes of \(F\): an odd valuation would give a ramified quadratic extension which remains ramified after an unramified base change. Conversely, away from 2, on any relative ramified place of \(F\) multiplying \(t\) by the corresponding power of \(D\) removes its valuation without changing its class in \(L\), so the remaining unit represents an unramified or trivial quadratic class. This yields a complete finite squareclass panel: take products of the four displayed fundamental unit squareclasses and generators of the primes of \(F\) above \(p\mid n,\ p\ne17\), with binary exponents. At each place over 2 require the product to lie in the squareclass of 1 or 5, the latter generating the unramified quadratic line. At 2 the two local fields of \(F\) are each \(\mathbf Q_2(\sqrt3)\), and the unit test is finite modulo \((1+\sqrt3)^5\): existence of a unit square root modulo that power implies a square by Hensel, since \(v_{1+\sqrt3}(2)=2\). No extra real condition is needed since \(L\) has no real places. For a relative ramified \(\mathfrak P\) of \(L\) above \(\wp\) in \(F\), the resulting character is the residue quadratic symbol of \(t D^{-\operatorname{ord}_\wp(t)}\), a local unit. These steps are a complete criterion for *quadratic* characters; they do not assert their sufficiency for the mark.

## 3. The literal marked order-two class is always a square

Write \(\beta=17B_*\); each prime \(p\mid B_*\) is \(1\bmod408\) and is split completely in \(F\). Let
\[
 \mathfrak B=\prod_{p\mid B_*}\prod_{\mathfrak P\mid p}\mathfrak P
 \quad\text{as an ideal of }L.
\]
It satisfies \(\mathfrak B^2=B_*O_L\). Its ideal class is not principal. If \(\mathfrak B=(a)\), conjugation fixes the ideal, so \(a/\bar a\) is a norm-one global unit and equals \(+1\) or \(-1\). In the first case \(a\in F\), hence has even valuation at every relative ramified prime. In the second case \(a/\sqrt D\in F\), so it has odd valuation at every such prime, including those over the fresh \(q_0\). Both contradict the defining ideal exponents. Hence \([\mathfrak B]\) has order exactly two.

For an arbitrary quadratic unramified character \(\chi_t\) from §2, let \(A\) be the signed rational squarefree representative of \(N_{F/\mathbf Q}(t)\). Its odd support lies among the \(p\mid n,\ p\ne17\), and an odd bit can occur only at primes splitting completely in \(F\): outside \(2,3,17\) the two possible residue degrees of the biquadratic field are 1 and 2. At a genuine \(p\mid B_*\), multiplying the four residue symbols over \(\wp\mid p\) gives
\[
 \prod_{\mathfrak P\mid p}\chi_t(\mathfrak P)
 =
 \left(\frac{A/p^{s_p}}p\right)
 \left(\frac{D/p}p\right)^{s_p},
 \qquad s_p=v_p(A)\in\{0,1\}.
\]
This strips the common powers of \(p\) before reduction; rational square unit factors have no effect. Multiply over \(p\mid B_*\) and use reciprocity (all such \(p\) are \(1\bmod4\)). The cross factors inside \(B_*\) cancel, giving the exact identity
\[
 \chi_t(\mathfrak B)=
 \prod_{p\mid B_*}\left(\frac{-n/B_*}{p}\right)^{s_p}
 \prod_{\substack{\ell\mid n,\ \ell\nmid\beta}}
        \left(\frac{B_*}{\ell}\right)^{s_\ell}.\tag{1}
\]

Both products are one **because of the actual local Kummer mark**. At every odd \(p\mid n\), \(E_n(\mathbf Q_p)/2E_n(\mathbf Q_p)\) has order four (multiplication by two is invertible on the formal subgroup, and the cardinality of quotient by two on the finite remaining group equals its 2-kernel; equivalently apply the exact local Kummer image). The four rational torsion points already have distinct valuation pairs \((0,0),(1,1),(1,0),(0,1)\) and give all classes. At \(p\mid B_*\), the local mark \((\beta,1)\) has pair \((1,0)\), hence equals the torsion class \((n,1)\). Therefore \(n/\beta\) is a square unit at \(p\); since \(17\) and \(-1\) are squares there, \((-n/B_*)/p\) is \(+1\). At \(\ell\mid n,\ \ell\nmid\beta\), the mark has pair \((0,0)\), so \(\beta\) is a local square. If \(s_\ell=1\), \(\ell\) splits in \(F\) and \((17/\ell)=+1\), so \((B_*/\ell)=+1\) too. No extra assumption on the helper bits or the companion support is required. Equation (1) is thus always \(+1\). Since all quadratic ideal-class characters have been covered,
\[
 \boxed{[\mathfrak B]\ne1,\quad [\mathfrak B]^2=1,\quad
 [\mathfrak B]\in 2\,\mathrm{Cl}(L).}
\]

## 4. What this rules out for the first-arm phase

For the base arm \(u=1\) and no repair prime, every \(p\mid n,\ p\ne17\) splits in \(\mathbf Q(\sqrt{-3})\). All relative ramified primes therefore read the actual quarter Kummer phase by the no-collision proof, not just \(q_0,p_\beta\). The pattern of first valuation parities is a constant from the torsion correction plus the literal mark indicator on primes of \(B_*\). By the class-relation criterion, and because the total relative ramified product is principal (the \(\sqrt D\) divisor, up to extension of a principal \(F\)-ideal), the anti-ideal representative \(\mathfrak b\) has exactly these possibilities:
\[
 [\mathfrak b]=1\quad\text{if the mark coefficient is 0},\qquad
 [\mathfrak b]=[\mathfrak B]\quad\text{if it is 1}.
\]
Both are invisible to all quadratic unramified Artin characters. This blocks the quadratic-character compression, **even if the full mod-two intersection data for it were computed perfectly**. To distinguish the cases by Artin evaluations needs a character of order at least four with a nontrivial value on the marked class, or a direct class relation. An order-four character is sufficient if it exists with that value, but is not guaranteed: the marked class might lie deeper than \(2\mathrm{Cl}(L)\). On a companion with additional collisions the same marked class is invisible to quadratic characters, although the two-case description can need the remaining ramified comparison corrections.

### Exact dependencies and replay

Use the same actual selector/mark as the independently reviewed balanced eights, paper **4b2d39bf6b4f5e9dda8e33482c723dfba02569f8a0e285c005c646aa35d5fe6e**. The relative class receiver is *The next marked sign from a relative ideal-class relation*, paper **7500994322c7257e29c58aa2411f77e23276a49871c4cd7ae1c893db73c45e4d**. This note does not attach a new claim to their immutable bytes.

    python3 -B replay_cm192_fixed_real_quartic.py | cmp - EXACT-CM192-FIXED-REAL-QUARTIC.json
    sha256sum -c SHA256SUMS
