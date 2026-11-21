# The ordinary edge bit is a fixed Artin–Schreier test killed by pure Hecke trace

This concerns the original **ordinary characteristic-two** edge moment on a genuine CM genus slice, not the different supersingular order-three receiver or helper-673 parity. It reformulates the already known cubic edge coefficient as a fixed elliptic Artin–Schreier cover. Every individual prime-to-6 pure Hecke **trace** kills its class. Keeping a marked kernel instead of tracing all kernels does not kill the pulled-back class. Nothing below supplies the required primitive degree-one edge coefficient for a literal detector.

## 1. Exact elliptic descent of the existing unordered-edge input

Write $t=t_3$ on the tame level-three chart modulo two and $u=(t+1)^{-1}$. At the actual endpoints of an edge let $a_s,a_t$ be the reciprocal $j$ invariants. With the exact normalizations,
$$
 a_s=u^4+u^3+u^2+u,\qquad a_t=u^4+u^3,
 \qquad c=a_s+a_t=u^2+u,
 \qquad a_s a_t=c^4.
$$
The last two formulas are symmetric under replacing the 3-ideal by its inverse. They follow from the level-three modular formulas (or the explicit $j_s,j_t$ in the preceding logarithm computation). Define $\wp(h)=h^2+h$. The degree-nine logarithm class is $g_9=u^9+u^3$ with $g_9\equiv c^5\bmod\wp$. On the actual complete indexed horizontal edge multiset of one Frobenius-stable genus slice preserved by the selected horizontal 3-ideal class,
$$
  c^5+c^3=a_s^3+a_t^3 .
$$
Each indexed vertex occurs twice in this symmetric endpoint sum; this uses the permutation by the chosen fixed 3-ideal and does not replace the orbit by distinct geometric labels. Therefore the total of the $c^5$ values equals the total of $c^3$. Also $\sum c=0$ on that exact edge multiset, so the total is $e_3$ of its unordered-edge polynomial. This last equality is the existing unmarked cubic receiver, not a new arithmetic evaluation.

The new cover description is
$$
  z^2+z=u^5+u,\qquad
  (u,z)\longmapsto(u+1,z+c),
$$
where the base involution is the literal $w_3$ (reverse the edge). Indeed the change in the right side is $\wp(c)$. The invariants $c$ and $W=z+uc$ satisfy
$$
      W^2+W=c^3+c.
$$
The other lift of edge reversal, followed by the deck involution $z\mapsto z+1$, instead gives the compatible quotient $W'^2+W'=c^3$. These are fixed supersingular elliptic curves in characteristic two (the respective counts over $\mathbf F_2$ are 5 and 3, with supersingular traces $-2,0$). On any actual edge $\operatorname{Tr}(c)=0$ since $c=u^2+u$, so either quotient gives the same phase. There is no orientation, cube-root branch, or new multiplicity convention. The first usual projective Igusa quadratic class pulls back to $a_s\equiv u^3+u\bmod\wp$, with odd pole order 3, whereas the new class has order 5 at the same supersingular puncture; the two are distinct.

## 2. Exact Hecke cancellation on the Artin–Schreier class

Let $\ell\nmid6$ be a prime and $T_\ell$ be pullback then field trace along the ordinary $\ell$-isogeny correspondence on the **tame** curve. An additive trace transports Artin–Schreier coboundaries into coboundaries. Write $g_5=u^5+u$. Then
$$
       T_\ell(g_9)\equiv T_\ell(g_5)\equiv0\pmod{\wp(\mathbf F_2(t))}.
$$

For the first assertion take an arbitrary ordinary closed point, possibly over a larger finite field $k$, with its cyclic 3-subgroup. Its ordinary elliptic curve and flag have the canonical lift to $W(k)$; use that lift and its connected cyclic 16-subgroup. The same exact local rational identity of the published dyadic logarithm calculation holds:
$$
 L=B_0(F_2(t))-B_0(t)+8g_9\pmod{16}.
$$
It is an identity on the ordinary connected-16 branch, proved in the corresponding localized Laurent ring without ideal-class assumptions. On the canonical lift the connected 2-quotient is the arithmetic Frobenius lift. Every prime-to-two isogeny preserves canonical lifts and carries their connected-16 flags to the connected flags, including all $\ell+1$ quotient kernels over the unramified residue extension on which they are defined.

Summing through a full Frobenius orbit of the source cancels the displayed coboundary. The same holds after applying the entire $\ell$ correspondence: the whole indexed multiset is stable under Frobenius, including all conjugate kernel flags. The map $\phi:X_0(48)\to E_0$ is normalized at infinity. As a map through the Jacobian it is a $T_\ell$ eigenmap with eigenvalue $a_\ell(E_0)$; the cuspidal translation vanishes since the Hecke correspondence sends $\infty$ to $(\ell+1)\infty$. Thus the additive elliptic logarithm of the entire Hecke orbit sum is $a_\ell(E_0)$ times that of the starting orbit sum. The latter is divisible by eight, and $a_\ell(E_0)$ is even (good odd prime and full rational 2-torsion). Reducing modulo 16 gives
$$
       \operatorname{Tr}_{k/\mathbf F_2}((T_\ell g_9)(t))=0 .
$$
This holds for **each ordinary closed point**, not just a chosen CM family. Passing the $g_9$ coefficient from the complete multiset to the displayed field trace is exactly the corestriction on the correspondence, including each isogeny with its geometric multiplicity.

For clarity such universal test values imply triviality over $\mathbf F_2$, not only over its algebraic closure. Otherwise the curve of the Artin–Schreier extension either is geometrically connected, in contradiction to the Weil bound (it would have two rational points over every ordinary rational point in every finite extension), or is the nontrivial constant quadratic extension, which has no rational point over any odd-degree finite extension. The base has ordinary points over arbitrarily large such extensions. Excluding the finite set of poles and cusps does not affect either argument.

For the second assertion,
$$
       g_9+g_5\equiv a_s^3+a_t^3\pmod\wp
$$
by the exact formulas of §1 ($g_5+c^3=\wp(u^3+u^2+u)$). The two degeneracy embeddings of the $j$-line commute with $T_\ell$ for $\ell\ne3$. On that line put $a=1/j$. One has the rational function identity in characteristic two
$$
     T_\ell(a^3)=[\ell\equiv3\bmod8]a .
$$
Here is a short exact arithmetic proof. At the cusp $a=\Delta(q)$ modulo 2, since $E_4\equiv1\bmod2$. Jacobi's product identity, taking eighth powers in characteristic two, gives $\Delta(q)=\sum_{x>0,\ {\mathrm{odd}}}q^{x^2}$. Hence the coefficient $A(m)$ of $a^3$ is the parity of the positive odd solutions $x^2+2y^2=m$. The weight-zero correspondence has at the cusp the exact coefficients $A(\ell m)+A(m/\ell)$ (the second term is zero when undefined); the factors from the sum of $\ell$ branches reduce to 1 modulo two.

If $\ell$ is inert in $\mathbf Q(\sqrt{-2})$, both coordinates are divisible by $\ell$ when $\ell$ divides a represented norm, giving cancellation. If $\ell$ splits, the order $\mathbf Z[\sqrt{-2}]$ has class number one by the imaginary quadratic Minkowski bound (the bound is below 2). Let $r(m)$ count elements of odd norm $m$ up to the two units $\{\pm1\}$. The two norm-$\ell$ ideals and their overlap give
$$
 r(\ell m)=2r(m)-r(m/\ell).
$$
Only $\ell m\equiv3\bmod8$ can contribute to the coefficients under discussion. There both $r(\ell m)$ and $r(m/\ell)$ are exactly twice their positive-odd representation counts. Thus their normalized parity combination is $r(m)\bmod2$. If $\ell\equiv1\bmod8$ then $m\equiv3\bmod8$ and the conjugate pairs show $r(m)$ even. If $\ell\equiv3\bmod8$ then $m\equiv1\bmod8$ and $r(m)$ is odd exactly when $m$ is an odd square, because the only conjugation-fixed class has $y=0$ (the first coordinate is odd). This proves the q-series identity, hence the rational identity on the $j$-line. The pullback difference for the two endpoints is a multiple of $a_s+a_t=c=\wp(u)$. Together with the $g_9$ identity this proves the generation-independent vanishing of $T_\ell g_5$.

## 3. What cancellation does and does not remove

On the moduli space which **retains** a chosen cyclic $\ell$-kernel the pullback of $g_5$ along the quotient map is still nontrivial in Artin–Schreier cohomology. Indeed the map has tame odd ramification at the supersingular tame level-three point. The prime-to-two subgroup correspondence is étale on the moduli stack; the effective stabilizer of the level-three supersingular flag has order 3 (the automorphisms of supersingular $j=0$ act transitively on the four 3-lines, and modulo the central negation have order 12). The ramification indices for the coarse map therefore divide 3. The valuation of the pulled-back pole has odd absolute value $5e$ at any point above the puncture. A characteristic-two coboundary $h^2+h$ can have only even pole order, so the class is nontrivial. This gives an exact **marked-kernel** escape from literal Hecke averaging, not a proof that such a partial sum on the actual CM fields is computable or nonzero. The same odd-degree reasoning applies to any additionally chosen tame refinement with odd ramification at this puncture.

For the arithmetic interpretation, take a true Frobenius-stable CM genus slice of conductor prime to $6\ell$ in a CM field unramified at $\ell$, and pull it back to the next conductor-$\ell$ layer through the exact descending $\ell$-isogenies. If $\ell$ is inert all kernels descend. If split, the two horizontal branches act by inverse ideal classes; on a quadratic genus slice they land in the same translated slice with multiplicity, so their two whole sums cancel in characteristic two, even if the chosen slice is not fixed by that ideal. Thus the **complete** descending pullback vanishes as well. This statement varies an order conductor, not the fundamental discriminant of a detector. The authenticated primitive edge coefficient of the actual fundamental $D=-17dq_*$ remains missing. No rank, nonzero point, or generic obstruction to other ordinary or odd-phase constructions follows.

### Exact inputs and controls

- [Colò, Appendix A](https://www.leonardocolo.com/documents/thesis/PhD_Thesis.pdf) and the checked ordinary edge logarithm identity, *One binary ordinary CM edge moment suffices for a selected detector arm*.
- [Maier, Tables 2 and 4](https://citeseerx.ist.psu.edu/document?doi=8f2883aec71214ea669a643e933e1b26c594fac5&repid=rep1&type=pdf) for the exact tame $t_3$ q-expansion and involution.
- Existing unordered cubic coefficient proof, *Unmarked ordinary genus-slice resultant*, SHA-256 `0656594a6840c53e5f1da36b92c14a9619969d47d3b538f46e33532ff0ecb3e3`. The elliptic quotient and pure Hecke Artin–Schreier obstruction above are the new statements.

The independent small script expands the exact tame eta series, forms the $q$-series traces and recognizes the degree-$\le5$ polynomials for nine primes. For this finite check the degree bound follows because both coarse-map ramification indices at a corresponding supersingular flag are the same (source and target have effective stabilizer of order three with one common stabilizer at the intermediate flag). Hence taking the trace introduces at most a pole of order five at the one supersingular base puncture. The finite table is not used in the uniform proof or as a CM-occurrence calculation.

```sh
python3 check_ordinary_as_cover.py | cmp - EXACT-ORDINARY-AS-EDGE.json
sha256sum -c SHA256SUMS
```
