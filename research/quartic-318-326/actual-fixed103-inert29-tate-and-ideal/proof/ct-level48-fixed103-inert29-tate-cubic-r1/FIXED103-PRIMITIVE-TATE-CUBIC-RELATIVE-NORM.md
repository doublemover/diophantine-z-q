# The primitive order-nine test as one relative CM cubic residue

At the actual protected good inert place 29, the maximal-order part of the signed level-48 phase is one cubic residue of a relative CM norm. This is an exact alternative input to the primitive detector, not a computation of that norm for a selected original conductor. In particular a cube leaves open an order-three phase, and it is not a rank obstruction.

## 1. A single fixed unit on every supersingular flag

On $E_0:y^2=x(x+1)(x-3)$ over $\mathbf F_{29}$ set
$$
 T_0=(0,0),\quad H=(23,7),\quad f=y-3x+4.
$$
The point $H$ has order three and the tangent there has slope three, so $\operatorname{div}(f)=3(H)-3(O)$. The regular value at $T_0$ is $4$. For any nonexceptional $A=(x,y)$ on $E_0$ the usual rational two-torsion translation gives
$$
       u(A):=f(A+T_0)=\frac{4x^2+9x+3y}{x^2}.
$$
The exact full fixed-chart replay verifies that $\phi(Q)$ is finite with $x\ne0$ and that $u(\phi(Q))$ is nonzero for **every** one of the 224 supersingular ordered level-48 flags over $\mathbf F_{29^2}$. The 112 distinct image points are not indexed CM multiplicities. In particular the same shift works for every genuine reduced CM term, at arbitrary eligible conductor.

Use the reduced Frey--Rück pairing on the divisor $(A+T_0)-(T_0)$ and the torsion divisor $(H)-(O)$. In the convention with exponent $(29^2-1)/3=280$, this is the homomorphism
$$
       e(A)=\bigl(f(A+T_0)/4\bigr)^{280}\in\mu_3 .
$$
See [Bruin, *The Tate pairing for Abelian varieties over finite fields*, Theorem 4.1](https://pub.math.leidenuniv.nl/~bruinpj/tate-pairing.pdf), which identifies the divisor evaluation with the perfect reduced Tate pairing. Since $4\in\mathbf F_{29}^\times$ is a cube even in that field, it does not affect the cubic value. For $G=(14,13\sqrt2)$ of order nine, direct evaluation gives $e(G)=\gamma=14+5\sqrt2$, a primitive cube root of unity. The precise comparison with the previous phase is
$$
 [4](1-F_{29})A=kG \quad\Longrightarrow\quad
        u(A)^{560}=\gamma^{k\bmod3}.
$$
Indeed $H,T_0,f$ are rational over $\mathbf F_{29}$. Hence $e(F_{29}A)=e(A)^{29}=e(A)^{-1}$, and $e([4](1-F_{29})A)=e(A)^8=e(A)^2$. The replay checks the same exact exponent on all 224 actual chart flags, not just abstract groups.

## 2. The signed norm, with its orientation

For the first-arm fixed field $K_0=\mathbf Q(\sqrt{-1751})$, chosen conductor $c$ and primitive genus $\chi_c$, put $L=K_0(\sqrt c)\subset H_c$, with $H_c$ the genuine ring class field. Let $P$ be its actual oriented CM point of conductor $c$. Take the literal rational function
$$
        U_Q=(4x(\phi(Q))^2+9x(\phi(Q))+3y(\phi(Q)))/x(\phi(Q))^2
$$
on the level-48 curve over $\mathbf Q$. The finite chart check shows its values at the actual ring-indexed points are units at the chosen 29-place. Define
$$
        V=N_{H_c/L}\bigl(U_P\bigr),\qquad R=V/\sigma(V)
$$
for the nontrivial $\sigma\in\operatorname{Gal}(L/K_0)$. Both base field and conductor satisfy the protected 29 assumptions, so the named reduction place has residue field $\mathbf F_{29^2}$. The two cosets of $\ker\chi_c$ give the exact product
$$
        \overline R=\prod_{a\in\operatorname{Gal}(H_c/K_0)}
                      u(\phi(\overline{aP}))^{\chi_c(a)} .
$$
Each factor is counted by its genuine CM index, including collisions; the choice of opposite coset orientation only inverts the result. Write $k$ for the full previous signed phase exponent modulo nine. Then
$$
              \overline R^{560}=\gamma^{k\bmod3}.
$$
Thus $\overline R$ noncube is **equivalent to exact order nine** in the signed readout. It is a sufficient rational witness for the corresponding marked side under the already selected local Selmer/torsion hypotheses, but the value of $R$ for a selected original conductor is not supplied. The same proof applies to the proposed moving base $K'=\mathbf Q(\sqrt{-n/241})$ and fixed primitive conductor 241 when its protected local conditions hold: use $L=K'(\sqrt{241})$, not the fixed reference's $K_0(\sqrt{241})$. A change of base does not compute that moving norm.

For the independently computed fixed reference $K_0$, $c=241$ only, the full signed exponent sum is $-86\equiv4\bmod9$, so the cubic value is $\gamma$ in the coherent reference orientation. The fixed reference is not a value for $K'$, or for the original moving $c$.

## 3. What a genuine aggregation theorem must retain

One tempting compression is to replace the scalar cubic character by a sum of arbitrary functions on the two genus-zero parameters $t_{16}$ before and after quotient by the 3-line. It does not work even with completely free functions on their 56+56 possible reduced values. Encode $a+b\sqrt2$ by $a+29b$. The replay gives six exact edges in cyclic order with respective cubic exponents
$$
 (122,132;0),\ (741,132;2),\ (741,731;0),\
 (558,731;1),\ (558,297;0),\ (122,297;1).
$$
Their alternating sum is $2\bmod3$. Any sum of two unary functions has alternating sum zero. This is an exact fixed-chart obstruction; it neither establishes impossibility for other joint-level functions nor rules out a different identity after summing over all genuine CM points.

The obvious characteristic-zero lift of the tangent is not a modular unit or a two-CM intersection. For any nonzero characteristic-zero $3$-torsion point $\widetilde H$ the abscissa satisfies $3x^4-8x^3-18x^2-9=0$; the quartic is irreducible modulo five. At a 3-adic embedding where $v_3(x(\widetilde H))=-1$ (the final Newton slope), put $A=\widetilde H-T_0$. Then $v_3(x(A))=2$, $v_3(y(A))=3/2$ and $s=y(A)/x(A)$ has depth $-1/2$. The two points above $A$ satisfy $X-X^{-1}=s$, so their $X$ depths are $\pm1/2$. The exact formula
$$
  t_{16}=X-2+3/(x(A)X)=-2+x(A)/X-X^{-3}
$$
follows by squaring $s$. On the small-$X$ sheet $v_3(t_{16})=-3/2$; on the large sheet $v_3(t_{16}+2)=3/2$ with $t_{16}$ a unit. In both cases $t_8=t_{16}^2/(t_{16}+2)$ has depth $-3/2$, hence $t_4,t_2,j$ all have depth $-3/2$ by the literal downward formulas. Every abscissa is conjugate to the tested one; the two signs of $y$ give the same valuation. Thus none of these genuine horizontal tangent zeros is CM, since CM $j$ is an algebraic integer. This concerns the genuine $3$-torsion tangent lift, not every possible other function with the same reduction on the finite chart. It does not assert that no such other function could be found.

There is also no compact unramified cyclic cubic **congruence** cover of $X_0(48)$ in characteristic zero giving the evident geometric cover. Here $z^3=u(\phi(Q))$ is a geometrically connected étale Kummer cover in characteristic 29: the divisor is three times the pullback of the nontrivial class $H$; the degree-two map $\phi$ injects its order-three class by norm. In characteristic zero an unramified cyclic congruence character must kill the upper cusp translation $\left(\begin{smallmatrix}1&1\\0&1\end{smallmatrix}\right)$ and the opposite lower one $\left(\begin{smallmatrix}1&0\\48&1\end{smallmatrix}\right)$. On every congruence completion its kernel therefore contains all upper and allowed lower local unipotents. At primes not dividing 48 these generate the full local factor. At a prime dividing 48 Gauss decomposition also puts every diagonal with first entry $1$ modulo the relevant local part of 48 in the kernel, since such a unit is $1+xy$ with $x=1$ and $y$ an allowed lower parameter. The remaining diagonal unit quotient at $2,3$ is a 2-group. Therefore no such degree-three character exists. This does not classify arbitrary characteristic-29 auxiliary-level covers.

A sufficient genuinely new arithmetic theorem would compute the **unit residue at the named 29-place of the oriented ratio of half-norms** $R$ (or its cubic class), keeping the ordered full level-48 flag and the two genus cosets. An ordinary absolute CM norm, valuation-only intersection formula, or unoriented class polynomial does not provide this. For example, [Schofer, *Borcherds Forms and Generalizations of Singular Moduli*, Corollary 3.5](https://arxiv.org/abs/math/0603714) computes absolute logarithmic CM averages for Borcherds divisors, not either of these selected unit residues; the obvious lift here also lacks the required horizontal CM support. A substitute level-48 function with the same cubic residues and a computable **relative** norm, or an equivariant finite-field CM resultant/trace theorem on this exact joint-level function, would suffice. Neither is asserted.

### Replay

The script uses the exact prior inert-29 finite chart evaluator and fixed conductor-241 numerical donor, both hash-pinned. It recomputes all 224 fixed labels, the six-edge residue, the degree-four irreducibility check and the exact fixed numerical calibration. It counts no moving ring class orbit.

```sh
python3 check_inert29_tate_cubic.py | cmp - EXACT-INERT29-TATE-CUBIC.json
sha256sum -c SHA256SUMS
```
