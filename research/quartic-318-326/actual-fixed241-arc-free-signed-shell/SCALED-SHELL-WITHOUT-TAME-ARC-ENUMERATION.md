# The same scaled shell removes both freely variable tame quotient steps

The forced-last-241 calculation can also absorb the degree-5/7 Hecke step in the actual real CM calibration. Neither the 5/7 nor the 241 quotient curves, characteristic-zero fields, target local orders or separate kernel scans are needed. The valid multiplicities, ordered 16/3 flags and absolute genus sign are still exact. This works at the real calibration's good contributing primes and adds no new source congruence. It does not compute any moving oriented exponent.

## 1. Leave only the chosen Atkin transform on the fixed seed

A noncuspidal divisor occurrence in the real calibration is one of:

- a fixed seed's diagonal, with multiplicity two for $\mathcal G$;
- its actual degree-$r$ Hecke correspondence, with $r=5$ for $\mathcal G$ or $r=7$ for $\mathcal H$.

It also carries its literal Atkin transformation $A\in\{1,w_{16},w_3,w_{48}\}$ and sign. Since $r$ is prime to 48, moving this $A$ before $T_r$ gives an exact path bijection, not just a equality of unsigned $j$-counts: quotienting by the cyclic primary factors of relatively prime degrees commutes, as does their prime-to-degree torsion transport. The same is true with the subsequent degree $f=241$. So first form only the named *Atkin* $A$ on the fixed seed; call this exact prepath marked curve $B$ and its degree from the seed $k_A\in\{1,16,3,48\}$. After it the two freely variable prime degrees are $r$ (absent on the diagonal) and $f$.

Use the previous exact geometric saturation only on the seed and its local Tate-lattice transport to $B$, with no other quotients. The source CM order of this curve has conductor 4 or 12: in the actual chosen flag library the endpoint 2-depths are both 2, and the actual source/target 3-depths are 0 or 1. The known primary Atkin flags read which one. No conductor attached to the full flag is substituted for this source endomorphism order. Let $U$ be the named auxiliary pure radical in the seed quaternion algebra, of square $D_A\in\{-320,-2880\}$.

## 2. Exact two-prime multiplicity from the single candidate

Take $r=1$ on the diagonal and let $M=fr$ in all cases. For the actual moving fundamental discriminant $D$, enumerate

$$W\in\mathcal R_B,\quad \operatorname{Trd}(W)=0,\quad W^2=M^2D,\quad (W+M)/2\in\mathcal R_B.$$

The moving pure radical is $V=W/M$. At each of the two varying primes $l\mid M$, a candidate admits a last lattice modification at that prime if it is integral on an adjacent cyclic-quotient Tate lattice. Precisely one of the following happens:

1. **$W$ is nonzero modulo $l$.** The integral matrix $lV=W/(M/l)$ has square $l^2D$ and is nonzero nilpotent modulo $l$. Its unique kernel/image line is the only possible quotient line. In an adapted $(v,w)$ source basis the same computation as for the forced 241 arrow gives a matrix with first column divisible by $l$ and second upper entry a unit; the square forces the first lower entry divisible by $l^2$. Thus $V$ is integral on $T_l+l^{-1}v$ automatically. This is one genuinely marked kernel, even if other kernels have the same reduced $j$.
2. **$W$ is zero modulo $l$.** Then $V$ is integral on the unmodified local lattice, and its stable lines are precisely the eigenlines of $V\bmod l$. If $l\nmid D$, the trace is zero and eigenvalue polynomial is $X^2-D$; it has two distinct eigenlines when split and none when nonsplit. If $l\mid D$, fundamentalness at the odd prime gives $v_l(D)=1$, so $V\bmod l$ cannot be zero; it is a nonzero nilpotent and there is precisely one line. Thus the number of quotient choices in this case is exactly $1+(D/l)$, with Legendre value zero on the odd ramifier.

At $l=f$, the actual $(D/f)=-1$ makes the second case empty, so $W\bmod f\ne0$ is required. At $l=r=5$ or 7, keep the computed multiplicity 1 or $1+(D/r)$. It depends only on whether $W$ is zero in $\mathcal R_B\otimes\mathbf F_r$ and on the fixed Legendre value of $D$. Since $r\nmid k_A$, the actual order there equals the seed's order, and checking $W/r$ for local integrality is an exact rank-four seed-lattice coefficient test. **No action on $r$-torsion is needed for this multiplicity check.** On the diagonal multiply by its fixed two, with no condition at a nonexistent $r$.

The two local tests are independent because the two path degrees are coprime; they determine the exact number of indexed arrow combinations. Away from $r,f$ all the associated target orders are identified with the prepath order. In particular at 2 the displayed half-integrality test is precisely that of the moving generator $(1+V)/2$, and at 16,3 the two prescribed eigenvalues are checked on the actual $A$-transported flags using the actual integral generator $\alpha=(1+V)/2$, as made explicit below. At $p\nmid 2\cdot3\cdot5\cdot7\cdot f D$, use the named normalized Lie action of the same $V$. No other level choice arises from either of the variable arrows.

## 3. The exact 16-arm and a sharper actual support congruence

Let $B_0=(W+M)/2$ be formed in the exact quaternion lattice before any finite action is taken. The verified membership condition is $B_0\in\mathcal R_B$, and the actual ordered split generator on the 16-arm is $\alpha=B_0/M$. Here $M$ is odd. The polynomial $X^2-X+(1-D)/4$ has two distinct roots modulo 2 because $D\equiv1\pmod8$; its derivative $2X-1$ is odd, so each root lifts uniquely modulo 16. On the chosen cyclic 16-line check the **full** prescribed root $\lambda$ of this polynomial with the full vector action of $\alpha$, not the radical $V=2\alpha-1$. For the exact $D=-311$ control, the roots modulo 16 are 2 and 15. Two exact valid split-matrix pairs have the same $V$ modulo 16 but opposite pass/fail status for the marked $\alpha$ test: start with $A_0=\operatorname{diag}(2,15)$, and conjugate by $1+8E_{21}$ for the first coordinate line or $1+8E_{12}$ for the second. This retains the same characteristic polynomial and $2A_0-1$ modulo 16, but sends the corresponding marked generator off its line. They lift as conjugations of the actual split 2-adic root pair. Therefore an implementation dividing an already read 16-torsion radical matrix by 2 is not valid.

In the finite Tate-lattice prepath computation use $k_A B_0 \in\mathcal R_0$ before reducing its action modulo $2^{2h+4}$, $h=v_2(k_A)$, which still suffices at the adapted lattice. Alternatively, if starting from a finite matrix for $W$, retain **one additional 2-adic digit** before the division. At 3 it is legitimate to test using $B_0/M$ too (or equivalently using $V$ and the converted root, since 2 is invertible); neither varying tame prime is 3.

For the actual auxiliary calibration, write $\omega_0=U/2$ in its full source CM order and $u=\sqrt{-5}$. At 2 both endpoints have conductor exponent 2. In the integral local basis $(1,4u)$, the cyclic 16-rays with equal endpoint depth are exactly $(0,1),(8,1)$ (the equal-depth table of the exact calibration). Multiplication by $4u$ sends $(a,b)$ to $(-80b,a)$, so its eigenvalue on those two cyclic lines is respectively 0 or 8 modulo 16. Conductor 12 just multiplies by 3, and a dual 16 switch negates this eigenvalue by trace zero; both preserve the two possibilities. Let $a_0\in\{0,8\}$ be the actual auxiliary scalar on the same marked 16-line. In a basis containing this line, both endomorphisms are upper triangular modulo 16, with respective diagonals $(\lambda,1-\lambda)$ and $(a_0,-a_0)$. Hence

$$x=\operatorname{Trd}(W\omega_0)=2M\operatorname{Trd}(\alpha\omega_0)
    \equiv 2M a_0(2\lambda-1)\equiv 2 a_0\pmod{32}.$$

The last simplification uses $a_0\in\{0,8\}$ and odd $M,2\lambda-1$. Thus the common six-family sieve can safely restrict to $16\mid x$ rather than merely $2\mid x$; a path with the identified auxiliary scalar can use its exact class modulo 32. These constraints are necessary filters, not replacements for the finite marked vector checks.

## 4. All accepted combinations have the same signed depth

At the actual named prime $p$, choose a seed symplectic $f$-torsion frame whose Weil value has the prescribed Gauss sum. Take any complement $w$ to the kernel of $W\bmod f$ there. The absolute genus sign of **every** counted path from this $W$ is

$$\left(\frac{k_A\det(w,Ww)}{f}\right).$$

To see the exact cancellation, the last-arrow formula uses total pre-241 degree $k_A r$ and nilpotent matrix $fV=W/r$. The factor of $r$ from transporting the Weil pairing cancels its reciprocal from the nilpotent matrix. The determinant remains in the same named frame, and changing the complement scales by a square. This has no unverified choice of sign between two stable $r$-lines. Diagonal uses $r=1$ and the same computation.

For $x=\operatorname{Trd}(WU)/2$, use the **single scaled support expression**

$$m=M^2 D D_A-x^2>0,\qquad |x|<M\sqrt{D D_A},\qquad x\equiv0\pmod {16}.$$

At a good contributing place $p\nmid rf$ the prime-to-$p$ arrows identify the local orders, flags and CM lift thickening as in the original dual-arrow calculation. The prepath auxiliary order and any target auxiliary order have the same local rank-two unramified order, because the changing conductors divide powers of $r,f$. The off-diagonal coordinate of $W=MV$ in that local quaternion decomposition is scaled by a $p$-unit. Thus all admitted combinations have identical normalized depth $(v_p(m)+1)/2$, with odd positive depth on $m$. This calculation never needs the characteristic-zero target's conductor or its individual reduction model. Multiplying by the exact input divisor sign, the line multiplicity of §2, and this common absolute genus sign recovers the same contribution as the complete sum over indexed paths. Distinct original seed occurrences remain distinct before adding their terms.

Consequently the prime sieve uses the six possible scaled families $M=241,1205,1687$ and $D_A=-320,-2880$. With the fixed seed Frobenius correction $J^2=-pd$ and seed saturation index $I_0$, the $W$ rows are again certified by the fixed binary quadratic field norm

$$N_{K_*/\mathbb Q}(k_A I_0 b)=\frac{(k_A I_0)^2 m}{|D_A| p d},\qquad W=(x/D_A)U+bJ.$$

The actual degree and projection denominators are fixed. No freely variable tame path is enumerated, and only the seed tame actions at 2,3,241 (plus any fixed saturation precision) are read. The square-root-in-magnitude outer trace shell and the need for a literal selected $D$ remain. This is an exact oriented-exponent evaluator design, not a calculation of those exponents, a cubic phase, odd rank, or a rational point.


The stdlib replay checks the two alpha/radical controls, the full root pair, and independently enumerates the primitive local cyclic lines and their enlarged-lattice conductor tests:

```sh
sha256sum -c SHA256SUMS
python3 check_exact_alpha_precision.py | cmp - EXACT-ALPHA-AND-SHELL-MOD32.json
```
