# Two optional exact support screens for the scaled fixed-241 receiver

These screens sit **before** constructing any local supersingular order. The first tests the rational quaternion algebra on each support row. The second removes a rational prime only from the **full anti-invariant oriented divisor**, not from individual indexed intersections. They neither change the six exact trace shells nor evaluate a moving exponent.

Input identities: scaled all-free tame-arc shell, manifest `ac177226841efab5e79f55d0a057850b6881161379a3929c88572c6d988854a8`; complete exceptional-place and four-imaginary-projection receiver, manifest `127d48b5903e21fb7507b9c93ccd895278b39154edb81e1411f363f06dd5444f`. On the selected arms the latter uses the genuine split-at-five source refinement, not a claim about an arbitrary earlier scalar.

## 1. Exact coordinate comparison and rational support

Write $f=241$, $M=fr$ for the shell scale, $r\in\{1,5,7\}$. The moving fundamental discriminant $D<0$ is split at 2 and 5. Its moving radical is $V^2=D$ and $W=MV$. The actual prepath auxiliary radical is $U=2g_0u$ with $u^2=-5$, $g_0=4$ or $12$, and $D_A=U^2=-20g_0^2$. The published shell has
$$x=\operatorname{Trd}(WU)/2,\qquad m=M^2 D D_A-x^2>0.$$
Use the following translation, where $g$ is only a **scaled shell parameter**, not the auxiliary curve conductor:
$$g=M g_0,\qquad y=x/2,\qquad S=5|D|g^2-y^2=m/4.$$
The shared constraint $16\mid x$ is $8\mid y$. On an identified auxiliary ray the finer condition $x\equiv 2a_0\pmod{32}$, $a_0\in\{0,8\}$, is $y\equiv a_0\pmod{16}$. Factoring at the two signs of $y$ is identical, but candidate embeddings at those signs cannot be identified.

For a collision, remove the component along $U$:
$$J_0=W-(x/D_A)U,\qquad UJ_0=-J_0U,\qquad J_0^2=m/D_A=-S/(5g_0^2).$$
Indeed the anticommutator of two pure quaternions is the reduced trace of their product, here $2x$. Then $J=g_0uJ_0$ anticommutes with $u$ and $J^2=-S$. Since $S>0$, the generated rational algebra is $(-5,-S)$; it contains the moving quadratic field $\mathbb Q(\sqrt D)$. These statements also hold for the abstract algebra of any row: in $(-5,-S)$ take these $u,J$, recover $J_0=(g_0u)^{-1}J$ and $W=J_0+(x/D_A)U$; its square is $M^2D$ and $W/M$ embeds that quadratic field.

The algebra is ramified at infinity. At 2 and 5 it is split because its embedded quadratic algebra is split and gives nontrivial idempotents, impossible in a division algebra. At any other odd prime $\ell$, the auxiliary extension is either split or unramified quadratic. In the inert case, $-S$ is a local norm exactly when its valuation is even. Hence the entire **finite** ramification set is
$$\{\ell:\ \ell\ne 2,5,\ (-5/\ell)=-1,\ v_\ell(S)\text{ odd}\}.$$
The set must be exactly $\{p\}$ for a candidate collision in $B_{p,\infty}$. Compute this set before discarding exceptional primes; an extra inert-odd factor still defeats the row even if that extra prime could never contribute. Two certified distinct members already reject. Conversely a singleton certified by exact factorization or equivalent complete parity information passes **only** the rational isomorphism test. Neither maximal-order integrality nor Lie or tame marks are certified. Hilbert reciprocity in these guarded shells implies the set has odd cardinality; this is a replay consistency check, not a replacement for finding the set. At a nonexceptional singleton $p$, the moving field must likewise be inert, since $p\nmid2D$ and the algebra cannot contain a split local quadratic algebra.

For the good-prime evaluator keep its existing exceptional set $p\mid 2\cdot3\cdot5\cdot7\cdot fD$. The prime 29 is already auxiliary-split and so cannot appear on this support; the cubic receiver uses its separately named unit place. Odd primes dividing $g$ are already among the fixed exceptions. The other guards, including nonzero genus signs, are unchanged.

## 2. Which rational primes can be skipped in the full signed ideal

Put $F_*=\mathbb Q(\sqrt5,\sqrt6)$, $M_{\mathrm{im}}=\mathbb Q(\sqrt{fD})$, and $E=F_*M_{\mathrm{im}}$. The calibrated complete genus product $R\in E^\times$ has $cR=R^{-1}$, with $c$ complex conjugation: it fixes $F_*$ and negates $\sqrt{fD}$. At a good unramified rational prime $p$, if
$$ (5/p)=(6/p)=+1,\qquad (fD/p)=-1,$$
the Frobenius is precisely $c$. Every $E$-prime over $p$ is then fixed by $c$; therefore $v_{\mathfrak P}(R)=v_{\mathfrak P}(cR)=-v_{\mathfrak P}(R)$, so each oriented exponent is zero. At a remaining candidate collision, $(D/p)=-1$, so this criterion becomes $(5/p)=(6/p)=(f/p)=+1$. Nothing asserts an individual indexed intersection, auxiliary summand, unsigned count, or partial ideal has zero valuation. If skipping $p$ in the evaluator, skip it only for the entire final anti-invariant ideal.

For each of the four projected imaginary fields $M_s=\mathbb Q(\sqrt{sfD})$, $s=1,5,6,30$, an inert good prime is likewise fixed and gives no projected exponent. If $F_*$ is nonsplit at $p$, exactly two of these four fields split: multiply $(fD/p)$ by the four values $1,(5/p),(6/p),(30/p)$, which then have two of each sign. If it is split, either all four split or all four are inert. Simply omitting the inert projections must not change the named orientations, residue-degree multiplicities, or exponents used in the remaining projections.

## 3. Primitive coefficient reuse and exact bounded audit

For fixed $D$ let $d=\gcd(g,|y|)$. Use the key $(g/d,|y|/d)$ and set $S_0=5|D|(g/d)^2-(|y|/d)^2$, so $S=d^2 S_0$. Rational Hilbert symbols, including the inert-odd set, are unchanged by removing this square. If an actual good prime survives, $p\nmid g$, hence $v_p(S)=v_p(S_0)=v_p(m)$; at a discarded prime dividing $d$, the full valuation has changed by $2v_p(d)$. Use a cached factorization/parity only with the original $D$. Keep the physical seed, Atkin transform, signed $x$ and exact marked scalar class, prepath order, Lie orientation, named coefficient place and genus sign on each row. Reuse never merges different geometric occurrences. In particular, an implementation cannot read $\alpha=(W+M)/(2M)$ from an already truncated $W\bmod16$.

The audited reference is the established numerical **control** $D=-311$, not an original selected detector. It includes a three-prime rejecting row, an anti-invariant-zero prime, a row with precisely two active quadratic projections, and the two already known rational $p=19$ candidates $x=112,1024$. These latter rows remain only rational support/depth candidates. Two rescaled representatives of $x=112$ illustrate cache reuse and the excluded depth shifts at 3 and 5. The only extra census is the first 128 nonnegative magnitudes $y=8k$ in the single shell $(M,g_0)=(241,4)$. It is deliberately not a full six-shell experiment. Trial factoring takes place only on that bounded exact control and never establishes availability of factorizations at the true scale. No marked $p=19$ path, moving exponent, full cubic residue, or original rank/point is produced.

```sh
sha256sum -c SHA256SUMS
python3 check_rational_and_antiphase_prefilters.py | cmp - EXACT-BOUNDED-SUPPORT-CONTROL.json
```
