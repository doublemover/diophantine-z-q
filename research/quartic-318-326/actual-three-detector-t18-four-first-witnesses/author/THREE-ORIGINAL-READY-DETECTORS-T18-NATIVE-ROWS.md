# The fixed \(t_*=18\) first witness fills the three original detector first rows

Fix a genuinely prepared original common index, its actual contact key, the original labels and the physical anchor. This is an exact first-witness construction and a rank-free companion interface at slots 190, 241 and 292, alongside the separate scalar at slot 314. It does not produce any of the three global detector companions or choose a new key or index.

## 1. Native normalization at the same three slots

Write \(\tau\) for the original Gaussian contact parameter, \(c_j\) for the three actual scales (including \(c_0=1\)), \(D,Q\) for the actual common clearing and wheel enlargement, and \(q,p_{j,i}\) for the genuine denominator and five contact primes of row \(j\). Here \(j=0,1,2\) refers to the literal outputs of the same \(\texttt{ThreeDetectorUniformFamily318.witness}\) at slots \(190+51j\). Its exact \(\texttt{witness\_squareclass}\) gives
\[
 b_j=F(c_j^2\tau)\,S_j^2
\]
with \(F=\texttt{ContactWeightWitness318.contact}\) and the **actual** rational square factor \(S_j\) from the literal first or scaled chain, not an independently chosen scaling. As recorded in the previously reviewed original-fold donor, the affine linear contacts give
\[
 F(c_j^2\tau)=\left(\frac{c_j^2}{D^2 Q^2 q}\right)^5\prod_{i=0}^4 p_{j,i}.
\]
It follows, in the original charts, that
\[
 d_j=q\prod_{i=0}^4 p_{j,i},\qquad
 \rho_j=\frac{c_j^5 S_j}{(DQ)^5q^3},\qquad
 b_j=d_j\rho_j^2,\quad B_j=17b_j=\beta_j\rho_j^2,\quad \beta_j=17d_j.
\]
The genuine prime profile gives distinct primes within each row, all different from 17, so \(\beta_j\) is its positive squarefree integer, including the factor 17. This does not require factoring the reduced numerator of the folded \(b_j\) or its complement. The sign of \(\rho_j\) does not matter; it is nonzero by \(b_j>0\), and determines a permitted sign of the first ordinate below. With merely a positive rational \(b_j\), the same construction also works by choosing the positive squarefree representative of \(17b_j\) abstractly; the contact identity here supplies the actual compact scale for a genuine key.

## 2. The direct first-row witness, not a replacement polynomial

For each \(j\) write \(\mu_j=\beta_jt_*^2,\ A_j=1+3\mu_j,\ k_j=(1-\mu_j)(1-9\mu_j)\), with the same fixed \(t_*=18\) on all three rows. Then \(\mu_j>1\) and \(A_j^2-k_j=16\mu_j\), so \(0<k_j<A_j^2\). Assign
\[
 T_j=\frac{B_j k_j}{A_j^2},\qquad
 y_{1j}=\frac{8\beta_j^2 t_*\rho_j^3(1-3\mu_j)}{A_j^2},\qquad
 e_j=\frac{T_j}{b_j}=\frac{17k_j}{A_j^2},\quad
 p_j^{\rm cert}=\frac{y_{1j}}{B_j}
    =\frac{8\beta_j t_*\rho_j(1-3\mu_j)}{A_j^2}.
\]
These give \(0<T_j<B_j\) and \(y_{1j}\ne0\). The identities
\[
 B_j-T_j=(4\beta_jt_*\rho_j/A_j)^2,\qquad
 B_j+3T_j=B_j\bigl(2(1-3\mu_j)/A_j\bigr)^2
\]
give exactly the first native point and its ordered class \(([B_j],1)\) on \(y^2=x(x-T_j)(x+3T_j)\). In the \(\texttt{Certificate}\) normalization they give
\[
   e_j b_j=T_j,\qquad 17(p_j^{\rm cert})^2=b_j(17-e_j)(17+3e_j).
\]
For a fixed key \(e_j\) depends on the contact squareclass, not on the later common index or square factor \(\rho_j\). The three \(e_j\)'s need not coincide; the source has three separate slots for them.

In the literal \(\texttt{Raw318FinalReplay}\) formulas, write \(z_{1j}=e_j b_j,\ z_{2j}=(s_j^{\rm cert})^2,\ z_{3j}= -G_j/3\) with
\[
 G_j=((s_j^{\rm cert})^2-e_j(17-b_j))
      ((s_j^{\rm cert})^2+3e_j(17-b_j)).
\]
The two first-side rows of each block are precisely \(z_{1j}-e_j b_j=0\) and
\[
   3e_j z_{1j}+17(p_j^{\rm cert})^2-289 b_j-34 z_{1j}=0.
\]
After inserting \(z_{1j}=e_j b_j\), the latter is the factored \(\texttt{Certificate.first}\) equality above. The slot map, directly from \(\texttt{ThreePoleCertificates318.fill}\), is:

| literal pole | \(e,s^{\rm cert},p^{\rm cert},q^{\rm cert}\) | \(z_1,z_2,z_3\) | first-side row IDs | other three row IDs |
|---|---|---|---|---|
| 190 | 39, 40, 41, 42 | 191, 192, 193 | 152, 154 | 153, 155, 156 |
| 241 | 43, 44, 45, 46 | 242, 243, 244 | 205, 207 | 206, 208, 209 |
| 292 | 47, 48, 49, 50 | 293, 294, 295 | 258, 260 | 259, 261, 262 |

Thus the six displayed first-side row equations are solved simultaneously on the same original input and index. No unknown second-side values were inserted into those six equations.

## 3. Exact remaining raw companion inputs

Put \(\delta_j=1-b_j/17\in(0,1)\). The single remaining global input per detector for this fixed \(T_j\) is an affine rational point on
\[
             w^2=\beta_j(v^2-k_j\delta_j)(v^2+3k_j\delta_j).       \tag{*}
\]
In the **raw certificate** variables its exact conversion is particularly short:
\[
                 s_j^{\rm cert}=17v/A_j,\qquad
                 q_j^{\rm cert}=17\rho_j w/A_j^2 .
\]
Substitute \(e_j(17-b_j)=17^2 k_j\delta_j/A_j^2\). The right side of \(\texttt{Certificate.second}\) becomes
\[
 b_j\,17^4 (v^2-k_j\delta_j)(v^2+3k_j\delta_j)/A_j^4
   =17^3 B_j (v^2-k_j\delta_j)(v^2+3k_j\delta_j)/A_j^4.
\]
The left side is \(17^3\rho_j^2 w^2/A_j^4\); their equality is exactly (*) as \(B_j=\beta_j\rho_j^2\). The other raw rows read \(z_2-(s^{\rm cert})^2=0\), \(z_3+G_j/3=0\) after substituting \(z_1=e_j b_j,\ z_2=(s_j^{\rm cert})^2\), and \(17(q^{\rm cert})^2+3b_j z_3=0\). Thus they too reduce to the stated identity with the actual row expressions, not to a modified polynomial. For the fourth row in each block the explicit polynomial part is
\[
 -289e_j^2+34e_j z_{1j}-z_{1j}^2
   +\tfrac{34}{3}e_j z_{2j}-\tfrac23 z_{1j}z_{2j}
   +\tfrac13 z_{2j}^2
 =-(17e_j-z_{1j})^2+\tfrac23(17e_j-z_{1j})z_{2j}
   +\tfrac13 z_{2j}^2 =G_j/3,
\]
which verifies the sign of the auxiliary coordinate.

The conversions in (*) are reversible since \(A_j>0,\rho_j\ne0\). A rational point has \(v\ne0\) since the right side at zero is negative. In the original \(\texttt{PointPair}\) notation, the second coordinates are \(s=B_j v/A_j\), \(y_2=(B_j\rho_j/A_j)^3\beta_j v w\); applying the native \(\texttt{PointPair.certificate}\) recovers the raw values displayed above. There is no division by \(q^{\rm cert}\), \(w\), or \(y_2\), all of which are allowed to vanish. Conversely a raw certificate with this \(e_j,p_j^{\rm cert}\) would have \(s_j^{\rm cert}\ne0\) automatically by the negative right side at zero, and produces (*).

If the actual \(\delta_j\) is a rational square \(J_j^2\), \(v=J_jA_j,\ w=8\beta_jt_*(1-3\mu_j)J_j^2\) is an immediate exact point of (*); no selected detector is asserted to satisfy this. The same all-place argument as in the uniform scalar proof gives local points of (*) under the precise detector Ready hypotheses. At 2, 3 and 17 the depths of \(B_j/289\) are respectively at least 3, 1 and 1; at every other odd-support prime the square denominator puts \(B_j\) at positive depth, so \(\delta_j\) is a local square. At the other nonsquare-\(\beta_j\) places outside \(2,3\), neither \(1-\beta_jt_*^2\) nor \(1-9\beta_jt_*^2\) vanishes in the residue field, \(\delta_j\) has even depth, and the good-reduction unit Kummer argument applies as before. This is not an assertion of a global point.

The prepared source and row 287 anchor are not changed. Whenever the existing preparation supplies a single common index with all three Ready detector poles and a prepared scalar, the three first witnesses here and the fixed scalar first witness **coexist on that same original assignment**. There is no requirement that their four native parameters coincide. The four companion quartics each retain their own actual complement. Producing global rational points on all four such receivers would meet \(\texttt{complete\_at\_index}\), without a Selmer-size or rank input. The existing factorless \(t\)-rescaled low-real-branch construction has a different choice of \(T_j\); the present calculation supplies the **same normalized \(t_*=18\)** as in the scalar proof and directly identifies all original certificate slots. Neither construction produces a global second witness here.

## Exact source bindings

- Native raw statements \(\texttt{Raw318FinalReplayData.lean}\) SHA-256 c563f76c563192a218c3bdf22714ab73f36d3a0ed9c629a346d7d3bb9fa80457.
- \(\texttt{ThreePoleCertificates318.lean}\) e751b9e9f9125245a152f9cb1d9cb28e3a48571e1de09b101390d851eb85cab8.
- \(\texttt{ThreeDetectorUniformFamily318.lean}\) df9f80935c672c24ed8d095be490c4253951c69af224fbf8236d9d54737fe42b.
- \(\texttt{ThreeDetectorPrePole318.lean}\) c5455945e0aeba441d5333dbf49338dde340dd13a29ee5c1fe0fc8c3ee74be22.
- \(\texttt{NormalizedPolePoints318.lean}\) 410995ba113f37dfcb54261e61eb6b90fde58242a4fa0eed79282e99ad060542.
- Previously reviewed original factorless/contact donor list 4e142e87dffb2aa8f9eb88a72fcf43328d43d3fb54f9ac95402ac0eeb0c56a61 and the uniform \(t_*=18\) scalar list e4f4c4f4462c7b50d3f66ec358ab35292e58087dba920650884c03be06aa7eed.

No key, companion point, prime scan, native build or remote action is involved.
