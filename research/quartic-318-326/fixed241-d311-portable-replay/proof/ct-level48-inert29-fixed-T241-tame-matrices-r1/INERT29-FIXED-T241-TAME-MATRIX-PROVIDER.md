# All degree-241 arcs on the three inert-29 target models

The exact local operator for **fixed conductor 241** is now a table of 726 actual isogenies. Each outgoing kernel from each of the three supersingular source models has its own exact action on the transported level-16 and level-3 flags. On arbitrary oriented maximal-order inputs the relevant determinant sign is then a fixed-field calculation, independent of the size of the moving fundamental discriminant. This is the finite operator, not the set or signed sum of its selected moving CM embeddings.

## 1. Source frames, actual kernels, and tame maps

Use the exact three models $A_0:y^2=x^3+1$, $A_2:y^2=x^3+14x+22$, and $A_{25}:y^2=x^3+6x+21$ over $\mathbf F_{29^2}$, indexed by their $j$. The last two are literal degree-two and degree-three quotients of $A_0$ by the lines with abscissae $-1$ and $20$. Every model has scalar $29^2$-Frobenius $[-29]$. Consequently a geometric isomorphism between any two such models with the same $j$ is defined over this field, since it intertwines the common scalar; there are no missing twist cases. The implementation finds one exact short-Weierstrass scaling for every output.

Choose full ordered $E[16]$ and $E[3]$ bases on each model. The first lives in the degree-four subfield of the fixed binomial degree-120 extension used in the complete primitive reference, and the second is already $\mathbf F_{29^2}$-rational. Each frame is constructed by scalar cofactors and checked for exact order and independence. The full $24\times4$ abstract cyclic flag choices on each model are retained. Their actual Colò coordinates give 32 distinct geometric labels on $j=0$, and 96 on each of the other two models. The table does not throw away the frame information in the repeated $j=0$ labels.

On $A_0[241]$ use the exact two eigenline generators from the primitive conductor-241 reference. Transfer this entire 241 basis through the fixed source maps of degrees 2 and 3 to get a frame on each other model. These maps are prime to 241; their degree factors in the Weil pairing are both squares modulo 241. Thus all three frames agree with one common symplectic square-class convention, though not necessarily the same literal symplectic volume. Every $241$-line is enumerated once as $(1,k)$ for $k=0,\ldots,240$, and $(0,1)$. Unlike the split-conductor reference, the table includes both possible horizontal lines because their status depends on the future oriented embedding.

The quotient map on each marked input is evaluated by the exact same pairwise Vélu formula and four-shift degree-30 trace as in the fixed-conductor reference. There are two length-60 root orbits per line, and batch inversion uses a common nonzero product. To obtain both target matrices evaluate at all four tame basis generators before normalizing the actual output model; recover the four columns by exact finite torsion coordinate lookups. Each matrix is invertible modulo its level, as checked. For any incoming flag, multiplying its frame coordinates and taking the resulting cyclic spans gives the two actual target subgroups, not just the target $j$. The paper's three models contribute exactly 242 arcs each.

## 2. Applying a signed row

For any supplied $V=\iota(\sqrt{D})\bmod241$ in the receiver's frame, a kernel line $L=\langle z\rangle$ carries the weight
$$
         (\det(z,Vz)/241) .
$$
Zero is horizontal. This formula works for either residue squareclass of $D$, and uses the exact kernel ordering in the table. On the full genuine CM index set, the base ideal's quadratic factor cancels the corresponding Weil-volume factor of the transported reference generator: an actual prime-to-241 ideal isogeny of degree $d$ multiplies the pairing exponent by $d$, while its ring class genus term is $(d/241)$. Thus, via a common symplectic square class, the determinant convention differs from the full indexed genus weights only by a single constant sign. The three fixed model changes above preserve that convention. One still needs the actual optimal embeddings and their oriented flags; an unmarked $j$ list or ordinary unweighted $T_{241}$ matrix does not supply them.

As a full exact validation of this operator, the script recovers the two transported 241 eigenline directions for **all 48** original base indices of $D_0=-1751$. It uses an independent $x$-orbit lookup of all $(241^2-1)/2$ nonzero abscissae on each fixed source model, with the sorted projective line labels; since changing a nonzero point's sign does not change its eigendirection, no ordinate logarithm is required. It then reaggregates the entire split primitive family solely from the determinant formula and the precomputed matrices. All 48 positive/negative histograms agree exactly with the independent explicit-conductor replay; the exact total is still $-86\equiv4\bmod9$. This check verifies the matrix convention and the original orientation transport at every indexed fibre, including true collisions.

## 3. One nonsplit local branch control

Under the already specified fixed-241 duplicate-alias source refinement, keep exactly the first-arm incidences of 241 to $17,q,103$ and keep all remaining helper incidences to it plus. The six actual contact/denominator source choices can use Gaussian norm 1 at 241 for the contacts and norm 17 for $q$. Choose the fresh helpers in the sharper compatible class $1\bmod241$ when their fixed-241 rows are plus. Then $D'=-n/241$ is congruent to $-17\cdot103\cdot17=117\pmod{241}$ in the first arm, a nonsquare; the same nonsplit type remains on the companion since its protected total $\theta$ symbol is plus. This is a local refinement of the allowed graph, not a numerical original input or a requirement on every selection. For the companion balancing gadget, no repair needs the 241 vertex as a chosen alias: if the main kernel had its only exceptional bit there, either $e_{241}$ or $1+e_{241}$ would belong to the kernel. Their actual retained $q$ row is 1 since the $q$--$241$ incidence is 1 and the $q$ row of the skew correction is zero. Thus both needed bits have witnesses at other vertices.

For the fixed local trace-zero matrix
$$
              V=\begin{pmatrix}0&117\\1&0\end{pmatrix}
$$
all 242 lines are vertical, of which 121 are positive and 121 negative under the exact determinant. At frame input $((1,0),(1,0))$ the three independently exact responses on the ordered output phase are $8,8,4\bmod9$ on $j=0,2,25$, respectively. The full 96-frame response distributions per model are in the separate small inert control. This proves that local inert orientation does not by itself annul the operator. It does **not** prove that a moving true CM index has this chosen frame, or that any of the actual signed moving sums is nonzero.

### Replay

The matrix replay pins the complete fixed primitive reference and its coordinate donors for exact finite field and Vélu rules. The orientation control consumes the resulting full table and a separate exact 29 flag/phase evaluator. No moving CM orbit is constructed.

```sh
OPENBLAS_NUM_THREADS=1 python3 replay_inert29_fixed_T241.py | cmp - EXACT-INERT29-FIXED-T241-MATRICES.json
python3 check_T241_inert_orientation.py | cmp - EXACT-T241-INERT-ORIENTATION.json
sha256sum -c SHA256SUMS
```
