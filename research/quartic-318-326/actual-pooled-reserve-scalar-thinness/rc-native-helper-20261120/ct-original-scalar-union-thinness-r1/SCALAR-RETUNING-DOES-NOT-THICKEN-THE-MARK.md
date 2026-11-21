# Retuning the literal scalar poles still gives a thin rank family at each fixed integer input

The analytic question is pointwise in the original integer input.
A count for one prepared pole alone does not rule out using the entire
union of source indices to reach a positive-density twist family.
In the **scalar** row the following exact identity does rule that out,
for every integer input \(a\), on the same original pole formula.
This does not obstruct changing a detector's mark, or independently
proving the ranks of a thin family.

## 1. Every literal scalar preparation at input \(a\) has the same mark

The pinned definitions **PreparedIntegerSource318.scalarB** and
**ScalarForwardWitness318.poleInput** give
\[
 b_{\rm sc}=114444\,R(a)\cdot q^2 ,
\]
where the rational quotient \(q\) contains the actual trace, norm,
source labels and index. On any eligible pole \(q\ne0\); it does not
affect the squareclass \([17b_{\rm sc}]\). Put \(x=a(a+1)\). Exact
expansion of inputFourth and inputR gives
\[
 \begin{split}
 R(a)&=4S(x),\\
 S(x)&=(7446x+661)(7446x+1861)(29784x+7445)(476544x+119479).
 \end{split}
\]
Since \(17\cdot114444\cdot4=204^2\cdot187\), the positive squarefree mark
is always
\[
                     \beta(a)=\operatorname{sf}\bigl(187\,S(a(a+1))\bigr).
\]
This is independent of all choices of source labels at that input,
the common lattice index \(h\), the real direction \(t\), all
local preparations and later twist helpers. In particular choosing
new admissible scalar indices, allowing arbitrarily many admissible
local CRT refinements, or letting the companion \(\theta=[1-b_{\rm sc}/17]\)
vary cannot change this mark.

For all integer \(a\), \(x\) is even, and \(S(x)\equiv11\bmod24\)
and \(S(x)\equiv14\bmod17\). These identities follow directly by
the four product factors (the exact class computations are replayed):
modulo 3 all slopes are zero and the constant product is 2;
modulo 8 the first two factors are equal and odd and the other
two are 5 and 7, giving 3; modulo 17 all slopes are zero and the
constant product is 14. Thus \(187S(x)\equiv17\bmod24\) and
its 17-valuation is exactly one. Dividing out integer squares
prime to 6 preserves the residue modulo 24, and preserves the odd
17-depth. Consequently \(\beta(a)\equiv17\bmod24\) and \(17\mid\beta(a)\),
so the real quadratic field \(K_a=\mathbb Q(\sqrt{\beta(a)})\)
never degenerates. At \(a=0\) the representative is the same
204618888056724185 as in the literal compact scalar packet.

## 2. Quantitative upper bound even without keeping a selection algorithm

Let \(d>0\) be any positive squarefree twist parameter prime to 6
whose full \(\mathrm{Sel}_2\) contains the marked class
\((\beta(a),1)\) in the \((x+3d,x-d)\) convention. It is not necessary
to assume the assigned helper pattern, the deleted sharp witness,
or \(|\mathrm{Sel}_2|=8\) for this upper bound.

- For \(p\mid\beta(a)\) (all such primes are \(\ge5\)), if \(p\nmid d\)
  the curve has good reduction at this odd place. The local Kummer
  image is unramified, with even valuation of each scalar coordinate.
  It cannot contain \((\beta(a),1)\), so every such \(p\) divides \(d\).
- If \(p\mid d\) and \(p\nmid\beta(a)\), the torsion points at the
  three roots generate the local image. Indeed
  \(E_d(\mathbb Q_p)/2\) has size \(|E_d(\mathbb Q_p)[2]|=4\), from
  the open pro-\(p\) formal subgroup and the finite quotient, and
  the \(x=0,d\) torsion tuples have independent valuation pairs
  \((1,1),(1,0)\). The only local class with both valuation bits zero
  is the identity. The marked class therefore requires
  \((\beta(a)/p)=+1\).

Hence necessarily \(d=\beta(a)m\) with \(m\) squarefree and all its
prime divisors split in \(K_a\). This applies individually to **both**
members of every selected scalar pair as the source varies, since
both literal curves are required to keep the same mark.

The semigroup of squarefree split-supported \(m\) has counting scale
\(Y/\sqrt{\log Y}\). For detail take \(\chi\) to be the nontrivial
quadratic character of \(K_a\). Its indicator has Dirichlet series
\[
 \prod_{\chi(p)=1}(1+p^{-s})
 =\zeta(s)^{1/2}L(s,\chi)^{1/2}
 \prod_{\chi(p)=1}(1-p^{-2s})
 \prod_{\chi(p)=-1}(1-p^{-2s})^{1/2}
 \prod_{p\mid\mathrm{disc}(K_a)}(1-p^{-s})^{1/2}.
\]
All the displayed corrective factors are finite or absolutely
convergent in a neighbourhood of the real point 1, with positive
value there. The fixed-modulus prime number theorem also gives the
prime mean \(1/2\) with arbitrary fixed log-power error, and all higher
prime-power indicator values vanish. The standard
[Landau–Selberg–Delange theorem](https://arxiv.org/abs/1710.01389)
then gives a positive constant times \(Y/\sqrt{\log Y}\).
Removing the irrelevant prime 2 (if present) is only a finite
factor; the claim needed here is just the upper bound.

Thus for each fixed original integer input \(a\),
\[
 \#\{d\le X:\ d\text{ from either selected scalar twist coordinate,
                     at any eligible source for }a\}
           \ll_a X/\sqrt{\log X}.
\]
Even a density-one theorem on all squarefree quadratic twists (or
on a fixed ordinary progression) cannot force hitting this union
for a single fixed input. This is stronger than saying the original
one-prime row is sparse. It quantifies a necessary support obstruction
that survives **all** scalar index and helper choices on the actual
original formula. It is an upper bound rather than an assertion that
every split-supported \(d\) is eligible. It makes no assertion about
the two ranks or actual solutions to the polynomial.

### Exact source and replay

ScalarForwardWitness318.lean from the original scalar source
completion is bound in the manifest below. The replay expands the
literal rational coefficients before comparing the product,
exhausts \(a(a+1)\) residue classes, and checks the zero-input
integer representative without rank or large-level computations.

    python3 -B replay_literal_scalar_support.py | cmp - EXACT-LITERAL-SCALAR-SUPPORT.json
    sha256sum -c SHA256SUMS
