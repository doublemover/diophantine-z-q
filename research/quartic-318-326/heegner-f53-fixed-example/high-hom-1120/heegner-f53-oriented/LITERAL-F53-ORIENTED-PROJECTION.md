# One literal oriented reduction and an evaluated low-level modular map

Fix only the example already pinned in `../heegner-odd-residue-example`:
`d=323, K=Q(sqrt(-455)), N=5,007,792, B=60875, r=(1+B)/2=30438`.
The rational prime is 53, and the orientation on K is
`sqrt(-455) -> u` in `k=F53[u]/(u²-22)`. This dossier does not assert
any twisted high-level value, trace nonvanishing or rank.

## 1. Actual oriented marked point

Let `A: y²=x³+1` over k, `F(x,y)=(x^53,y^53)`, and
`w(x,y)=(ζx,y)`, with `ζ=(-1-u/9)/2`. The cube map on F53 is a
bijection, so counting affine points gives #A(F53)=54. The Frobenius
polynomial gives `F²=[-53]`. Since `ζ²+ζ+1=0` and
`Fw=w⁻¹F`, put `J=1+2w`, `V=(1+w)F`. Then
`J²=[-3]`, `V²=[-53]`, `JV+VJ=0`. The integral endomorphisms
`α=-9J-2V` and `Ω=-4-9w-V` therefore satisfy
`α²=[-455]`, `2Ω=1+α`, `Ω²-Ω+[114]=0`. Taking the
differential at zero gives `dα=-9(1+2ζ)=u`, not the conjugate root.
Do not replace this differential calculation by a false conjugation
formula for the entire endomorphism.

Since discriminant -455 is fundamental this is an optimal embedding of
the maximal order into the geometric endomorphisms. At every l|N the
quadratic algebra splits, with distinct roots `r,1-r` modulo l. Both
summands of the Tate module have rank one: the canonical degree
`deg(Ω-z)=z²-z+114` shows Ω cannot be scalar on E[l]. For either residual
root z one can choose a lift having degree valuation exactly one (nonzero
derivative); if Ω-z killed the whole E[l], it would factor through [l]
and its degree would be divisible by l². At l^e = 16,3,289,361 set
`C_l^e=ker(Ω-[r])∩A[l^e]`. They are cyclic of order l^e by that split
rank computation. Their direct sum is the literal `C_N`, and
`r²-r+114=185 N`. The model is therefore an oriented optimal
embedding with the prescribed differential root and level eigenline.
This does not identify a marked modular point from either source or
target j alone.

The arithmetic specialization identification is the fixed-orientation
optimal-embedding reduction theorem, not a computational inference.
Use [Cornut–Jetchev](https://arxiv.org/abs/1012.0725), the specialization
of CM points at the inert prime, as applied to the conductor-one
signed fiber in V13 14726–14821. In a fresh example choose the place of
the class field giving this class representative (or label it as the
corresponding translated class). All 20 class labels must subsequently
be retained once; changing the initial label merely permutes this
unweighted trace at that fixed orientation, not all 16 orientations.
If for an application the original place was fixed in advance, obtain
its exact labeled identification instead of rechoosing the place.

## 2. Verified low evaluation at the actual projected point

The exact script uses `L=F53[w0]/(w0^8-2)`, with `u=8w0^4`.
The binomial is irreducible: 2 has order 52, all prime divisors of
8 divide 52, gcd(8,52/52)=1, and 53≡1 mod 4. The script obtains
actual generators of C16 and C3 by multiplying A(L) points by
`(53^4-1)/16` or `(53^4-1)/3` and applying `Ω-[1-r]`.
It independently tests membership on A, the exact group order, and
`Ωg=[r]g` (the generated random points are merely a search method;
the resulting coordinates and equalities are exact).

For an actual 2-edge with kernel generator (x0,0) on `y²=x³+Ax+B`,
translate x by x0. The model becomes `y²=x³+a x²+b x`,
`a=3x0,b=3x0²+A`. Its marked Hauptmodul is
`t2=256b/(a²-4b)`. This follows from the normalized source and target
invariants `j=(t2+256)³/t2²`, `j'=(t2+16)³/t2`; more intrinsically
the marked orbit parameter is a²/b and the choice of infinity cusp,
source pole width one, is a²/b=4. The exact rational formula defines a
nonconstant coordinate on the genus-zero marked moduli curve; comparing
the q-leading coefficient on source j at the pole of order one fixes
the scale. This argument is on the actual marked edge, and hence
remains valid at j=0 and level sets of j with multiple edges.

Compute four adjacent 2-edges from `(A,C16)`, and four from
`(A/C3, image C16)`, using the two genuine Vélu maps on those groups.
From [Colò, thesis Appendix A](https://www.leonardocolo.com/documents/thesis/PhD_Thesis.pdf#page=252)
the first and last degeneracies in a chain of length l=2,3,4 have
ordered formulas `T²/(T+c), T(T+b)` with (c,b) respectively
(16,16),(4,8),(2,4). The printed middle second formula in the thesis
has a typo: first t4=t8²/(t8+4), Fricke w4=256/t4 and w8=32/t8
force the second to be t8(t8+8); the q^-1 coefficient t8= q^-1-4+...
confirms it. Same Fricke check at t4 and t16 gives the other formulas.
The script checks unique lift at each step and tests the target j on
the actual Vélu quotient as a redundant check.

The two t16 values are (6+40u,44+18u). The canonical X0(48) functions
(x,y) in [Colò, App. A](https://www.leonardocolo.com/documents/thesis/PhD_Thesis.pdf#page=265)
satisfy `y²-y(x⁴+1)=3x⁴`, and both projections
`t16(z)=x-2+3x/y`, `t16(3z)=(y-2x-1)/x`. The actual point's
noncuspidality can be read from its complete smooth elliptic moduli data;
the poles and zeroes of x in the primary divisor formula are cuspidal.
The equation and the two ordered projection values have exactly one
admissible solution over k, found by full enumeration:
`x=39u, y=22+45u`. No choice of sign or unordered j-line is used.

Set `Y'=2y-x⁴-1`, `v=Y'/(4x²)`, `z=(x-1/x)/2`. Then
`v²=z⁴+z²+1` exactly. With `A0=(v+1)/z², B0=(A0²-1)z`,
`B0²=(A0²-1)(2A0+1)`, and
`φraw=(2A0+1,2B0)` is on the literal `E_-1:y²=x(x+1)(x-3)`.
On the ∞ branch y has pole of order 4, with leading y/x⁴=1;
thus `v/z²→1`, `A0→1`, `B0→0`.
So `φraw(∞)=(3,0)`. Translating that exact point to zero gives
`φ0(A,C48)=(43+47u,15+18u)`. The map is degree two: z is
degree two in x, v follows by multiplication and division, the
remaining quartic coordinate transformation has rational inverse
`z=B0/(A0²-1)`. The corresponding elliptic factor is the exact
level-48 optimum discussed in [Brunault §6.3](https://perso.ens-lyon.fr/francois.brunault/recherche/reg_siegel.pdf).
Here only the **chosen rational** low map is evaluated.

## 3. Exact next evaluator input, not yet a result

For each actual oriented class A_i (one row above, shifted by the true
class ideal action), record:
- fixed field `k`, short coefficients, an actual representation of `Ω_i`
  satisfying the intertwining relation to the previous isogeny, tangent `u`;
- same marked 16,3,17²,19² eigensummands, or a certified quotient arrow
  and transported bases for each component. A step prime to N transports
  by image, not by rechoosing an unspecified branch;
- actual first quotient B_i=A_i/C_d with transported C48. On B_i[d], P
  is the same marked Ω_i eigenline via `image C_d²`, Q is the opposite
  eigenline via `image A_i[d]`. Thus one may recompute the two split
  d-eigenlines after B_i without choosing l² generator coordinates if
  the descended Ω_i action is known. Orient `e_d(P0,Q0)=ζ_d` consistently
  across all 20 rows; character invariance permits square-scaled
  reparametrizations but does not permit independent Weil-root changes;
- for each a∈(Z/d)×, genuine ordered quotient B_i/<Q0+aP0>,
  transported C16,C3, and the actual two edge lists. The two coordinate
  formulas in §2 compute its `φ0` value, using a certified alternate
  chart or limit at any denominator zero; the frozen example checks
  only its own chart. Compare the translated order `Ω_d=(1+dα)/2` and
  the level-48 middle discriminant label `d B≡1 (mod 96)`.
- sum all 288 values with exact `χ_-d(a)`, then perform the single
  quadratic Gauss-isomorphism using that same `ζ_d`; only then sum all
  20 high-level points and test nonzero after [4] on the correct E323.

Frobenius² acts as [-53] on A_i and all its isogenous targets over k, so
every geometric prime-to-53 subgroup used here is k-defined; a basis
of E[d] need not be k-rational. Since ord_323(-53)=72, a conductor-d
basis can be taken in F53^144; the separate 17 and 19 point bases
are available over F53^16 and F53^18 respectively. No complete such torsion-basis/quotient
data are supplied by the lattice-input list or the j-coordinate.
The separate exact list of 5760 signed conductor-323 complex form labels
is an ancestry/checksum, not an evaluated finite trace. No fabricated
row values should be accepted.
