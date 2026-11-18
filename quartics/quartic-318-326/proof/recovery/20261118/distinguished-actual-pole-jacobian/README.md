# A single marked Jacobian on each of the four unchanged prepared poles

For a fixed rational prepared pole b put R=b/17, D=1−R. In this note 0<R<1, R=βu² and D=θz² (positive squarefree representatives). Assume θ>1; the square-complement case already gives a literal pair directly. In particular v17(R)>0 is odd by preparation. All four b's here can be those of the *same* reviewed common-index producer. No new index, auxiliary prime, squarefree factorization of D or choice of unindexed pole is needed to WRITE either of the following rational objects:
    
    J_R: y²=x(x+4)(x−3D/R),    δ_R=(D,1,D) in root order (0,−4,3D/R).

The displayed full Kummer class is in Sel₂(J_R), does not come from rational torsion, and maps to the 2-torsion of Sha. If its image in Sha is zero, the literal pair at this specific b has rational witnesses with both ordinates nonzero. Equivalently, lifting δ_R is necessary AND sufficient for rationality of the distinguished genus-one fiber selected below, but only sufficient for the original unrestricted Realization. Even nonzero rank or another rational Kummer class on J_R is not enough by itself. No assertion that δ_R actually lifts on the indexed poles.

## The actual fiber and its reversible marked map

The unrestricted iff (source below) permits any r₀=βc²>1. Select r₀=1/R. This is legal since (1/R)/β=1/(βu)². For its two quadrics use λ=R a, M=R b₁/z, and s as in that iff. At affine t=1 or homogeneously:
    
    M²=λ²+12R t²,               R s²=(λ+2t)²−16D t².                   (1)

Their normalization is the smooth curve C_R in local/FIXED-POLE-NORM-LINE-LOCAL.md: that paper uses a DIFFERENT λ, its rational norm-line parameter. Its birational equivalence is written there; the first C_R equation is β d²=(R l²−2l+1)(R l²+6l+9). In (1) the two diagonalizing forms L=λ−6t, K=λ+2R t give exactly

    L²=4M²−3R s²,               K²=D M²+R²s².                           (2)

Conversely, given (2), t=(K−L)/(2(R+3)) and λ=L+6t give (1), by reversing the independent linear combinations: L²−4M²+3R s² equals 3 times the second quadric minus 4 times the first, and K²−D M²−R²s² equals −R times the second minus D times the first (quadric forms taken left minus right). The coefficient determinant is nonzero for 0<R<1. For s≠0 set

    x=D(2M/(R s))²,          x+4=(2K/(R s))²,          x−3D/R=D(L/(R s))².  (3)

Thus y=D(2M/(R s))(2K/(R s))(L/(R s)) and (x,y) is on J_R. Conversely any nontorsion point in δ_R gives rational U,V,W with x=D U², x+4=V², x−3D/R=D W². Choose their signs so y=D U V W, and take s=1, M=R U/2, K=R V/2, L=R W; then (2),(1) hold. Over an algebraic closure the rescaling U,V,W by square roots of D identifies this full marked 2-cover with the usual split cover for the trivial class (multiplication by 2); this yields the claimed Jacobian and identifies its Selmer label, not only its j-invariant. Equations (2),(3) give the standard smooth complete-intersection full 2-cover since the three roots of J_R are distinct. The affine exclusions remove finitely many points. Alternatively define the curve by smooth completion throughout. The two presentations therefore give the same class in Sha, with smooth-cover local points movable away from those exclusions.

## Why this is in the Selmer group and what a rational lift buys

See the independent local proof and executable controls in local/. Its finite assumptions follow already if b has square reduced denominator, v₂(b)≥3, v₃(b)≥1 and v₁₇(b) positive even ≥2 (as well as 0<b<17). At 2,3,17 use D locally square by R of positive valuation (at least 3 at 2). At odd p|β we have v_p(R) odd, hence positive by the square denominator away from 17; so D is square. At odd p|θ not 17, v_p(D) odd cannot be negative: then v_p(R)=v_p(D)<0 contradicting the square denominator. Consequently R≡1 mod p, making β locally square. No stronger original 2-adic squareclass assumption on b is needed. The real place is immediate.

J_R(Q)[2] consists of O and the three displayed roots. In the split halving criterion a nonzero 2-torsion point can be halved only if both of its differences from the other roots are squares. At −4 or 0 a negative difference precludes halving; at 3D/R the difference from 0 has odd 17-adic valuation. Thus there is no rational 4-torsion, and odd-order torsion contributes zero modulo doubling. O is not δ_R because θ>1. The first Kummer entries of the roots at −4 and 0 are respectively −4 and −12D/R (negative), whereas D>0. The first entry at the largest root is 3D/R, differing from D by 3/R, of odd valuation at 17. Thus δ_R never comes from torsion. If it lifts, a nontorsion point and all of its odd multiples have the same class and are infinitely many. They give infinitely many rational points of C_R and avoid any finite boundary, including t=0, b₁=0 or s=0 in the original quadrics.

The norm-line presentation even removes the zero-ordinate restriction. For its parameter l set X=l(1+√D) over Q(√D). Its norm is R l² and the other two norm factors multiply to β d², giving the full aligned mark with some secondary class as in the aligned trace construction. In that construction the two original rational points arise, up to signed twist and square scaling, as P±σP from the point with normalized abscissa X. If an ordinate vanishes, one of these traces is a nonzero 2-torsion point T, so σX must equal the normalized abscissa after translation by T. The normalized torsion translations are X, −3/X, 1+4/(X−1), −3+12/(X+3) including the identity. But σX=[(1−√D)/(1+√D)] X with constant not 1 or 0. None of the four equations holds identically in X: the latter three maps have genuine finite poles. Only finitely many l, including excluded degeneracies/trace O, are lost. Thus the positive global alternative would supply both nonzero ordinates on the literal original curves. Lifting at one b, or having local points at all four, does not prove simultaneous rational lifts.

## Small exact arithmetic control and source context

At b=(204/91)², R=2448/8281, D=5833/8281, 1+3R=(125/91)². The prepared numerical control λ=2, M=250/91, s=4 satisfies (1); (3) gives a nontorsion rational point in δ_R. This is a stand-alone check of the map, *not* one of the source's selected poles. The actual a=0,−1 indexed scalar and three selected contacts use their own unchanged R. Executable rational forward/reverse and addition checks are provided. Precise dependencies:

* Unrestricted trace source UNRESTRICTED-EXACT-POSITIVE-MARK-TRACE.md SHA256 98a40e1ba029cd5c09c59a011dd9bbc2f7b798ac3ae13b9578e6829aa111139c.
* Aligned norm construction, forward-quadratic-norm-marked-lift-r1/README.md SHA256 3b90b89e9203c11bad6212ac316e1e00c9ab9998d4ace17f7e9cd41e0b5222f7.
* Actual common producer forward-fixed-window-gaussian-order-producer-r1/ORIGINAL-318-JOIN.md SHA256 422fe47db714325de582134629ad8c7c2f9004dc94b834ae9d162eec203573a9; project source pin a0950ac7c24df6d336a196966fb790d6abd55e44.
* Independent fixed-fiber local proof is preserved byte-for-byte under local/, including its manifest 9be2a85e. This is mathematical source, not a Lean theorem or a global PointPair construction at any indexed pole.
