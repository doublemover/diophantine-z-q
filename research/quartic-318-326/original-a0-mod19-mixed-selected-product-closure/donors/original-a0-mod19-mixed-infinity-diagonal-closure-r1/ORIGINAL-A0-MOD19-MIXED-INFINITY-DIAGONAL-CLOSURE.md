# All descendants over the first diagonal direction of the selected mixed corner

Keep the same actual compact sharp input-zero source, literal 19-unit scale and selected plus primary-1 × minus alternate-1 intersection. Use the exact reciprocal pole coordinates r=1/U,s=1/V and the first horizontal blowup (r,s) of the true-infinity proof. This treats the entire geometric direction λ=s/r=1 of that blowup, including its subsequent horizontal exceptional orbits. It does not treat λ=0 or ∞ or any other source-boundary corner.

## 1. Exact fold polynomial and a proper horizontal fan

Near λ=1 set Q=1−1/λ; it is a regular parameter with r and U−V=Δ=Q/r exactly. The chosen point is π=r=Q=0 with π=19. As before G=f_- is regular and reduces to 1. The only pole input into the plus stages through 15 is the alternate-primary shared leaf12, whose exact output is f_(11,+)^2+Δ². Squaring successively and adding the regular leaves gives the exact form

    f_+ = Δ^32 + Σ_(j=0)^15 b_j Δ^(2j) + (H−M/r)²,

where each b_j is integral in the regular chart, H=π^d w(5P₀²−1) is regular, and M=2P₀² is a unit. The coefficients can simply be taken from the indicated squaring recursion, so this is an identity with actual functions even when those coefficients themselves depend on r,Q. The last term is the separate native J-leaf, not another degree-32 term. The square root w of the stripped common weight is the same fixed unit as in the true-infinity proof.

In the nonnegative (r,Q) order lattice take the regular fan with consecutive rays

    (1,0),(2,1),(3,2),...,(16,15),(1,1),(0,1).

Every adjacent determinant is 1. Explicitly it is obtained by blowing up the horizontal coordinate pair for the first ray (1,1), and successively subdividing the cone between the latest (n,n−1) and (1,1); its sum is (n+1,n). Thus it is a proper sequence of regular coordinate blowups, constructed integrally over the DVR and then pulled back by the original étale chart. The geometric fibre over the fixed other-base coordinates and (π,r,Q)=0 is the usual horizontal toric exceptional fibre, a chain of rational curves. In particular no étale extension of the variable function field is inferred from the use of étale coordinates.

The primitive ray (16,15) is the exact balance wall 16b=15a for a ray (a,b), where the degree-32 term and J pole meet. All other rays, and the open charts between them, are treated next.

## 2. Unit strips on the two sides of the wall

On the side 16b≤15a use the regular multiplier D_1=(r/Q)^32 and set F_1=D_1 f_+. Here r/Q is regular and has positive order on every nonzero ray of this side. The normalized leading formula is

    F_1 = 1 + Σ b_j (r/Q)^(32−2j) + (r^15/Q^16)² (Hr−M)².

All ratio monomials written here are regular on the side. Each summand in the sum vanishes along the fibre over the original r=Q=0. The secondary ratio r^15/Q^16 vanishes at any orbit with an active ray having 16b<15a. Thus on every such orbit F_1 reduces to 1 and is a unit, while D_1 reduces to zero.

On the side 16b≥15a use D_2=r² and F_2=D_2 f_+. The normalized formula is

    F_2 = (Q^16/r^15)² + Σ b_j r² (Q/r)^(2j) + (Hr−M)².

The lower exponent in direction (a,b) is 2a+2j(b−a) ≥ (2−j/8)a, and is nonnegative; it is positive when a>0 for every j≤15. At a point over r=0, some active ray has a>0, so the whole lower sum vanishes. The monomial Q^16/r^15 is regular and vanishes at any orbit with an active ray of strict sign 16b>15a. At every such orbit over the original point F_2 reduces to bar(M)²≠0, while D_2 is zero.

In either strict case the actual contact is

    c_fold=κ F_i G/(F_i+D_i G).

Its denominator is a unit and it is divisible by π^e with e=v₁₉(κ)>0. Hence δ=1−β c_fold² is a unit and the normalization splits over the geometric exceptional orbit; it is already étale in the regular total space. This includes intersections of the wall divisor with either adjacent strict divisor, since the active rays there include a strict one. There is no nonrational Kummer residual curve on either strict side.

## 3. Balanced orbit and proper graph comparison

On the open orbit of (16,15), use R=r/Q and K=Q^16/r^15. The two strips agree by F_2=K²F_1 (and D_2=K²D_1), with K invertible. At R=0 their leading quotient F_1 reduces to 1+bar(M)²/K² and can vanish only at the two genuine K=±sqrt(−α), α=bar(M)². At all other points this is again the unit/étale situation with rational open orbit sheets. At *each* of the two roots the exact true-infinity proof applies on this very chart (its derivative in K is nonzero for either sign): the completed/étale normal equation is A B=π^(2e)R^64, with a proper regular peeling resolution and rational geometric fibres above the named point. This invokes that precise previous mixed normalization formula; it does not infer normality solely from this leading residue.

The strict and balanced orbit list is exhaustive for the fibre of the proper horizontal blowup sequence over λ=1, π=r=0. At every regular split open, a target morphism is constant on each sheet above an actual rational exceptional curve, and in the two remaining localizations the resolved geometric fibres are rational. BLR extension to the actual good elliptic target and proper image in the main graph give no nonconstant elliptic image over this direction. More explicitly, the main graph on the proper refined base maps onto the original local graph, and the named regular local models have proper image containing the generic graph over their localizations. One need not assume arbitrary auxiliary resolutions glue. Thus no elliptic quotient is supplied by these geometric fibre components, not merely an estimate of their genus. This local exclusion uses no parity of e and does not address an unrelated raw corner or the remaining coordinate ends.

Exact pins: original mixed strip list b6cac3561eaf495332b35cd62ba95b0b6deadfd038a3ede16951f61d4a980d0f; exact reciprocal stage and true infinity normal toroid list 0c23f97db63715427e3c64265bb48e8b1f470d0838f5fd73fb1c664a4518752b / note 5678be43d86feaa64d675e37111083de61291b49479ce3ef0c2949ae4646e300; geometric peel list 420987f3bca9ec216c000a21bf15071699e9135efbe7ca82d5c233d89272fdd7; actual good-target list e9a3423e5bf681944b8a70529990763bfce3f8e2db92fe8b1b5bdb64fb4b9e7f; [BLR, Néron Models §8.4 Cor. 6](https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf). No prime search, Frobenius computation, numerical key or point.

    sha256sum -c SHA256SUMS
    python3 -B check_diagonal_horizontal_fan.py | cmp - EXACT-DIAGONAL-HORIZONTAL-FAN.json
