# The first off-diagonal direction chart over the selected mixed raw corner

Keep the same actual compact sharp input-zero source, literal 19-unit detector scale, and mixed plus primary-1 × opposite alternate-1 intersection. Work at the raw collapsed corner X=Y=0 of its stage-12 transition. This note covers only the first horizontal blowup chart with off-diagonal unit direction. It does not cover the diagonal descendants or either coordinate end of that blowup.

Use the exact poles as in the true-infinity proof. If π=19 and Z is the actual shared weight, write w=√(Z/π^(2d)) after finite unramified constants, where 2d=v₁₉(Z). Then

    U=π^d w p₁^+,      V=π^d w a₁^−,     r=1/U,      s=1/V

are the true scaled poles and their reciprocal relative coordinates, not just residue formulas. Blow up the horizontal ideal (r,s), and in its r-chart put λ=s/r. Take the open in which λ and λ−1 are units; at the geometric exceptional line over π=r=s=0 this means the directions other than 0,1,∞. Set Q=1−1/λ, also a unit. Now U−V=Q/r and U=1/r exactly. The regularity of the coordinate chart follows étale-locally from the actual r,s simple pole coordinates.

The stages through 11 in both folds are regular, and the plus stage 12 has the exact strip

    r² f_(12,+) = Q² + r² f_(11,+)².

The next three additive terms are regular in this off-diagonal open, so the consecutive strips at stages 13,14,15 restrict along r=0 to Q⁴,Q⁸,Q^16. The remaining square gives Q^32. The only other polar term is the last weighted J-leaf, whose square root at this scale is

    π^d w(5P₀²−1) − 2P₀²/r.

Its squared pole has order two and therefore contributes only r³⁰ times an integral term in the final strip, not to Q^32. Thus the exact functions

    F=r^32 f_+,      G=f_-,       H=F+r^32G

are all regular and units at the named geometric exceptional open: F and H restrict to Q^32 along r=0 there, and G reduces to 1 because neither pole feeds that opposite fold. Consequently the exact contact function

    c_fold = κ F G/H

is already regular and divisible by π^e, with e=v₁₉(κ)>0. In particular δ=1−β c_fold² is a unit reducing to 1. There is no balanced contact direction here, no residual positive-genus cover, and no use for the optional parity of e.

The normalization is finite étale over this regular neighborhood and splits into its two rational sheets when restricted to the geometric off-diagonal open of the exceptional λ-line. That line is the actual fibre over the original raw point: the coordinate blowup is pulled back from the universal horizontal blowup by the original étale coordinates, so the geometric fibre at the chosen base point has precisely the usual parameter λ. A rational target map extends to the good elliptic scheme by BLR extension; it is constant on each of the rational λ-sheets. The proper main graph argument then prevents a nonconstant elliptic image of any component centred in this open direction chart, including ones dominated by further modifications above it. This does not rule out components lying over λ=0,1,∞ or new centers in those omitted directions.

Exact binding: mixed pole strip manifest b6cac3561eaf495332b35cd62ba95b0b6deadfd038a3ede16951f61d4a980d0f; true-infinity exact reciprocal pole and weighted J identity list 0c23f97db63715427e3c64265bb48e8b1f470d0838f5fd73fb1c664a4518752b / note 5678be43d86feaa64d675e37111083de61291b49479ce3ef0c2949ae4646e300; good ordinary targets list e9a3423e5bf681944b8a70529990763bfce3f8e2db92fe8b1b5bdb64fb4b9e7f; [BLR, Néron Models §8.4 Cor. 6](https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf). No residue search, key construction or global map conclusion.
