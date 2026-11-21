# All 17 previously local-pass fixed-b candidates fail before higher descent

Use the literal fixed b=10568037907556089, t=1/2399,
λ(u)=(16u⁴+24u²+1)/(32u²) and C_u as in the preceding
`ct-fixed-b-scalar-prefilter-r1` proof. These are the same 17
closely specified candidates from Joined's existing local-pass list,
not every u≤8,000,000: the wheel used a particular nonzero unit phase
and this note does not claim coverage of possible omitted phases,
other numerical ranges, parameter choices, or other b.

Eleven of the 17 were excluded by the frozen one-scalar replay:
four globally inconsistent, seven single old contact-ball conflicts.
The six remaining scalar survivors are now all excluded by comparing
the exact two coordinates of the same torsor.

## Necessity and finite scope

Use the same L₀,L₂ as in the scalar proof and L₁ from the split conic
Z₀²−Z₂²+λH²=0 with its explicit rational seed
((1−λ)/2,(1+λ)/2,1). The two homogeneous functions are

    g₀=L₁L₂/H²,       g₁=L₀L₂/H².

Their even half-divisor classes are exactly T₀=(0,0) and T₁=(bt,0),
respectively. Any rational point on the literal C supplies the global
pair of étale double-cover fibers, even if it hits a tangent divisor.
The proof in the scalar packet applies to both coordinates:
outside the reconstructed good-prime support both fibers are
unramified, and over each finite p inside the support their actual
joint local image is a single affine translate of the literal
first-two-coordinate Kummer image on E(Q_p)/2. The two coordinates
are not allowed to choose independent local reference points or
independently vary within their marginal sets. The script uses a
single local α reference for both g_i and positively witnesses
all of E(Q_p)/2 in its pair representation (four at odd p, eight
at p=2), including the exact double-sign torsion classes. The
real place is not needed for this negative criterion. All required
checked finite primes had definite local rows; no local skips among
the six. All supports and arithmetic seeds are checked on literal
candidate values; larger primes use exact Pocklington certificates.

Thus the global affine system is a necessary condition for every
rational point. A witness for inconsistency XORs exact input rows to
(0,1). Its nonemptiness is not a rational point and is not a
4-cover existence or rank claim, because only a necessary system
was computed and real/contact and other conditions need not be met.

At a good old contact, if both root radicands and all needed
leading terms are stable on the full W mod p² ball, positive root
reps modulo p³ and the four relative signs give the exact possible
unit Legendre codes on that ball. We use code 0,1,4,5 for unit
pairs (component bits are 0 and 2). Stability is checked by
a p² error bound against each literal tangent valuation. Not
reaching the needed margin would skip the row, never exclude.

## Exact six dispositions

| u | Result |
|---:|---|
| 2749849 | No rational point in the required simultaneous old contacts; two exact balls suffice |
| 2891117 | Global affine contradiction, no rational point on this C |
| 3262241 | Global affine contradiction, no rational point on this C |
| 5685821 | Global affine contradiction, no rational point on this C |
| 5791843 | Global affine contradiction, no rational point on this C |
| 6162461 | Global affine contradiction, no rational point on this C |

For u=2749849 the finite necessary system initially has 32 solutions
(rank 21 in 26 variables). The **two** original balls at
(3162001,6437986254436) and (17590513,158682579241704) already
contradict every one, regardless of other old contact conditions.
Both have allowed code set {0,5}, i.e. exact equality of their
two local unit bits. The resulting rows are (26873040,0) and
(6947664,0) over the actual ordered support encoding in the JSON.
As a small independent linear certificate, first take the forty
existing finite local rows, append those two contact rows, then XOR
the zero-based input rows 11,19,20,22,26,28,29,40,41. The result is
(0,1). The script verifies that exact identity and also independently
replays enumeration of all the joint lift masks against the
certified ball codes. This is a simultaneous obstruction; the two
indicated cells alone separately are not claimed to exclude all.

Combining packets: nine literal auxiliary torsors have no rational
point by an affine inconsistency; seven more fail one old marked
ball; the last fails two old marked balls jointly. Therefore
none of this specified 17-element old local-pass list can play
the marked role. This does **not** prove an actual final pole,
give any rank, or rule out moving to a different parameter/chart.
It uses no Cassels–Tate perfection, 8-descent, or hidden validity
of a possibly selected source coefficient. In particular, in the
eight marked-only exclusions unmarked existence is left open.

Reproduce in the workspace:

    C=rc-native-helper-20261120/ct-fixed-b-scalar-prefilter-r1
    M=rc-native-helper-20261120/ct-fixed-b-two-coordinate-prefilter-r1
    args=$(jq -r '.[][0]' "$C/JOINED-LOCAL-PASS-INPUTS.json" | paste -s -d' ')
    python -B "$C/cheap_fixed_b_tangent_scalar_gate.py" $args | cmp - "$C/EXACT-SCALAR-GATE-JOINED-CANDIDATES.json"
    python -B "$M/replay_two_coordinate_prefilter.py" | cmp - "$M/EXACT-TWO-COORDINATE-SIX-SURVIVORS.json"

All arithmetic is exact and bounded with standard Python and SymPy;
no Lean compilation, remote writes or user-computer actions.
