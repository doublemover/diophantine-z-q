# A degree-two projection forces companion degree divisible by four

Keep the same fixed archived input-zero raw equation

    W² = δ f(t) f(t′),      f(t) = (t² − β)(t² + 3β),

with β = 204618888056724185 and the literal positive δ. The exact preceding input holds: β and δ are nonsquare and [δ] differs from [β]; see the published degree-(2,4) proof's archived applicability section, with its 181 and 17 checks. Nothing here changes the archived scalar. If nonconstant rational functions t,t′ on a rational line over Q satisfy this identity and deg(t)=2, then deg(t′) is divisible by four. In particular (2,6) and (6,2) are excluded. The surviving multiples of four above the separately excluded degree four are not treated here.

## 1. Homogeneous fibres and branch assignment

Use the preceding degree-two involution theorem: with the same fixed nonsquare δ and nonisogenous-over-Q elliptic targets, the sole possible branch has M(t)=(t′)²=P/Q of even degree d=deg(t′), W in Q(t), and Q(z)=Q(t)(sqrt(M)). Write P,Q as coprime binary forms of degree d and use A=t²−β, C=t²+3β, both homogeneously. As the degree-two cover of the t-line has genus zero, it has exactly two odd places of M. Each of P,Q has an even number of odd zeros (its homogeneous degree is even); disjoint supports force one side to have none, hence to be a nonzero rational constant times a squared binary form. Infinity is counted in these statements, and P,Q and the branch fibres below are nonzero because M is nonconstant.

Put F=P−βQ, G=P+3βQ. The odd-zero sets of F,G partition the four distinct roots of AC; they are disjoint by coprimality. Rationality means each of the two irreducible quadratic pairs goes into one of the fibres as a full pair. At any of the four roots, both P and Q are nonzero: otherwise F or G vanishes there and so do P,Q. The square identity gives δ times the two rational scalar factors a square. Thus the separate assignments are (F,G)=(δ A L²,C S²) or (δ C L²,A S²), after a common scaling and absorbing a rational square. The combined assignments are (δ AC L²,S²) or (S²,δ AC L²), with degrees of L,S dictated by d. This exhausts all repeated-root patterns since remaining multiplicities are even. In particular no assumption that the extra square factors have distinct roots or avoid infinity is made.

## 2. The separate assignments are impossible

Over K_R=Q(sqrt(β)) (at a root of A) and K_I=Q(sqrt(−3β)) (at a root of C), evaluate the same formulas P=(3F+G)/4 and Q=(G−F)/(4β), as in the published degree-(2,4) case. For the first assignment either possible square side has classes respectively 1 and δ in these fields. For the exchanged assignment the square side Q has classes −δ and −1, and the square side P has classes 3δ and 3. Nonzero opposing factors at the evaluated roots are guaranteed by coprimality, even in the higher degrees. Consequently the rational scalar of a square side can exist only if [δ] is in the subgroup {1,[β],[−3β],[−3]}, the product of the rational-class kernels of restriction to K_R and K_I. Since δ is positive, nonsquare and distinct in squareclass from β, this is impossible.

## 3. The combined assignments force even half-degree

In either combined assignment the evaluations at roots of both A and C give the identical square-side constraints of the degree-four proof. Indeed if F=δ AC L² and G=S², then at all four roots (P,Q)=(S²/4,S²/(4β)). If F=S² and G=δ AC L², then (P,Q)=(3S²/4,−S²/(4β)). In both cases S is nonzero there. The two restrictions on rational squareclasses have joint kernel trivial, so the four possibilities and their exact identities are:

| F, G | square side | exact product |
|---|---|---|
| δ AC L², S² | P=U² | (2U−S)(2U+S)=3δ AC L² |
| δ AC L², S² | Q=β U² | (S−2β U)(S+2β U)=δ AC L² |
| S², δ AC L² | Q=−β U² | (S−2β U)(S+2β U)=δ AC L² |
| S², δ AC L² | P=3 U² | (2U−S)(2U+S)=(δ/3) AC L² |

Here S and U have homogeneous degree d/2 and L has degree d/2−2. Both factors on the left are nonzero, since the product on the right is nonzero. They are coprime: in every row a common geometric zero would make S=U=0, and hence make two independent linear combinations of P,Q zero, contrary to coprimality. This also excludes a common zero at projective infinity. In the UFD Q[X,Y], each irreducible power in the product on the right contributes an even degree: both A,C have degree two, and all other exponents are even coming from L². This remains true when A or C also divides L. By coprimality each such power lies wholly in one of the two left factors. Each left factor therefore has even degree, so d/2 is even. This proves the claim for every surviving degree-two structural possibility.

The raw identity is symmetric under exchange of t,t′, so the same divisibility holds when the second projection has degree two. There is no conclusion here about degree (4,4), about a higher multiple of four against degree two, or about any rational point in an individual archived fibre.

## Exact published dependencies

Both original inputs are at immutable Git commit `5de0f863bd8a0e1cefd97c5141d33e1bdb08ba0b`, [publication scope](https://github.com/doublemover/diophantine-z-q/tree/5de0f863bd8a0e1cefd97c5141d33e1bdb08ba0b/research/quartic-318-326/actual-archived-raw-degree2-parity-and-bidegree24): the degree-two involution/normalization paper in `author/parity`, SHA-256 `1c0c092014b87dd880429dbff3bb50be31ec4d221e3f671cc06883cabece5a42`, and the degree-(2,4) four-constant/archived applicability paper in `author/bidegree24`, SHA-256 `670957fc9459daec6a7a74ea54dcad60cd96f79220e9c46a1ba15b44d3b64564`. Their checksum-list digests are respectively `c6e665f9b125fbebce4e08cd3599fdb566918d3b23f8e0d961175011345eef03` and `0ffb817600e4dd9f227c197f8d3a78c99b2774ff7d76ecf22d547b4e2a88c6ee`.
