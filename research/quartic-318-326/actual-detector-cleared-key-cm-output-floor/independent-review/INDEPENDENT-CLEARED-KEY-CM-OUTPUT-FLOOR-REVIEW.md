# Independent cleared-key and paired CM output floor review

**PASS for the literal construction and the stated enumeration scope.**
The exact author checksum list is
`7c2162992ae134bbfdefa9679bd02ed2e5d6021d4865756c3eb17ba630dabd46`;
the paper is `d1c85d4af8d8a2f0b7afd79407b25f6a3da5f04afd7d56a6c7cfa004780eb14f`.
The checker `5725abe941d52766fc87ed03a3ce593c1ee7ebad55eaf495fae9f3a03c264094`
reproduced `31c267298d4703019e274050639eeaa0521c15e24139daefa6269cedb4324b9b`
byte-for-byte. All author hashes verified.

I retrieved the published Gaussian-selection body by exact bytes
(`29e5419420d73d1699801548e411527e265378ebd22bde95d7f7653d59fbc3e0`)
and checked the exact source for clearing and the unscaled original
row 190. The slope at minus one forces the ratio of clearing to
any nonzero scale to be integral. The nonintegral roots force
divisibility by 2, 11, 37, and 2399. Clearing row 190 also puts these
primes into the common base independently of the chosen detector.
I independently reduced and factored all ten differences of the five
literal rational roots; the stated lower bound only needs the four
positive differences from the largest root.

The base Gaussian ray includes the cyclotomic field of conductor
equal to its integer modulus: norm character on ideals, trivial on
principal generators congruent to one, and modulus divisible by 16.
Its conductor divides the maximal rational abelian conductor, which
divides the literal key's Q. The 13/19-refinement really puts both
primes into the old base. The norm of a Gaussian generator congruent
to (9,0) mod 16 is 17 mod 32; combining with the exact other norm
conditions gives 8977 mod 11424. Both distinct genuine primes q and
the prime at the largest root lie on that ray. Bounded trial division
and the four remaining exact gap identities give the squarefree
twist/discriminant floor above 2.78 times 10^179 for both members.
It is an envelope, not a realized smallest key. The relaxed envelope
still exceeds 5.14 times 10^126 only if the same genuine row ray and
protected negative depths are retained; no construction for that
relaxed premise is claimed.

I checked the printed original [Tatuzawa theorem 2, p. 164, and class
number formula (1)](https://www.jstage.jst.go.jp/article/jjm1924/21/0/21_0_163/_pdf).
For fixed epsilon in (0, 1/2), at the precise max-threshold stated in
the paper, the primitive real character bound is strict and permits
one exceptional character. The selected negative fundamental
discriminants have the correct primitive conductor and unit count
two. Exact integer comparisons with pi < 22/7 give more than
8 times 10^85 characteristic-zero CM class indices on at least one
arm of each distinct pair. For a repeated pair the conclusion only
holds across the two distinct admissible choices of new final prime;
it does not resolve the one fixed pair. Genus halving reduces this
record count by two, not to a count of distinct finite labels. I also
checked the separate norm-coordinate interval count and the local
matrix precision-loss example.

These are barriers to the specified output or direct trial loops,
not complexity lower bounds for all algorithms or a barrier to an
aggregate/order-three certificate. No literal numeric key, no actual
CM coefficient, and no point or rank are produced.

Signed: independent paper and exact-byte reviewer, 2026-11-21.
