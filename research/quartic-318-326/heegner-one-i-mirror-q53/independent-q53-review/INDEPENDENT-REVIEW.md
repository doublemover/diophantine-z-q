# Independent review: exact ordinary mirror q53 principal relation

Reviewed immutable note SHA-256:
- Local chart: 2259c61ccd4a2ffcf45776ce1bd58c25eb6de4f2448122c841ebd399ba95e470.
- Signed norm and small places: 50e3b176afb65c9615b2b0bd1495198dde1fd52cb913938309e2512292ef7a96.
- Complete composite ideal: 85fa0a6d30b774d42a5a4554576daf589837aae9983fd86dbbb784b3999183d2.
- Exact fixed-row nonsmoothness: 7442d0d89b928a987e2d23d022c121d4a5d4b96b180fbb2927f0c3e4d11e234d.

All exact author local, norm, small-support, relative polynomial
and 150M sieve JSONs reproduce. As an independent norm check,
I split the actual x polynomial over seven good residue fields
53,131,157,313,521,547,677, computed normalized y multiples using
literal finite-field elliptic additions with y_a=c_a y_1, then
took sign-pair products and finite-field norms. This avoids
differentiating division polynomials or computing a resultant.
All seven agree with the full signed norm. The separate script
takes the directory containing the exact original point-field,
ordinary q53 and q53 global-norm packet folders. Output is archived.

The norm formula's derivative sign and factor follow from
[a]^*(dx/(2y))=a dx/(2y). The Gaussian terms from opposite points
subtract with no factor of two or twelve. Both degree-168
fields are cyclotomically disjoint, and their actual common
base change computes the same determinant, not just its
twelfth power. The relative even Gaussian polynomial is
a degree-six polynomial over the line field before substituting
Z², so the degree-84 x-trace is divided by six, not twelve.
Its exact independent degree-14 resultant gives the same norm.

At 53 the exact Hensel residue establishes the valuation one
at the chosen degree-13 prime and no other support at 53.
At 5303 the simultaneous minus signs on W and ζ exponents
produce the actual rational mirror residue and the norm
forces one degree-one factor. At 3 the free twelve-orbit
Tate residues give valuations (0,3,0,1,0,0,0,0,2,0,1,0).
The inverse-dilation ξ weighting gives 4 mod 13. Each of the
other four primes has nontrivial relative stabilizer and
vanishes under faithful projection. The twist prime 17 is
killed by the central −I as well.

For every p|C, the nested monic roots at the line and mirror
levels have invertible derivatives, and all denominators are
units, as is 6d·13. The compatible simple roots give actual
embeddings into Q_p. Restriction to the maximal order lands
in Z_p by integrality, so yields a surjective reduction
mod p^v(C). Its degree-one prime power contains the literal
principal element, and equality of local ideal norms forces
it to be the whole p-divisor. No global index or maximal
power-basis assumption is used. The degree-one prime has
trivial relative stabilizer, since a local automorphism of
Q_p over Q_p is identity. C^4=24 mod53 ensures that some
support exponent survives mod13; distinct rational supports
cannot cancel. This proves a nonzero projected divisor,
not a nonzero ideal class.

The relation is eξ[q53]+4eξ[q3]+eξ[q5303]+eξ[I_C]=0 in the
ordinary faithful class quotient. All 8,444,396 primes through
150,000,000 were checked and none divides C. That obstruction
is specific to this exact row; it neither excludes a
different reduction nor computes generation, rank, or Selmer.
The prior GRH generator comparison remains conditional;
the present exact divisibility computation does not use GRH.

Independent reviewer: Vesper (high_review_ci), 2026-11-21 UTC.
