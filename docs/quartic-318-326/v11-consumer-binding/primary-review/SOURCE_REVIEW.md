# Independent source check of the Version 11 Kato interface

Reviewer: /root/restart_group_law. Date: 2026-11-08.
Decision: no correction required to the narrow V11 index, norm and retained-class repair. This is a fresh scoped internal mathematical review; the separate 318/326 contribution binding remains pending its final candidate and downstream trace.

## Scope and provenance

This reviewer did not author the V11 application or the proposed 318/326 binding. The task is the exact enlarged-index, transition-map and limiting-class interface, not a new validation of every antecedent in the restricted converse. The actual V11 source, its application contract, and its construction/application/K15 spans were read. All recorded hashes match. Historical evidence files were read as evidence of what was previously argued, not as a substitute for today's source check.

The original Kato1999 PDF was freshly fetched from the publisher and its SHA256 is exactly 483dc18c56b2fe9cfac4e37f2e6594399625c3f0ea98a05bb69116377c67fc06. Sections0.1 and0.4–0.8 were read from the extraction, with printed pages314 and318 also visually checked. The original Kato2004 PDF was also freshly fetched from the publisher, and its SHA256 exactly matches 3c6e14b11fa60262db8aff782ce3cf4d83e9100c0be83621a7e4ce502cec605d. I read (5.1.1), (8.1.2)–(8.1.3), Section8.2, Sections8.9–8.11 and Proposition8.12 from the publisher text and local extraction, then visually checked printed pages180 and186. The direct PDF and visual checks corroborate the previously accessed publisher-indexed text. Source URL: https://www.numdam.org/article/AST_2004__295__117_0.pdf .

## Required domain and actual constructed domain

Kato1999 Definition0.1 fixes a modulus containing the coefficient prime and all representation ramification, and a coprime excluded modulus. It requires all positive multiples of the first modulus coprime to the second, not merely indices whose intersection with a fixed prime set is {2}.

In V11, N is the fixed elliptic conductor, D=2^a d is the primitive quadratic conductor, and d divides F. The K5 smoothers c=d_s=1+2^e·3N_oddF are odd and prime to Nd. Thus N_K=2Nd and N'_K=c d_s satisfy the coprimality requirement, and the representation T tensor chi is unramified outside prime(N_K). The expanded K8 defines every positive m coprime to N'_K, so the whole required domain is included. The old 2004 index family is explicitly a subfamily. Powers of2 in D need not divide N_K: ramification support is the condition, while every actual upper field retains full D.

## Transition computation

Take any admissible m and any prime ell not dividing N'_K. Then mell remains admissible. If ell divides m, S_Dmell=S_Dm, including dyadic, bad and twisting primes. The stated original-class norm law therefore has an empty product.

If ell does not divide m, N_K|m forces ell outside2Nd. Hence ell is a good odd prime, unramified for chi, absent from Dm, and the difference of supports is exactly {ell}. The weight-two, r=1 polynomial is 1-(a_ell/ell)sigma^-1+(1/ell)sigma^-2 before twisting. The corestriction equivariance identity sends its linear term to -(a_ell chi(ell)/ell)sigma^-1 and leaves the quadratic term unchanged because chi²=1. This is precisely P_ell(ell^-1 sigma^-1) for P_ell(X)=1-a_ell chi(ell)X+ell X². Arithmetic Frobenius defining P and the inverse cyclotomic deck element in its argument have different roles. No good-prime polynomial is needed at a ramified prime.

The primary2004 statement has now been checked: Proposition8.12 requires m|m', S union prime(m') contained in S', and exclusion of smoothing primes from S'. It gives precisely a product over S' minus S. These hypotheses hold in each use above. Formula8.1.3 inherits8.1.2 and5.1.1: the source allows any positive level, S contains the level/modular support and2, the smoothers avoid S and6, and d_s is prime to N. K5 supplies all of these, including at the newly admitted bad-prime levels. Here k=2,r=r'=1, so the target Tate twist is1. Section8.9 supplies an integral induced target for the SL2(Z) symbol construction, and8.11 projects to the original fixed newform lattice. Integral linear combinations of the fixed symbols preserve the maps and relations.

## Exact limiting class, not proportionality

For n≥1, the construction supports at DN_K2^n and D2^n both equal prime(2Nd). Thus the inner original-class norm has no new Euler factor. There are two paths from Q(zeta_DN_K2^n) down to Q(zeta_2^n), through Q(zeta_N_K2^n) or Q(zeta_D2^n). Corestriction transitivity equates the paths. The character is trivial over the second upper intermediate field, so tensoring commutes with that inner norm. Substituting K8 gives cor(y_N_K2^n)=y_2^n.

No linear disjointness is used. This is norm of the actual upper class, not norm of a restriction, so there is no extension-degree scalar. These levelwise equalities commute with transition maps. The tail n≥1 is cofinal. Taking divisor1 in source Section0.4, its Section0.7 norm-defined class is therefore the full-cohomology image of the actual retained dyadic class, after the single fixed lattice map if needed.

A common multiplier2^c_E commutes with every construction and transition. At exactly the height-one primes used,2 is invertible; thus it does not alter the localized coordinate ideal J. This does not assert an unscaled integral class equality between different lattices, does not divide out a smoother, and does not replace the supplied class by an arbitrary rank-one generator.

## Consumer and limits

Kato1999 Theorem0.8 bounds the local-restriction kernel H²_0 and the coordinate ideal of its own supplied nontorsion class. The V11 repair identifies that class before invoking the retained nonvanishing and full/j_* comparison arguments. The separate positive-complex integral assertion and central calibration are not consequences of the away-from-two theorem.

The proposed active 318/326 documentation should bind to this V11 repair while preserving the historical V10 pin. Its exact RC→pole→final-witness trace is being supplied by another reviewer. A final contribution acceptance must bind both that trace and the whole resulting documentation bytes. Further global group-law proof development is not a prerequisite to checking this narrow Kato interface. No global restricted-converse or integer-to-source-existence closure is asserted here.

## Binding checked

V11 manuscript SHA256:1210d2e6f409e502fc9c95afc248fac16a9df48c760a396143780c20ec80b662. V11 source application contract SHA256:bb725ef321d28b2cdfeac64fa86deb864c09590d49e5fe05b9bdb95f73986e0b. The construction span12307–12448, application12670–12780 and K15 consumer12619–12669 match their contract hashes. This new review is independent of that contract's listed authors, but remains an internal model review, not human peer review or a formal proof of Kato's theorem.
