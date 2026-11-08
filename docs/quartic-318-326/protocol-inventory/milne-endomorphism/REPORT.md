# Milne I.10.15 correction and the actual V13 endomorphism field

Decision: **no mathematical repair is needed in the inspected V13 consumer**. Its faithful integral-homology argument already avoids the defective step in the old notes. The source/application record should explicitly bind Milne's corrected proof, rather than leave an unqualified reference to the original v2.00 proof. This is an independent bounded review of existing mathematics, conditional on the named abelian-variety, finite-cover and good-reduction inputs. No source or historical approval was edited.

## The correction, exactly

The official course-note errata credits Timo Keller with observing two flaws in I.10.15's proof: the module must lie in End^0(A), where the degree polynomial is defined, and choosing a basis for End^0(A) prematurely assumes its finite dimension. Shaul Zemel's nearby observation concerns an earlier route to the rank bound. These are credited observations about Milne's notes, not verified people who challenged this project. The errata links a replacement proof at https://www.jmilne.org/math/CourseNotes/ProofOf1015.pdf.

The replacement works first with each finitely generated submodule of End(A), proves injectivity after tensoring Z_l, and only then gets finite rank. For a simple A, the degree-polynomial discreteness argument applied to a rational basis now proves finite generation without circularity. Isogeny decomposition handles general Hom(A,B). The theorem's statement is unchanged. Milne's corrected January 2, 2022 reconstruction of the 1986 chapter has the corresponding Theorem 12.5 and the same repair. It is a corrected author reconstruction, not a newly inspected publisher-typeset copy.

## The actual six-contact consumer

V13 lines 599–605 specify a normal number field K and an actual abelian surface A/K. Lines 620–638 form W0=Res_(K/Q) A, of dimension 2[K:Q], and use its **geometric integral endomorphism lattice**. Fix an embedding Qbar into C. An algebraic homomorphism acts on the lattice Λ=H1(W0(C),Z). Its analytic lift is complex-linear, so vanishing on the full lattice forces the map to vanish. Consequently

End(W0_Qbar) → End_Z(Λ)

is injective. The target is free of rank (4[K:Q])². A subgroup of a finite free abelian group is finite free. Therefore r≤16[K:Q]²≤16F0². This is stronger for the present characteristic-zero purpose than an injection merely into a Z_l-module, which alone would not prove integral finite generation. The manuscript already says “faithful integral-homology realization”; no replacement of its argument is required. Milne I.2.1–2.3/2.9 provide the torus/lattice interface. No canonical action of every Galois automorphism on this one fixed Betti realization is assumed.

Choose a finite Z-basis of the actual algebraic End lattice. Each basis morphism uses finitely many algebraic coefficients, so all are defined over one finite extension. Thus its algebraically defined Galois image is finite. For a finite-order integral matrix M congruent to1 modulo3, every eigenvalue ζ satisfies (ζ−1)/3 integral. Milne I.14.5 forces ζ=1; characteristic-zero finite-order matrices are semisimple, hence M=1. Reduction mod3 is therefore faithful on the finite image. It follows that [E:Q]≤3^(r²) and [EK:Q]≤F0·3^(256F0^4), exactly the printed D, without a new factor.

At p outside T, K is unramified and the conjugate surfaces have good reduction. Choose l≠p. The induced Tate representation of W0 has trivial inertia, since inertia fixes the embeddings of K and is trivial on every summand. Its conjugation action on actual End is trivial by faithful Tate realization (Milne I.10.6 already suffices). The kernel field E and L=EK are unramified outside T. Over K the actual Weil restriction splits into conjugate factors; G_K fixes their labels and G_E fixes the whole End lattice. Their intersection therefore fixes every ordered Hom group. These checks retain the prior geometric construction as an input.

## The five-contact companion and literal318 boundary

V13 lines6973–7000 use a separate field of degree at most576 coming from a marked fiber, not the preceding factorial bound. Once A,B and their full three-torsion are defined over that field, a homomorphism killing A[3] factors through[3], so Hom(A,B)/3 embeds in Hom(A[3],B[3]). The finite-image argument above applies to the actual Hom lattice; Galois acts trivially mod3 and hence trivially. The correction to I.10.15 changes neither this implication nor its constants. The marked-fiber, integral PEL model and good-reduction assertions themselves are not established by this lattice argument.

The literal318 arithmetic notes strengthen the later height estimate to49/8 and retain global source arithmetic as an explicit obligation. This review does not turn the inherited Hom-field lemma into a proof of the actual PEL/metric identification, the dimension-two image, that height, or any288-row witness. The proof-obligations document remains explicit about those boundaries.

## Exact versions and scope

The five selected V11 and V13 passages are raw-byte identical; hashes and line ranges are in manifest.json. The historical A061 decision and report are preserved with their original identities. The current reviewer is /root/restart_geometric_model; the recorded historical reviewer is only the named Astra-review description in that evidence, not a verified human identity.

Fresh readings used the official2008 v2.00 notes, live errata, linked one-page corrected proof and corrected2022 chapter through the official indexed source. Earlier direct downloads returned406; no fresh PDF byte equality or new published-typesetting comparison is claimed. Exact returned reading evidence is hash-bound locally and excluded from public packaging. IV.7.3's separate local-family erratum is not used in these arguments and remains outside this acceptance. This is not a broad Milne or whole-A061 source certification.
