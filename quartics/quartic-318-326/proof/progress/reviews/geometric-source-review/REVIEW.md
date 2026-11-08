# Independent review of the arithmetic source identification

Disposition: accepted as an informal arithmetic function-field identification, conditional on the explicit source geometric inputs stated in the reviewed note. No discrepancy found. This is not a kernel proof of the PEL source, its comparison map, or any integral model.

Reviewed file: `resumed-source-twists/SOURCE_IDENTIFICATION.md`, SHA256 `04bfa5384f69d5a58463193623c823cfc84be82e49b026e7028995cfd6ca6611`.

## Sources and historical separation

I read the actual v10 passage “Recovering the contact line from published quotients,” including its genus, inertia, rationality, and cross-ratio argument, in `diophantine-z-q/manuscripts/quartic_v10.tex`, SHA256 `9559b22cc581346da1b3150fa9b8dfb62cfb048f6aac0b866448ae7ae879ff38`. It already supplies the labelled branch configuration used here. I read González–Rotger Theorem 4.2 and Tables 2–3 and visually inspected the rendered printed p.939 from the PDF with SHA256 `e595d1a428f20e1c6b3695bc37be658ca12c517fb6600171f531fe931b796c3a`. The four Table 3 coefficient pairs and their identification as the actual Jacobians over Q are transcribed correctly.

The historical disposition is prior source inputs and prior branch justification found, with this note supplying the arithmetic twist connection. This review does not assert that no earlier packet contained that connection. Manuscript disposition remains pending: I made no manuscript or shared repository edits and do not claim this note has been incorporated there.

## Checked argument

For a faithful exponent-two group of order eight acting on a genus-one curve in characteristic zero, the origin-fixing quotient has order at most two, while the translation subgroup lies in E[2] and has order at most four. Both bounds are therefore equalities. Each residual nontrivial labelled inertia involution has a fixed point, so it is outside the translation subgroup and induces minus one on the Jacobian. This identifies the complementary-character double cover, rather than only its branch count.

The translation subgroup is the intrinsic full E[2] action; its quotient is defined over Q. The induced degree-four Jacobian isogeny has kernel E[2], hence factors multiplication by two to give a Q-isomorphism of the quotient Jacobian with E. The odd cubic double cover has a rational infinity point, so it is its own Jacobian after choosing that point. No rational point on the original genus-one torsor is needed.

The rational Kummer classification with two rational branch points yields each character field as Q(t)(sqrt(c_i(t-a_i))); four independent characters recover the full labelled W extension. The change t=x+centroid and then (x',y')=(C_i x,C_i y) gives coefficients (C_i^2 A_i,C_i^3 B_i). Since both A_i and B_i are nonzero, a Q-isomorphism of short Weierstrass equations yields C_i/d_i as a rational square. Thus the use of the actual Jacobians, rather than equality of j-invariants, is essential and valid.

I independently recomputed all four translated cubic pairs, their published coefficient scalings, nonzero discriminants, complementary constants, and rational square factors using exact fractions. Results are in `independent_arithmetic.json`. They give c=(-14,-6,42,-21), complementary products (5292,12348,-1764,3528), and square factors (630,2058,42,336)^2 relative to d=(1/75,1/343,-1,1/32). The complementary-squareclass map squares to the identity for four variables, so the recovered four classes are unique.

## Accepted scope and outstanding work

Within the stated characteristic-zero geometric inputs, the note proves the displayed arithmetic labelled Q(t)-function-field identification, and its constants match the primary source. It does not prove the integral regularity/semistability, controlled-field or good-reduction assertions; constants supported at a few primes do not imply those claims. It also does not construct the actual PEL moduli scheme, universal abelian surface, or formal Lean source comparison. The finite-etale auxiliary open-j and torsion constructions must not be silently identified with the PEL object.

## Recomparison of the frozen current revision

The producer subsequently froze the note at SHA256 `44cbabb45a33e086230fd3e86315a2d825f902ef6ce0a85fca58dbf5ae6c808f`. I reread that revision and compared it with the exact earlier reviewed content. Reconstructing the earlier content reproduces its original SHA256; `recomparison.diff` records the only two changed paragraphs. The geometric argument, hypotheses, arithmetic numbers, and source citations are unchanged. The changes report the producer's successful four-module, 90-declaration replay and extend the description of its Lean algebraic conclusion.

I read `SourceTwistFieldEquiv318.lean`, including `scaleEquiv`, `fourRootEquiv`, and `source_equiv_of_published_scalings`, and the producer's audit result. The final theorem indeed takes explicit rational coefficient scalings and constructs an actual Q(t)-algebra equivalence between the two tensor root algebras. The field interpretation is the existing independence result for these contact parameters, not a constructed PEL source. The revised wording preserves that boundary. My acceptance of the informal arithmetic identification applies to this current frozen revision as well. I have inspected the added Lean theorem's statement and construction but have not independently recompiled the four producer modules; the 90-declaration kernel/audit result remains producer verification, not a new independent replay claim.
