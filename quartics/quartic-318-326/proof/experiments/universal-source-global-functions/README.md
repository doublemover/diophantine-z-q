# Universal global functions and all-test rigidification

Five new sources prove the actual universal structure-sheaf isomorphism
O_T = (p_T)_* O for the original contact source over every Q-scheme test T.
The proof uses pinned Mathlib's genuine flat global-section base-change
theorem on affine opens and its actual sheaf affine-basis criterion. It
covers nonreduced and nonquasicompact tests and every original open.

For the actual contact field family and its exact section, every further
scheme test therefore has bijective section evaluation. Original relative
line classes admit actual rigidified representatives, and equal classes
have exactly one actual compatible isomorphism.

The complete twenty-six-source closure passed strict Lean 4.35.0 checks
and a private-inclusive recursive audit of **322 declarations**, using only
`propext`, `Classical.choice`, and `Quot.sound`. Twenty-one unchanged producer
copies close imports. The 680 baseline predecessors were reused from
verified artifacts, not freshly rebuilt. The unchanged constants producer
has one harmless style warning; the contact-section producer retains two
harmless unused-simp warnings.

Effective fppf object descent, degree zero and representability are not
asserted. See `APPLICATION.md` and `validation/receipt.json`. Independent
acceptance is separate.
