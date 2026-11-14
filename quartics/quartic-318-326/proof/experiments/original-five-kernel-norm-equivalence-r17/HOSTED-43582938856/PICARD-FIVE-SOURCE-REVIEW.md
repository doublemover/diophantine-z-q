# Independent Picard tensor-multiplication source review
Reviewer: lean_review_resume; internal source comparison only.

Observed proof run43582938856 at6fe85071934d36d22cfdbd7c503f6b9a54e6ef18, artifact14109303935, ZIP93d1efa164eb4f2b3a52adeb0ac4b9cc59375322ad56674620cd2a19024fffc8. I independently matched GitHub run/head/digest, actual ZIP RESULT/log members, published predecessor intake/source, and candidate bytes. The later bbda workflow-only tip has the same production sources; its results are not substituted.

Candidate OriginalTensorTraceBaseChange318 changes only one simp-only list item: LinearMap.mul_apply'. Before756963fda9c0c01481ae77b95e8c7f144b03637b617fc0f2ed662e3a6c6d30ef; afterf47c9797b6c7be59d7bc2c29a3a6ec3dce6b7ac43bf9e6f5b8d5d10cf1c01cd3.

The exact hosted hard goal in the tmul branch retains LinearMap.mul on both sides. The existing explicit LinearMap.ext now leaves a tensor variable, and full zero/tmul/add induction remains intact. The deprecation warning is not the hard error and does not justify altering the induction API in this repair.

I independently fetched Mathlib pin56a005855ea17e0b0958f73ec801ae140b0a1679 Algebra/Algebra/Bilinear.lean, blob e9748290daf0410f8e131703d2d90be0423e58dc. Its exposed public LinearMap.mul_apply' at49 is exactly mul R A a b=a*b, proved rfl. It applies to BOTH displayed multiplication-map applications. With existing tmul_mul_tmul and one_mul, the left product (1⊗s)*(a⊗t) becomes a⊗(s*t), equal to the existing baseChange_tmul result. All required module/tower structures are those already supplied by the same commutative algebras.

Every commutative R,S,A with Algebra R S and Algebra R A remains quantified. Multiplication covers the ENTIRE tensor module through zero, arbitrary pure tensors and sums, not only coefficients. Free/finite R-module assumptions on S remain confined to the original trace/norm results. Arbitrary base A, including nonreduced square-zero test algebras, is retained. No characteristic, separability, flatness, basis, nonzero or reducedness premise is added.

The resulting endomorphism is literally multiplication by the original 1⊗s, equal to scalar extension of multiplication by s; it is not a conjugate or isomorphic substitute. Same-file trace and norm use that exact equality with original native trace/determinant base change. norm_infinitesimal retains every e with e*e=0, same Units.map norm and trace coefficient.

I read actual downstream OriginalRightTensorNormTrace318.norm_coefficient and norm_infinitesimal. Its commRight transports this same left tensor algebra to S⊗A with A acting on the RIGHT; the original coefficient becomes s⊗1. No tensor flip, scalar factor, norm direction or sign is silently dropped. SquareZeroNormTrace's original epsilon-square and norm-infinitesimal map remain unchanged.

All imports, public statements, options/resources, induction branches and consumer bytes are unchanged. The source is supported as a bounded observed-frontier normalization candidate. No Lean/Lake build, kernel proof, recursive axiom audit or whole-packet/theorem acceptance was performed. New packet-specific nine-obligation APPLICATION/README and propagation have not yet been accepted by this candidate-only report.
