# Independent source review: Picard tensor trace base change r16

Reviewer: lean_review_resume. Hosted evidence: run 43578868567, published base 977040de03da47698b89a3345d93e2ffcbc2220c. Source-only review, no local Lean/Lake/compiler execution.

## Verdict and exact scope
No source-level defect found in the bounded extensionality correction. This is clearance to package the candidate for hosted checking, not application, kernel, whole-packet, recursive-axiom or mathematical acceptance.

OriginalTensorTraceBaseChange318 changes from f9055364c7c7097fc0c7ca5ee89596d7f75e5d2dd7f286b14df9553d6e715c51 to 756963fda9c0c01481ae77b95e8c7f144b03637b617fc0f2ed662e3a6c6d30ef. Independently verified that replacing exactly `ext z` by `apply LinearMap.ext; intro z` (two source lines) reconstructs the entire candidate byte-for-byte. Imports, public statements, all original proof expressions after that introduction, options and budgets are unchanged.

## Actual error and primary API
The own predecessor log says the induction target z has type S, not a tensor, after the generic ext tactic. Its induction_on deprecation is a separate warning. The pinned Mathlib LinearMap/Defs excerpt (56a005855ea17e0b0958f73ec801ae140b0a1679, lines 205–221) gives ext from pointwise equality of the SAME semilinear maps. Explicit application therefore introduces z in the whole A tensor_R S domain rather than recursively applying tensor extensionality first. The retained old induction API has zero, tmul and add cases, matching the existing branches.

## Nine application obligations
1. Inputs remain arbitrary commutative R,S,A with the original R-algebra structures. Multiplication needs no extra finite, free, field, domain or reducedness premise.
2. The compared maps remain precisely multiplication by 1 tensor s on A tensor_R S and baseChange A of multiplication by s on S. No abstract replacement endomorphism is introduced.
3. Explicit extensionality covers EVERY tensor element. The unchanged zero/tmul/add induction covers zero, pure tensors and all sums, not only the right coefficient s.
4. The original tmul multiplication, one_mul and baseChange_tmul route retains the actual left A action and tensor orientation.
5. The exact endomorphism equality is consumed unchanged by trace_apply/trace_baseChange and norm_apply/det_baseChange. No comparison up to an unspecified isomorphism is substituted.
6. AlgebraMap R A, arbitrary A (including nonreduced dual-number tests), and all original trace/norm coefficients are unchanged.
7. Module.Free R S and Module.Finite R S stay in their original later scope. The original e*e=0 condition remains on norm_infinitesimal, with no extra condition on e or s.
8. Zero/sum/degenerate coefficient and nonreduced cases are retained. The deprecation warning is intentionally not repaired in this source delta.
9. Read actual OriginalRightTensorNormTrace318.norm_coefficient and norm_infinitesimal. They apply these exact statements, then the original commRight equivalence moves A tensor S to S tensor A with A acting on the right. The same epsilon and algebraMap R A trace appear; no sign or scalar is dropped. That later consumer is unchanged and not claimed compiled by this review.

## Provenance and metadata checks
Independently compared all 213 successor roots with exact published predecessor git blobs: only this source changes, 212 are identical, complete order identical. All declared APPLICATION bindings and intake source hashes match actual bytes. Own RESULT packet hash matches the published r15 intake; raw failure and before bytes are exact. Reviewed APPLICATION c884083f3d625f9a12546032ba8c8677a6eac6be7530590b5520b8677db5bdb6; intake 76d916517f3088a7bbe56525089560200a81e37e230810bfbe4d49672e4a4700. All acceptance flags remain false. The nine newly authored obligations accurately describe the narrow change.

Hosted elaboration/kernel behavior of the retained branches and later norm/trace consumers remains pending. Final owner-folder propagation and integrated publication review are separate.
