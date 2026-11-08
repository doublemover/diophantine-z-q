# Independent bounded review: intrinsic tensor normalization

Decision: ACCEPTED within the exact local normalization scope. No discrepancy found in all ten target Lean sources, read in full. All 38 target artifact, direct-dependency and predecessor-receipt hash comparisons pass. This is a non-author source/argument review of the ten new modules, not a new compiler replay and not acceptance of global bicanonical gluing.

## Reviewer and independence

Reviewer: /root/restart_contact_field. Tools: read-only cloud terminal source inspection and SHA-256 recomputation; no compiler used for this review. The reviewer authored several older contact-field and normalization/chart predecessors and helped restore exact copies of the earlier contact differential sources. This review does not independently certify that own earlier work. The ten target tensor/derivative normalization modules were authored by the Hodge worker. The review follows their actual consuming joins against the named existing chart and frame interfaces.

## Exact object and index coverage

The parameter is every c : Fin 4 → Qˣ. Finite statements quantify every i : Fin 4, while the local section/frame theorems use every i : Option (Fin 4), including none for infinity. The target is the actual universal relative cotangent sheaf of ContactGlobalSmooth318.Model c over Q and its sheafified module tensor square. The local embeddings are the actual five ContactIntrinsicFrames318 maps, not a parallel coefficient family. No specialization to one twist tuple or omission of a branch occurs.

## Pure tensors and actual restriction

TensorSheafNormalization318 uses the actual sheafification adjunction unit naturality, counit triangle and restriction comparison. congr_pure is the image of the real presheaf tensor map. unitIso_pure checks the left unitor followed by the sheafification counit sends a⊗b to a*b, not merely to an unspecified multiple. restriction_pure retains the coefficient ring isomorphism induced by the open immersion and sends the ambient pure tensor to the tensor of its restricted sections. ContactBicanonicalFrameNormalization318.localFrame_pure composes these three specific maps. Thus its frame coefficient is exactly the product of the two cotangent frame coefficients.

## Universal derivative, including the inferred proof definitions

ContactBranchCoordinate318 transports the literal source square equation through sourceLocalizationEquiv, retaining the actual polynomial t and normalized root z_i. It proves t-a_i=c_i^(-1)z_i² on the entire localization, including the ramified point. SquareCoordinateDifferential318 differentiates this equation by the universal derivation and proves Dt=(2c_i^(-1)z_i)Dz_i. ContactBranchDifferential318 specializes it to the actual chosen localization frame, including the exact factor 2z_i/c_i.

IntrinsicFrameDerivative318.chartFrame is exactly the inverse intrinsic affine-chart comparison followed by the sheaf frame of the algebraic Kähler frame. chartFrame_section and chartFrame_inverse_section compare its value with IntrinsicChartSections318.sectionMap(Ds). The latter is independently identified in the existing chart API with the actual ambient universal derivative, not an abstract generator.

ContactDerivativeFrameComparison318.branchFrame_eq and infinityFrame_eq are rfl comparisons of the actual chosen frames with that generic chartFrame. The inferred definitions localDerivative_branch and localDerivative_infinity are applications of frame_inverse_section_of_eq with those exact equalities, the actual coordinates, and their proved normalization e(Ds)=1. They are proposition-valued proof terms; they introduce no hypothesis or new axiom. Their inferred conclusion is precisely that inverse local frame at one equals sectionMap(Dz_i), respectively sectionMap(Du). The u coordinate is the existing actual u=c₀/y₀ convention. The separate normalized localDerivative name unfolds to the same left side, so there is no missing comparison between differently named generators.

## q0/q1 and retained coefficient powers

ContactBicanonicalDerivative318.localSquare is the genuine pure tensor of the normalized local derivative with itself. Its coefficient under the actual bicanonical frame is exactly one, and the inverse frame at one is consequently that square. ContactBicanonicalSectionNormalization318.frame_inverse uses module linearity to identify inverse frame at any a with a times localSquare. Its q0_normalized and q1_normalized then apply this to the already defined local sections, with the same coefficients and the same ΓSpec identifications. Finite coefficients retain 4*C_i/c_i and t times this expression, divided only by the other-branch denominator. Infinity coefficients retain 4*C₀*u²/(c₀⁵D_inf) and 4*C₀/(c₀⁴D_inf). No change of scalar or omitted twist power is hidden in the sheaf maps.

BicanonicalCoefficientIdentity318.finite_cleared is a general commutative-ring identity. Its assumptions (t-a)D=CP, Dd=1 and t-a=kz² imply P*(4Ckd)=(2kz)² by multiplication and substitution alone. It never inverts t-a or z, so it retains the ramified point. Its actual-chart specialization is correctly excluded from this packet's README and belongs to the separate continuation.

## Validation and limits

The producer's preserved log records ten successful strict builds and a 283-declaration, 23-module recursive axiom audit. JoinedAudit.lean iterates all module constant names, including generated/private declarations and the two proof-valued definitions, allowing only propext, Classical.choice and Quot.sound. This review inspected that mechanism and log; it did not rerun them.

The accepted conclusion is exact whole-local-chart differential and tensor-section normalization. The packet does not assert equality on full intersections, global q0/q1 sections, a canonical-degree or genus computation, global triviality, a Jacobian factor, a PEL identification or a Kodaira–Spencer comparison. Separately supplied intersection maps cannot be retroactively treated as a proof of sheaf-section compatibility. No revision is requested for the reviewed packet.
