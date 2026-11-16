module
public import ContactProjectiveClassifiedIdeal318
public section
noncomputable section
namespace ContactProjectiveClassifiedEquiv318
open AlgebraicGeometry CategoryTheory
open ContactProjectiveClassifiedIdeal318
variable (c : Fin 4 → ℚˣ) (n : ℕ) (S : CommRingCat.{0}) [Algebra ℚ S]
lemma extract_classify (I : Ideal c n S) : extract c n S (classify c n S I)=I := by
  apply Subtype.ext
  exact (ContactProjectiveInputRecovery318.ideal_recovery c n S I.val.subschemeι
    (presentation c n S I)).trans I.val.ker_subschemeι
lemma classify_extract (x : ContactProjectiveParameterPoint318.Point c n S) :
    classify c n S (extract c n S x)=x := by
  have h := ContactProjectivePresentationIso318.invariant c n S
    (ContactProjectivePointFamily318.into c n S x)
    (ContactProjectivePointFamily318.idealSheaf c n S x).subschemeι
    (canonicalIso c n S x) (canonicalIso_source c n S x)
    (ContactProjectivePointPresentation318.data c n S x)
    (presentation c n S (extract c n S x))
  exact h.symm.trans (ContactProjectivePointRecovery318.recover c n S x)
/-- Genuine two-sided ALL-point classification of independently defined
locally chart-supported finite-projective full ideals on the ORIGINAL
projective curve. Standard finite-flat rank characterization is separate. -/
@[expose] def equivalence : Ideal c n S ≃ ContactProjectiveParameterPoint318.Point c n S where
  toFun := classify c n S
  invFun := extract c n S
  left_inv := extract_classify c n S
  right_inv := classify_extract c n S
end ContactProjectiveClassifiedEquiv318
