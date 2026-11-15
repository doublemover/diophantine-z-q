module
public import ContactProjectivePointRecovery318
public section
noncomputable section
namespace ContactProjectiveClassifiedIdeal318
open AlgebraicGeometry CategoryTheory
variable (c : Fin 4 → ℚˣ) (n : ℕ) (S : CommRingCat.{0}) [Algebra ℚ S]
/-- Intrinsic full ideals locally presented by finite-projective rank-n
whole quotients supported in actual original source charts. This condition
contains NO parameter point, classifier or assumed inverse identity. -/
abbrev Ideal := {I : (ContactRelativeLinearOpenChart318.curve S c).IdealSheafData //
  Nonempty (ContactProjectiveLocalPresentation318.Data c n S I.subschemeι)}
@[expose] def presentation (I : Ideal c n S) : ContactProjectiveLocalPresentation318.Data c n S I.val.subschemeι :=
  Classical.choice I.property
@[expose] def classify (I : Ideal c n S) : ContactProjectiveParameterPoint318.Point c n S :=
  ContactProjectiveGlobalClassifyingMap318.point c n S I.val.subschemeι (presentation c n S I)
variable (x : ContactProjectiveParameterPoint318.Point c n S)
abbrev canonicalIso : ContactProjectivePointFamily318.family c n S x ≅
    (ContactProjectivePointFamily318.idealSheaf c n S x).subscheme :=
  asIso (ContactProjectivePointFamily318.into c n S x).toImage
@[reassoc] lemma canonicalIso_source : (canonicalIso c n S x).hom ≫
    (ContactProjectivePointFamily318.idealSheaf c n S x).subschemeι=ContactProjectivePointFamily318.into c n S x :=
  (ContactProjectivePointFamily318.into c n S x).toImage_imageι
/-- Extract the actual full universal ideal; its local presentation is
constructed on the entire pulled-back parameter cover, not assumed. -/
@[expose] def extract : Ideal c n S :=
  ⟨ContactProjectivePointFamily318.idealSheaf c n S x,⟨ContactProjectivePresentationIso318.transport c n S
    (ContactProjectivePointFamily318.into c n S x)
    (ContactProjectivePointFamily318.idealSheaf c n S x).subschemeι
    (canonicalIso c n S x) (canonicalIso_source c n S x)
    (ContactProjectivePointPresentation318.data c n S x)⟩⟩
end ContactProjectiveClassifiedIdeal318
