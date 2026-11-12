module
public import IdealSheafCoefficientCartesian318
public section
noncomputable section
namespace ContactProjectiveClassifiedBaseChange318
open AlgebraicGeometry CategoryTheory
variable (c : Fin 4 → ℚˣ) (n : ℕ) (S T : CommRingCat.{0}) [Algebra ℚ S] [Algebra ℚ T]
  (φ : S →ₐ[ℚ] T) (I : ContactProjectiveClassifiedIdeal318.Ideal c n S)
local notation "f" => RelativeCoefficientChange318.familyMap (CommRingCat.of ℚ) S T φ
  (ContactIntrinsicDifferentials318.structureMap c)
/-- Actual full ideal-sheaf coefficient comap, with its local
presentation derived from the true Cartesian canonical closed families. -/
@[expose] def map : ContactProjectiveClassifiedIdeal318.Ideal c n T :=
  ⟨I.val.comap f,⟨ContactProjectivePresentationPullback318.data c n S T φ I.val.subschemeι
    (I.val.comap f).subschemeι (IdealSheafCoefficientCartesian318.map I.val f)
    (IdealSheafCoefficientCartesian318.cartesian I.val f)
    (ContactProjectiveClassifiedIdeal318.presentation c n S I)⟩⟩
lemma natural : ContactProjectiveClassifiedIdeal318.classify c n T (map c n S T φ I)=
    ContactProjectiveParameterPoint318.map c n S T φ (ContactProjectiveClassifiedIdeal318.classify c n S I) :=
  ContactProjectiveGlobalNaturality318.natural c n S T φ I.val.subschemeι (I.val.comap f).subschemeι
    (IdealSheafCoefficientCartesian318.map I.val f) (IdealSheafCoefficientCartesian318.cartesian I.val f)
    (ContactProjectiveClassifiedIdeal318.presentation c n S I)
    (ContactProjectiveClassifiedIdeal318.presentation c n T (map c n S T φ I))
end ContactProjectiveClassifiedBaseChange318
