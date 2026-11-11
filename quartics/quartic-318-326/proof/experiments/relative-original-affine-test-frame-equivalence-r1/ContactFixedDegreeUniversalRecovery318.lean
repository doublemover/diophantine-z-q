module
public import ContactProjectiveClassifiedEquiv318
public section
noncomputable section
namespace ContactFixedDegreeUniversalRecovery318
open AlgebraicGeometry CategoryTheory
open ContactProjectiveDegreeData318
variable (S : CommRingCat.{0}) [Algebra ℚ S] (c : Fin 4 → ℚˣ) (n : ℕ) (D : FixedDegree S c n)
local notation "q" => ContactProjectiveQuotientGluing318.into S c D.val.datum
local notation "x" => ContactFixedDegreeGlobalClassifier318.point S c n D
/-- Every original fixed-degree effective finite-flat Cartier datum is
recovered by the actual GLOBAL universal family over its global point,
with a source-preserving scheme isomorphism of the WHOLE family. -/
@[expose] def comparison : ContactProjectiveQuotientGluing318.family S c D.val.datum ≅
    ContactProjectivePointFamily318.family c n S x :=
  ContactProjectiveInputRecovery318.comparison c n S q (ContactFixedDegreePresentation318.data S c n D)
@[reassoc] lemma comparison_source : (comparison S c n D).hom ≫ ContactProjectivePointFamily318.into c n S x=q :=
  ContactProjectiveInputRecovery318.comparison_source c n S q (ContactFixedDegreePresentation318.data S c n D)
lemma ideal_recovery : ContactProjectivePointFamily318.idealSheaf c n S x=
    ContactProjectiveQuotientIdealSheaf318.idealSheaf S c D.val.datum :=
  ContactProjectiveInputRecovery318.ideal_recovery c n S q (ContactFixedDegreePresentation318.data S c n D)
end ContactFixedDegreeUniversalRecovery318
