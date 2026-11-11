module
public import ContactWholePulledCoordinates318
public import ContactOriginalPositiveGlobalSections318
public import ContactGlobalLineComparison318
public section
noncomputable section
namespace ContactOriginalPositiveProjectiveComparison318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalWholeRestriction318 ContactOriginalPositiveBaseCoordinates318
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ)

def opens : ULift Bool → (X c).Opens := OpenClutchedLocallyFree318.cover (finiteOpen c) (infinityOpen c)
def pulled : ULift Bool → (SectionGeneratedGluing318.unit (X c) ⟶ ContactProjectiveLinePullback318.line c)
  | ⟨false⟩ => ContactPulledCoordinates318.zeroMap c
  | ⟨true⟩ => ContactPulledCoordinates318.oneMap c

def original : ULift Bool → (SectionGeneratedGluing318.unit (X c) ⟶
    (ContactOriginalTwistingLine318.line c 1).object)
  | ⟨false⟩ => ModuleGlobalSections318.ofTop _ (ContactOriginalPositiveGlobalSections318.zero c)
  | ⟨true⟩ => ModuleGlobalSections318.ofTop _ (ContactOriginalPositiveGlobalSections318.one c)

lemma pulled_bijective (i : ULift Bool) (V : (X c).Opens) (hV : V ≤ opens c i) :
    Function.Bijective (SectionGeneratedGluing318.genLinear (pulled c i) V) := by
  rcases i with ⟨i⟩
  cases i
  · exact ContactWholePulledCoordinates318.zero_bijective c V hV
  · exact ContactWholePulledCoordinates318.one_bijective c V hV
lemma original_bijective (i : ULift Bool) (V : (X c).Opens) (hV : V ≤ opens c i) :
    Function.Bijective (SectionGeneratedGluing318.genLinear (original c i) V) := by
  rcases i with ⟨i⟩
  cases i
  · exact ContactOriginalPositiveGlobalSections318.zero_bijective c V hV
  · exact ContactOriginalPositiveGlobalSections318.one_bijective c V hV

lemma finite_relation :
    SectionGeneratedGluing318.genLinear (original c ⟨true⟩) (finiteOpen c) 1 =
      finiteCoordinate c • SectionGeneratedGluing318.genLinear (original c ⟨false⟩) (finiteOpen c) 1 := by
  change (ModuleGlobalSections318.ofTop _ (ContactOriginalPositiveGlobalSections318.one c)).val.app _ 1 =
    finiteCoordinate c • (ModuleGlobalSections318.ofTop _ (ContactOriginalPositiveGlobalSections318.zero c)).val.app _ 1
  rw [ModuleGlobalSections318.ofTop_one,ModuleGlobalSections318.ofTop_one,
    ContactOriginalPositiveGlobalSections318.one_finite,ContactOriginalPositiveGlobalSections318.zero_finite,
    ← LinearEquiv.map_smul]
  simp only [smul_eq_mul,mul_one]
lemma infinity_relation :
    SectionGeneratedGluing318.genLinear (original c ⟨false⟩) (infinityOpen c) 1 =
      infinityCoordinate c • SectionGeneratedGluing318.genLinear (original c ⟨true⟩) (infinityOpen c) 1 := by
  change (ModuleGlobalSections318.ofTop _ (ContactOriginalPositiveGlobalSections318.zero c)).val.app _ 1 =
    infinityCoordinate c • (ModuleGlobalSections318.ofTop _ (ContactOriginalPositiveGlobalSections318.one c)).val.app _ 1
  rw [ModuleGlobalSections318.ofTop_one,ModuleGlobalSections318.ofTop_one,
    ContactOriginalPositiveGlobalSections318.zero_infinity,ContactOriginalPositiveGlobalSections318.one_infinity,
    ← LinearEquiv.map_smul]
  simp only [smul_eq_mul,mul_one]

lemma coefficients (i j : ULift Bool) : ∃ a : Γ(X c,opens c i),
    SectionGeneratedGluing318.genLinear (pulled c j) (opens c i) 1 =
      a • SectionGeneratedGluing318.genLinear (pulled c i) (opens c i) 1 ∧
    SectionGeneratedGluing318.genLinear (original c j) (opens c i) 1 =
      a • SectionGeneratedGluing318.genLinear (original c i) (opens c i) 1 := by
  rcases i with ⟨i⟩; rcases j with ⟨j⟩
  cases i <;> cases j
  · exact ⟨1,(one_smul _ _).symm,(one_smul _ _).symm⟩
  · exact ⟨finiteCoordinate c,ContactWholePulledCoordinates318.finite_relation c,finite_relation c⟩
  · exact ⟨infinityCoordinate c,ContactWholePulledCoordinates318.infinity_relation c,infinity_relation c⟩
  · exact ⟨1,(one_smul _ _).symm,(one_smul _ _).symm⟩

/-- The SAME positive line used in actual eventual H1 vanishing is the
actual pullback of the original projective O(1), with its original pair of
global sections retained. This is not an ampleness/representability axiom. -/
def iso : ContactProjectiveLinePullback318.line c ≅ (ContactOriginalTwistingLine318.line c 1).object :=
  SectionGeneratedGluing318.iso (opens c) (pulled c) (original c)
    (pulled_bijective c) (original_bijective c) (coefficients c)
    (OpenClutchedLocallyFree318.cover_top (finiteOpen c) (infinityOpen c) (cover c))

lemma preserves (i : ULift Bool) : pulled c i ≫ (iso c).hom = original c i :=
  SectionGeneratedGluing318.iso_preserves (opens c) (pulled c) (original c)
    (pulled_bijective c) (original_bijective c) (coefficients c)
    (OpenClutchedLocallyFree318.cover_top (finiteOpen c) (infinityOpen c) (cover c)) i

/-- The same line is consequently the original intrinsic bicanonical
module via the already constructed normalized projective comparison. -/
def bicanonicalIso : (ContactOriginalTwistingLine318.line c 1).object ≅ ContactGlobalBicanonical318.tensor c :=
  (iso c).symm ≪≫ ContactGlobalLineComparison318.iso c
end ContactOriginalPositiveProjectiveComparison318
