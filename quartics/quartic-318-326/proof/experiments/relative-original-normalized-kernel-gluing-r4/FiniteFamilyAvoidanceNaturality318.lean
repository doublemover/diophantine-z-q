module
public import FiniteFamilyAvoidanceUniversal318
public section
noncomputable section
namespace FiniteFamilyAvoidanceNaturality318
open AlgebraicGeometry CategoryTheory
open FiniteFamilyAvoidanceOpen318 FiniteFamilyAvoidanceFactor318
universe u
variable {Z B X T T' : Scheme.{u}} (p : Z ⟶ B) [UniversallyClosed p]
  (q : Z ⟶ X) (U : X.Opens) (f : T ⟶ B) (h : Supported p q U f) (g : T' ⟶ T)
lemma supported_comp : Supported p q U (g ≫ f) := by
  apply (supported_iff_range p q U _).mpr
  rintro _ ⟨t,rfl⟩
  exact (supported_iff_range p q U f).mp h ⟨g t,rfl⟩
@[reassoc] lemma factor_natural :
    factor p q U (g ≫ f) (supported_comp p q U f h g)=g ≫ factor p q U f h := by
  apply (cancel_mono (locus p q U).ι).mp
  rw [factor_into,Category.assoc,factor_into]
end FiniteFamilyAvoidanceNaturality318
