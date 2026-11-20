module
public import SelectedTraceDualNormalization318
public section
noncomputable section
open Polynomial SelectedTraceDualNormalization318

namespace SelectedNormalizationDualFunctional318

variable {R K F : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
variable [Field K] [Field F] [Algebra R K] [IsFractionRing R K]
variable [Algebra K F] [Algebra R F] [IsScalarTower R K F]
variable [FiniteDimensional K F] [Algebra.IsSeparable K F]
local notation "B" => integralClosure R F

/-- The genuine trace dual as a B-module, not just the R-submodule
thereof. The 1 submodule is the actual inclusion of B into F. -/
abbrev normalizedComplementary (K : Type*) {R F : Type*}
    [CommRing R] [Field K] [Field F]
    [Algebra R K] [Algebra K F] [Algebra R F] [IsScalarTower R K F] :
    Submodule (integralClosure R F) F :=
  Submodule.traceDual R K (1 : Submodule (integralClosure R F) F)

theorem normalized_mem_complementary (z : F) (hz : z ∈ normalizedComplementary K) :
    z ∈ complementary K B := by
  apply mem_complementary.mpr
  intro y hy
  have hBy : y ∈ (1 : Submodule B F) := Submodule.mem_one.mpr ⟨⟨y,hy⟩,rfl⟩
  apply Submodule.mem_one.mpr
  exact (Submodule.mem_traceDual.mp hz y hBy).elim fun v hv =>
    ⟨v, hv.trans (Algebra.traceForm_apply z y)⟩

/-- The literal multiplication by M is an actual B-linear functional
on the trace dual of the normalization. Under the separate finite
duality identification with complementary·dJ, this is M/dJ; the
regular-resolution comparison is not part of this declaration. -/
theorem literal_dual_functional
    {x : F} (hx : Algebra.adjoin K ({x} : Set F) = ⊤) (hint : IsIntegral R x)
    (p : R[X]) (hp : p.map (algebraMap R K) = minpoly K x)
    (M : ℕ) {w : F} (hw : w ∈ Algebra.adjoin R ({x} : Set F))
    (witness : aeval x p.derivative * w = (M:F)) :
    ∃ f : normalizedComplementary (R:=R) (F:=F) K →ₗ[B] B,
      ∀ z : normalizedComplementary (R:=R) (F:=F) K, (f z:F) = (M:F)*(z:F) := by
  have h (z : normalizedComplementary (R:=R) (F:=F) K) : (M:F)*(z:F) ∈ B :=
    (actual_normalization_clear hx hint p hp M hw witness _ (normalized_mem_complementary _ z.2)).2
  refine ⟨{
    toFun := fun z => ⟨(M:F)*(z:F),h z⟩
    map_add' := ?_
    map_smul' := ?_ }, fun _ => rfl⟩
  · intro z₁ z₂
    apply Subtype.ext
    exact mul_add _ _ _
  · intro b z
    apply Subtype.ext
    change (M:F)*((b:F)*(z:F)) = (b:F)*((M:F)*(z:F))
    ac_rfl

end SelectedNormalizationDualFunctional318

#print axioms SelectedNormalizationDualFunctional318.normalized_mem_complementary
#print axioms SelectedNormalizationDualFunctional318.literal_dual_functional
