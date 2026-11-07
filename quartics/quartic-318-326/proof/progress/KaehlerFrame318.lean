module
public import UnitRamifiedIntegral318
public import Mathlib.RingTheory.Kaehler.Basic
public section
noncomputable section
namespace KaehlerFrame318
open KaehlerDifferential
set_option maxHeartbeats 0
variable {R B K : Type*} [CommRing R] [CommRing B] [Field K]
  [Algebra R B] [Algebra B K] [Algebra R K] [IsScalarTower R B K]

/-- The genuine derivation dual to an actual Kähler differential frame. -/
@[expose] def frameDerivation {A : Type*} [CommRing A] [Algebra R A]
    (frame : KaehlerDifferential R A ≃ₗ[A] A) : Derivation R A A :=
  KaehlerDifferential.linearMapEquivDerivation R A frame.toLinearMap

theorem frameDerivation_apply {A : Type*} [CommRing A] [Algebra R A]
    (frame : KaehlerDifferential R A ≃ₗ[A] A) (a : A) :
    frameDerivation frame a = frame (KaehlerDifferential.D R A a) := rfl

/-- One shared normalized frame generator forces compatibility on all actual
Kähler differentials. No integral-preservation conclusion is assumed. -/
theorem frames_compatible
    (integral : KaehlerDifferential R B ≃ₗ[B] B)
    (generic : KaehlerDifferential R K ≃ₗ[K] K)
    (generator : generic (KaehlerDifferential.map R R B K (integral.symm 1)) = 1)
    (ω : KaehlerDifferential R B) :
    generic (KaehlerDifferential.map R R B K ω) = algebraMap B K (integral ω) := by
  have hω : ω = integral ω • integral.symm 1 := by
    apply integral.injective
    simp
  conv_lhs => rw [hω,LinearMap.map_smul]
  rw [←IsScalarTower.algebraMap_smul K (integral ω) (KaehlerDifferential.map R R B K (integral.symm 1))]
  rw [map_smul,generator,smul_eq_mul,mul_one]

theorem field_derivation_on_integral
    (integral : KaehlerDifferential R B ≃ₗ[B] B)
    (generic : KaehlerDifferential R K ≃ₗ[K] K)
    (generator : generic (KaehlerDifferential.map R R B K (integral.symm 1)) = 1)
    (b : B) :
    frameDerivation generic (algebraMap B K b) = algebraMap B K (frameDerivation integral b) := by
  rw [frameDerivation_apply,frameDerivation_apply,←KaehlerDifferential.map_D R R B K]
  exact frames_compatible integral generic generator _

/-- The field derivation's preservation of the local integral ring is derived
from the actual Kähler frame and its shared generic generator. -/
theorem preserves_integral
    (integral : KaehlerDifferential R B ≃ₗ[B] B)
    (generic : KaehlerDifferential R K ≃ₗ[K] K)
    (generator : generic (KaehlerDifferential.map R R B K (integral.symm 1)) = 1) :
    ∀ b : B, ∃ c : B, frameDerivation generic (algebraMap B K b) = algebraMap B K c :=
  fun b => ⟨frameDerivation integral b,field_derivation_on_integral integral generic generator b⟩

/-- A genuine differential generator has a unit coefficient in every integral
rank-one frame. The unit is not supplied as the derivative conclusion. -/
theorem unit_of_differential_generator
    (integral : KaehlerDifferential R B ≃ₗ[B] B) (z : B)
    (hz : Submodule.span B ({KaehlerDifferential.D R B z} : Set (KaehlerDifferential R B)) = ⊤) :
    IsUnit (frameDerivation integral z) := by
  have hmem : integral.symm 1 ∈ Submodule.span B ({KaehlerDifferential.D R B z} : Set (KaehlerDifferential R B)) := by
    rw [hz]
    trivial
  obtain ⟨b,hb⟩ := Submodule.mem_span_singleton.mp hmem
  have hmul : b * frameDerivation integral z = 1 := by
    have hh := congrArg integral hb
    simpa only [map_smul,smul_eq_mul,LinearEquiv.apply_symm_apply,frameDerivation_apply] using hh
  exact IsUnit.of_mul_eq_one_right b hmul

/-- Normalize any generic rank-one frame on the actual nonzero image of the
integral frame generator. No preselected compatible field derivation is used. -/
@[expose] def normalizedGenericFrame
    (integral : KaehlerDifferential R B ≃ₗ[B] B)
    (generic : KaehlerDifferential R K ≃ₗ[K] K)
    (hne : KaehlerDifferential.map R R B K (integral.symm 1) ≠ 0) :
    KaehlerDifferential R K ≃ₗ[K] K :=
  generic.trans (LinearEquiv.smulOfUnit (Units.mk0
    (generic (KaehlerDifferential.map R R B K (integral.symm 1)))
    (fun h => hne (generic.injective (by simpa using h))))).symm

theorem normalized_generator
    (integral : KaehlerDifferential R B ≃ₗ[B] B)
    (generic : KaehlerDifferential R K ≃ₗ[K] K)
    (hne : KaehlerDifferential.map R R B K (integral.symm 1) ≠ 0) :
    normalizedGenericFrame integral generic hne
      (KaehlerDifferential.map R R B K (integral.symm 1)) = 1 := by
  let u : Kˣ := Units.mk0 (generic (KaehlerDifferential.map R R B K (integral.symm 1)))
    (fun h => hne (generic.injective (by simpa using h)))
  change (↑(u⁻¹) : K) * ↑u = 1
  exact u.inv_mul

/-- A field derivation extending the actual integral frame derivation is
constructed from rank-one Kähler frames and nonvanishing of the mapped generator. -/
theorem exists_field_derivation
    (integral : KaehlerDifferential R B ≃ₗ[B] B)
    (generic : KaehlerDifferential R K ≃ₗ[K] K)
    (hne : KaehlerDifferential.map R R B K (integral.symm 1) ≠ 0) :
    ∃ D : Derivation R K K, ∀ b : B,
      D (algebraMap B K b) = algebraMap B K (frameDerivation integral b) := by
  exact ⟨frameDerivation (normalizedGenericFrame integral generic hne),
    field_derivation_on_integral integral _ (normalized_generator integral generic hne)⟩

end KaehlerFrame318
