module
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Tactic
public section
noncomputable section
namespace LocalizedKaehlerFrame318
open KaehlerDifferential TensorProduct
open scoped TensorProduct
set_option maxHeartbeats 200000
variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- An actual relative Kähler frame transports along an actual formally étale algebra. -/
@[expose] def etaleFrame [Algebra.FormallyEtale S T]
    (frame : KaehlerDifferential R S ≃ₗ[S] S) : KaehlerDifferential R T ≃ₗ[T] T :=
  (tensorKaehlerEquivOfFormallyEtale R S T).symm.trans
    ((frame.baseChange S T).trans (AlgebraTensorModule.rid S T T))

theorem etaleFrame_map [Algebra.FormallyEtale S T]
    (frame : KaehlerDifferential R S ≃ₗ[S] S) (ω : KaehlerDifferential R S) :
    etaleFrame (T := T) frame (KaehlerDifferential.map R R S T ω) = algebraMap S T (frame ω) := by
  have h : (tensorKaehlerEquivOfFormallyEtale R S T).symm
      (KaehlerDifferential.map R R S T ω) = 1 ⊗ₜ[S] ω := by
    apply (tensorKaehlerEquivOfFormallyEtale R S T).injective
    simp [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,KaehlerDifferential.mapBaseChange_tmul]
  simp [etaleFrame,h,Algebra.smul_def]

theorem etaleFrame_D [Algebra.FormallyEtale S T]
    (frame : KaehlerDifferential R S ≃ₗ[S] S) (s : S) :
    etaleFrame (T := T) frame (D R T (algebraMap S T s)) = algebraMap S T (frame (D R S s)) := by
  rw [←KaehlerDifferential.map_D R R S T]
  exact etaleFrame_map frame _

/-- Actual localization supplies formal étaleness; it is not a hypothesis on the frame. -/
@[expose] def localFrame (M : Submonoid S) [IsLocalization M T]
    (frame : KaehlerDifferential R S ≃ₗ[S] S) : KaehlerDifferential R T ≃ₗ[T] T := by
  letI := Algebra.FormallyEtale.of_isLocalization (Rₘ := T) M
  exact etaleFrame frame

theorem localFrame_map (M : Submonoid S) [IsLocalization M T]
    (frame : KaehlerDifferential R S ≃ₗ[S] S) (ω : KaehlerDifferential R S) :
    localFrame (T := T) M frame (KaehlerDifferential.map R R S T ω) = algebraMap S T (frame ω) := by
  letI := Algebra.FormallyEtale.of_isLocalization (Rₘ := T) M
  exact etaleFrame_map frame ω

theorem localFrame_D (M : Submonoid S) [IsLocalization M T]
    (frame : KaehlerDifferential R S ≃ₗ[S] S) (s : S) :
    localFrame (T := T) M frame (D R T (algebraMap S T s)) = algebraMap S T (frame (D R S s)) := by
  rw [←KaehlerDifferential.map_D R R S T]
  exact localFrame_map M frame _

/-- A differential normalized in the chart remains normalized in the actual local ring. -/
theorem localFrame_normalized (M : Submonoid S) [IsLocalization M T]
    (frame : KaehlerDifferential R S ≃ₗ[S] S) (s : S) (hs : frame (D R S s)=1) :
    localFrame (T := T) M frame (D R T (algebraMap S T s)) = 1 := by
  rw [localFrame_D,hs,map_one]

/-- The transported normalized differential genuinely generates the whole local module. -/
theorem local_differential_generates (M : Submonoid S) [IsLocalization M T]
    (frame : KaehlerDifferential R S ≃ₗ[S] S) (s : S) (hs : frame (D R S s)=1) :
    Submodule.span T (Set.singleton (D R T (algebraMap S T s))) = ⊤ := by
  apply top_le_iff.mp
  intro ω _
  apply Submodule.mem_span_singleton.mpr
  refine ⟨localFrame (T := T) M frame ω,?_⟩
  apply (localFrame (T := T) M frame).injective
  rw [map_smul,localFrame_normalized M frame s hs,smul_eq_mul,mul_one]

end LocalizedKaehlerFrame318
