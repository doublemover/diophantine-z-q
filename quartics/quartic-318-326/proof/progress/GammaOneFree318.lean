module
public import FixedPointTrace318
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public section
noncomputable section
open UpperHalfPlane
open scoped MatrixGroups
namespace GammaOneFree318
set_option maxHeartbeats 0

@[expose] def realMatrix (gamma:SL(2,ℤ)) : GL (Fin 2) ℝ :=
  Matrix.SpecialLinearGroup.mapGL ℝ gamma

@[simp] theorem realMatrix_entry (gamma:SL(2,ℤ)) (i j:Fin 2) :
    realMatrix gamma i j=(gamma i j:ℝ) := rfl

@[simp] theorem realMatrix_det (gamma:SL(2,ℤ)) : (realMatrix gamma).val.det=1 :=
  (gamma.map (algebraMap ℤ ℝ)).det_coe

/-- The exact integer trace congruence of an actual Gamma1(N) matrix. -/
theorem trace_congruence (N:ℕ) (gamma:SL(2,ℤ)) (hgamma:gamma∈CongruenceSubgroup.Gamma1 N) :
    (N:ℤ)∣2-(gamma 0 0+gamma 1 1) := by
  obtain ⟨ha,hd,hc⟩:=(CongruenceSubgroup.Gamma1_mem N gamma).mp hgamma
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp
  push_cast
  rw [ha,hd]
  ring

/-- A matrix in Gamma1(N), N>=5, fixing an actual upper-half-plane point is identity. -/
theorem eq_one_of_fixed (N:ℕ) (hN:5≤N) (gamma:SL(2,ℤ))
    (hgamma:gamma∈CongruenceSubgroup.Gamma1 N) (z:UpperHalfPlane)
    (hz:realMatrix gamma•z=z) : gamma=1 := by
  have hb:=FixedPointTrace318.trace_bounds _ (realMatrix_det gamma) z hz
  simp only [realMatrix_entry] at hb
  have hbI : -2≤gamma 0 0+gamma 1 1 ∧ gamma 0 0+gamma 1 1≤2 := by exact_mod_cast hb
  have ht : 2-(gamma 0 0+gamma 1 1)=0 :=
    Int.eq_zero_of_dvd_of_nonneg_of_lt (by omega) (by omega)
      (trace_congruence N gamma hgamma)
  have htr : realMatrix gamma 0 0+realMatrix gamma 1 1=2 := by
    simp only [realMatrix_entry]
    exact_mod_cast (show gamma 0 0+gamma 1 1=2 by omega)
  have hg:=FixedPointTrace318.eq_one_of_trace_two _ (realMatrix_det gamma) z hz htr
  apply Matrix.SpecialLinearGroup.mapGL_injective (S:=ℝ)
  simpa only [realMatrix,map_one] using hg

/-- Every nonidentity Gamma1(N) element acts without a fixed point on the upper half-plane. -/
theorem no_fixed_point (N:ℕ) (hN:5≤N) (gamma:SL(2,ℤ))
    (hgamma:gamma∈CongruenceSubgroup.Gamma1 N) (hg:gamma≠1) (z:UpperHalfPlane) :
    realMatrix gamma•z≠z := fun hz=>hg (eq_one_of_fixed N hN gamma hgamma z hz)

/-- The actual subgroup action has trivial point stabilizers. -/
theorem subgroup_fixed_iff (N:ℕ) (hN:5≤N) (gamma:CongruenceSubgroup.Gamma1 N)
    (z:UpperHalfPlane) : realMatrix gamma.val•z=z ↔ gamma=1 := by
  constructor
  · intro hz
    apply Subtype.ext
    exact eq_one_of_fixed N hN gamma.val gamma.property z hz
  · rintro rfl
    simp [realMatrix]
end GammaOneFree318
