module
public import CoherentAdditionV318
public import RealQuarticTopologicalGroup318
public section
noncomputable section
namespace RealCoherentOrbit318
open ConcreteG8Domain (K D)
open CoherentMultipleCharts318 (chartU chartV)
open RealQuarticGroup318 (Oval)
set_option maxHeartbeats 2000000

variable (σ : K →+* ℝ)

lemma real_D_pos : 0<σ D := lt_trans zero_lt_one (RealMultiples318.real_D_gt_one σ)

local instance realGroup : AddCommGroup (Oval (σ D)) :=
  RealQuarticGroup318.group (σ D) (real_D_pos σ)

/-- The actual coherent arithmetic coordinates in any real embedding, as a
point of the independently constructed real quartic group. -/
@[expose] def orbit (n : ℤ) : Oval (σ D) :=
  ⟨(σ (chartU n),σ (chartV n)),by
    simpa only [map_pow,map_sub,map_one,map_mul] using
      congrArg σ (CoherentAdditionV318.chart_curve n)⟩

lemma orbit_zero : orbit σ 0=0 := by
  apply Subtype.ext
  change (σ (chartU 0),σ (chartV 0))=(0,1)
  simp

lemma orbit_add (n m : ℤ) : orbit σ (n+m)=orbit σ n+orbit σ m := by
  apply Subtype.ext
  apply Prod.ext
  · change σ (chartU (n+m))=ReciprocalGroup318.sumU (σ D)
      (σ (chartU n)) (σ (chartV n)) (σ (chartU m)) (σ (chartV m))
    rw [CoherentAdditionV318.chartU_add]
    simp only [ReciprocalGroup318.sumU,map_div₀,map_add,map_mul,map_one,map_pow]
  · change σ (chartV (n+m))=ReciprocalGroup318.sumV (σ D)
      (σ (chartU n)) (σ (chartV n)) (σ (chartU m)) (σ (chartV m))
    rw [CoherentAdditionV318.chartV_add]
    simp only [ReciprocalGroup318.sumV,map_div₀,map_sub,map_add,map_mul,map_one,map_pow,map_ofNat]

/-- The coherent coordinates form an actual integer group homomorphism. -/
@[expose] def orbitHom : ℤ →+ Oval (σ D) where
  toFun := orbit σ
  map_zero' := orbit_zero σ
  map_add' := orbit_add σ

/-- Exact identification with integer multiples of one fixed actual real point. -/
theorem orbit_zsmul (n : ℤ) : orbit σ n=n • orbit σ 1 := by
  simpa [orbitHom,zsmul_eq_mul] using (orbitHom σ).map_zsmul n (1:ℤ)

/-- Nontorsion is inherited from the exact arithmetic coordinate, not inferred
from a numerical approximation of its real angle. -/
theorem orbit_injective : Function.Injective (orbit σ) := by
  intro n m he
  have hz : orbit σ (n-m)=0 := by
    change orbitHom σ (n-m)=0
    rw [map_sub]
    exact sub_eq_zero.mpr he
  have hu : σ (chartU (n-m))=0 := congrArg (fun x : Oval (σ D) => x.val.1) hz
  have hzero : chartU (n-m)=0 := σ.injective (by simpa using hu)
  exact sub_eq_zero.mp ((CoherentMultipleCharts318.chartU_zero_iff (n-m)).mp hzero)

end RealCoherentOrbit318
