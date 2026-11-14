module
public import PadicQuadraticCoordinates318
public section
noncomputable section
namespace ActualOrbitTranslatedAccess318
open ConcreteG8Domain (K D)
open CoherentMultipleCharts318 ActualOrbitLocalFilter318 PadicQuadraticCoordinates318
open scoped QuadraticAlgebra Topology
set_option maxHeartbeats 1000000

@[expose] def inputU {F : Type*} (x : Fin 4 → F) : F×F := (x 0,x 1)
@[expose] def inputV {F : Type*} [AddMonoidWithOne F] (x : Fin 4 → F) : F×F := (1+x 2,x 3)
@[expose] def pack {F : Type*} [AddGroupWithOne F] (u v : F×F) : Fin 4 → F :=
  ![u.1,u.2,v.1-1,v.2]
@[expose] def denominator (p : ℕ) [Fact p.Prime] (n : ℤ) (x : Fin 4 → ℚ_[p]) : ℚ_[p]×ℚ_[p] :=
  (1,0)+mul (mul (lift p D) (sq (lift p (chartU n)))) (sq (inputU x))
@[expose] def translatedU (p : ℕ) [Fact p.Prime] (n : ℤ) (x : Fin 4 → ℚ_[p]) : ℚ_[p]×ℚ_[p] :=
  divide (mul (lift p (chartU n)) (inputV x)+mul (inputU x) (lift p (chartV n)))
    (denominator p n x)
@[expose] def translatedV (p : ℕ) [Fact p.Prime] (n : ℤ) (x : Fin 4 → ℚ_[p]) : ℚ_[p]×ℚ_[p] :=
  divide (mul (mul (lift p (chartV n)) (inputV x))
      ((1,0)-mul (mul (lift p D) (sq (lift p (chartU n)))) (sq (inputU x)))-
    mul (mul (mul (mul (2,0) (lift p D)) (lift p (chartU n))) (inputU x))
      (sq (lift p (chartU n))+sq (inputU x))) (sq (denominator p n x))
@[expose] def translate (p : ℕ) [Fact p.Prime] (n : ℤ) (x : Fin 4 → ℚ_[p]) : Fin 4 → ℚ_[p] :=
  pack (translatedU p n x) (translatedV p n x)

lemma inputU_error (p : ℕ) [Fact p.Prime] (m : ℤ) : inputU (error p m)=lift p (chartU m) := by
  rfl
lemma inputV_error (p : ℕ) [Fact p.Prime] (m : ℤ) : inputV (error p m)=lift p (chartV m) := by
  ext <;> simp [inputV,error,lift] <;> ring
lemma pack_chart (p : ℕ) [Fact p.Prime] (m : ℤ) :
    pack (lift p (chartU m)) (lift p (chartV m))=error p m := by
  ext i
  fin_cases i <;> simp [pack,lift,error]

lemma denominator_error (p : ℕ) [Fact p.Prime] (n m : ℤ) :
    denominator p n (error p m)=lift p (1+D*(chartU n)^2*(chartU m)^2) := by
  simp only [denominator,inputU_error,←lift_sq,←lift_mul,←lift_one,←lift_add]

/-- Coordinate transport is computed from the actual rational addition
law, so there is no assumption that the elliptic orbit has a chosen topology. -/
lemma translate_error (p : ℕ) [Fact p.Prime] (n m : ℤ) :
    translate p n (error p m)=error p (n+m) := by
  have hu : translatedU p n (error p m)=lift p (chartU (n+m)) := by
    rw [CoherentAdditionV318.chartU_add]
    simp only [translatedU,inputU_error,inputV_error,denominator_error,
      ReciprocalGroup318.sumU,lift_divide,lift_add,lift_mul,lift_one,lift_sq]
  have hv : translatedV p n (error p m)=lift p (chartV (n+m)) := by
    rw [CoherentAdditionV318.chartV_add]
    simp only [translatedV,inputU_error,inputV_error,denominator_error,
      ReciprocalGroup318.sumV,lift_divide,lift_sub,lift_add,lift_mul,lift_one,lift_two,lift_sq]
  rw [translate,hu,hv,pack_chart]

@[simp] lemma translate_zero (p : ℕ) [Fact p.Prime] (n : ℤ) :
    translate p n 0=error p n := by
  simpa only [error_zero,add_zero] using translate_error p n 0

lemma denominator_zero (p : ℕ) [Fact p.Prime] (n : ℤ) : denominator p n 0=(1,0) := by
  simp [denominator,sq,mul,inputU]

/-- Every translated chart is continuous at the actual positive identity.
The division norms at that point are exactly one at every prime. -/
lemma translate_continuousAt (p : ℕ) [Fact p.Prime] (n : ℤ) :
    ContinuousAt (translate p n) 0 := by
  have hd : Continuous (denominator p n) := by
    unfold denominator sq mul inputU
    fun_prop
  have hu : ContinuousAt (translatedU p n) 0 := by
    apply divide_continuousAt
    · unfold inputU inputV mul
      fun_prop
    · exact hd.continuousAt
    · rw [denominator_zero]
      norm_num [qnorm]
  have hv : ContinuousAt (translatedV p n) 0 := by
    apply divide_continuousAt
    · unfold inputU inputV mul sq
      fun_prop
    · exact (sq_continuous.comp hd).continuousAt
    · rw [denominator_zero]
      norm_num [sq,mul,qnorm]
  apply continuousAt_pi.mpr
  intro i
  fin_cases i
  · exact hu.fst
  · exact hu.snd
  · exact hv.fst.sub continuousAt_const
  · exact hv.snd

/-- Genuine congruence-neighborhood access for every integer center and
all multipliers. The residue modulus is constructed, not supplied by a caller. -/
theorem access (p : ℕ) [Fact p.Prime]
    (hb : ∀ e : ℕ, ∀ m : ℤ, ‖error p (4*6^e*m)‖≤((p:ℝ)⁻¹)^e)
    (n : ℤ) (U : Set (Fin 4 → ℚ_[p])) (hU : IsOpen U) (hn : error p n∈U) :
    ∃ e : ℕ, ∀ m : ℤ, error p (n+4*6^e*m)∈U := by
  have he : (translate p n) ⁻¹' U∈𝓝 (0 : Fin 4 → ℚ_[p]) :=
    (translate_continuousAt p n) (hU.mem_nhds (by simpa using hn))
  obtain ⟨V,hVU,hV,h0⟩ := mem_nhds_iff.mp he
  obtain ⟨e,he⟩ := access_of_bound p hb V hV h0
  refine ⟨e,fun m => ?_⟩
  have hm := hVU (he m)
  simpa only [Set.mem_preimage,translate_error] using hm

local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩
theorem two_access (n : ℤ) (U : Set (Fin 4 → ℚ_[2])) (hU : IsOpen U) (hn : error 2 n∈U) :
    ∃ e : ℕ, ∀ m : ℤ, error 2 (n+4*6^e*m)∈U :=
  access 2 two_error_bound n U hU hn

theorem three_access (n : ℤ) (U : Set (Fin 4 → ℚ_[3])) (hU : IsOpen U) (hn : error 3 n∈U) :
    ∃ e : ℕ, ∀ m : ℤ, error 3 (n+4*6^e*m)∈U :=
  access 3 three_error_bound n U hU hn

end ActualOrbitTranslatedAccess318
