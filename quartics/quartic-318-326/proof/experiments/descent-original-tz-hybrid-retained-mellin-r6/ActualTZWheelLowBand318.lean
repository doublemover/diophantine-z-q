module
public import ActualTZWheelZero318
public import ActualTZLowFrequencyPole318
public section
noncomputable section
namespace ActualTZWheelLowBand318
open scoped BigOperators
open ActualTZWheelZero318 ActualTZReferenceFactorNearOne318
open ActualTZRegulatedZetaAlgebra318 ActualTZLowFrequencyPole318

variable {I : Type*} [Fintype I]
abbrev Input (I : Type*) := (I→ℂ) × (I→ℂ)

private theorem atom_continuous (p : ℕ) (hp : p.Prime) (i : I) :
    ContinuousAt (fun z : Input I => B p (z.1 i) (z.2 i)) 0 := by
  have hpC : (p:ℂ)≠0 := by exact_mod_cast hp.ne_zero
  have hU : Continuous (fun z : Input I => (p:ℂ)^(-z.1 i)) :=
    (Complex.continuous_const_cpow' hpC).comp (((continuous_apply i).comp continuous_fst).neg)
  have hV : Continuous (fun z : Input I => (p:ℂ)^(-z.2 i)) :=
    (Complex.continuous_const_cpow' hpC).comp (((continuous_apply i).comp continuous_snd).neg)
  unfold B oneSite
  have h₁ : Continuous (fun _ : Input I => (1:ℂ)) := continuous_const
  have hx : Continuous (fun _ : Input I => (1:ℂ)/(p:ℂ)) := continuous_const
  have Hnum := (h₁.sub (hx.mul hU)).mul (h₁.sub (hx.mul hV))
  have Hden := h₁.sub ((hx.mul hU).mul hV)
  apply Hnum.continuousAt.div Hden.continuousAt
  change 1-(1/(p:ℂ))*(p:ℂ)^(-(0:ℂ))*(p:ℂ)^(-(0:ℂ))≠0
  simpa only [neg_zero,Complex.cpow_zero,mul_one] using atom_den_ne p hp

private theorem finite_continuous {X J : Type*} [TopologicalSpace X]
    (S : Finset J) (x : X) (f : J→X→ℂ) (H : ∀ j∈S,ContinuousAt (f j) x) :
    ContinuousAt (fun u => ∏ j∈S,f j u) x := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using (continuousAt_const (c := (1:ℂ)))
  | @insert j T hj ih =>
    simp only [Finset.prod_insert hj]
    exact (H j (Finset.mem_insert_self _ _)).mul (ih (fun i hi => H i (Finset.mem_insert_of_mem hi)))

private theorem wheel_continuous (W : ℕ) :
    ContinuousAt (fun z : Input I => wheel W z.1 z.2) 0 := by
  unfold wheel
  apply finite_continuous
  intro p hp
  apply finite_continuous
  intro i _
  exact atom_continuous p (Nat.mem_primeFactors.mp hp).1 i

@[expose] def multiplier (W : ℕ) (s t : I→ℂ) : ℂ :=
  (alpha W)^Fintype.card I/wheel W s t

theorem multiplier_zero (W : ℕ) (hW : 0<W) :
    multiplier W (0 : I→ℂ) 0=1 := by
  rw [multiplier,wheel_zero W hW,div_self (pow_ne_zero _ (alpha_ne_zero W hW))]

/-- The original fixed wheel tends to one uniformly on the literal
angular band once W is fixed. The threshold may depend on W and
epsilon; it is not an extra uniform-in-y limit. -/
theorem fixed_wheel_uniform (W : ℕ) (hW : 0<W) (ε : ℝ) (hε : 0<ε) :
    ∃ L₀≥(1:ℝ),∀ L≥L₀,∀ ξ η : I→ℝ,
      (∀ i,|ξ i|≤band L) → (∀ i,|η i|≤band L) →
      ‖multiplier W (fun i=>shift L (ξ i)) (fun i=>shift L (η i))-1‖<ε := by
  have H : ContinuousAt (fun z : Input I => multiplier W z.1 z.2) 0 := by
    unfold multiplier
    apply (continuousAt_const.div (wheel_continuous W))
    change wheel W (0 : I→ℂ) 0≠0
    rw [wheel_zero W hW]
    exact pow_ne_zero _ (alpha_ne_zero W hW)
  obtain ⟨r,hr,hM⟩ := (Metric.continuousAt_iff.mp H) ε hε
  obtain ⟨L₀,h₀,hD⟩ := disk_on_band r hr
  refine ⟨L₀,h₀,?_⟩
  intro L hL ξ η hξ hη
  let z : Input I := (fun i=>shift L (ξ i),fun i=>shift L (η i))
  have hz : dist z 0 < r := by
    rw [dist_zero_right,Prod.norm_def,max_lt_iff]
    exact ⟨(pi_norm_lt_iff hr).2 (fun i => (hD L hL (ξ i) (η i) (hξ i) (hη i)).1),
      (pi_norm_lt_iff hr).2 (fun i => (hD L hL (ξ i) (η i) (hξ i) (hη i)).2.1)⟩
  have h := hM hz
  change dist (multiplier W z.1 z.2) (multiplier W (0 : I→ℂ) 0) < ε at h
  simpa only [multiplier_zero W hW,dist_eq_norm,z] using h

end ActualTZWheelLowBand318
