module
public import ActualCyclicClosure318
public import RealGuardAmbient318
public section
noncomputable section
namespace ActualCyclicGuards318
open Set ActualCyclicClosure318
set_option maxHeartbeats 2000000

/-- The literal four half-trace guards on the genuine two-embedding group.
The right chart is the fixed translate X-generator, not an independent point. -/
@[expose] def guard (n : Fin 4 → ℤ) (j : Fin 4) (X : Pair) : ℝ :=
  ((((n j • (X-generator)) 0).val.1^2-((n j • X) 0).val.1^2)+
   (((n j • (X-generator)) 1).val.1^2-((n j • X) 1).val.1^2))/2

lemma guard_continuous (n : Fin 4 → ℤ) (j : Fin 4) : Continuous (guard n j) := by
  unfold guard
  fun_prop

lemma scaled_orbit (k h : ℤ) : k • pairOrbit h=pairOrbit (k*h) := by
  rw [pairOrbit_zsmul,pairOrbit_zsmul,mul_smul]

lemma shifted_orbit (k h : ℤ) : k • (pairOrbit h-generator)=pairOrbit (k*(h-1)) := by
  have hh : pairOrbit h-generator=pairOrbit (h-1) := by
    rw [pairOrbit_zsmul,pairOrbit_zsmul,sub_zsmul,one_zsmul,sub_eq_add_neg]
  rw [hh,scaled_orbit]

/-- Exact equality with the already verified literal source guard, for all
integers h and all four source labels. -/
theorem guard_pairOrbit (n : Fin 4 → ℤ) (j : Fin 4) (h : ℤ) :
    guard n j (pairOrbit h)=RealGuardAmbient318.guard j (RealQuarticAmbient318.orbit n h) := by
  simp only [guard,scaled_orbit,shifted_orbit,pairOrbit,RealCoherentOrbit318.orbit,
    RealGuardAmbient318.guard,RealQuarticAmbient318.orbit,
    CoherentMultiplePrefix318.u,CoherentMultiplePrefix318.parameters,
    Fin.append_left,Fin.append_right,ite_true]

lemma guard_zero_positive (n : Fin 4 → ℤ) (j : Fin 4) (hn : n j≠0) : 0<guard n j 0 := by
  have hzero : pairOrbit 0=0 := by rw [pairOrbit_zsmul,zero_zsmul]
  rw [←hzero,guard_pairOrbit]
  exact RealGuardAmbient318.identity_guard_positive n j hn

/-- A real open good neighborhood exists on the actual cyclic closure, and
positive-tail recurrence gives arbitrarily large simultaneous guard witnesses.
This does not assert intersection with the separate scalar-bound region. -/
theorem arbitrarily_large_actual_guards (n : Fin 4 → ℤ) (hn : ∀ j, n j≠0) (B : ℕ) :
    ∃ h : ℕ, B<h ∧ ∀ j : Fin 4,
      RealGuardTrace318.guardValue (n j) ((h:ℤ) • LocalGenerator318.P)≠0 := by
  let U : Set cyclicClosure := {x | ∀ j : Fin 4, 0<guard n j x.val}
  have ho : IsOpen U := by
    have he : U=⋂ j : Fin 4, {x : cyclicClosure | 0<guard n j x.val} := by ext x; simp [U]
    rw [he]
    exact isOpen_iInter_of_finite fun j => isOpen_lt continuous_const
      ((guard_continuous n j).comp continuous_subtype_val)
  have hne : U.Nonempty := ⟨0,fun j => guard_zero_positive n j (hn j)⟩
  obtain ⟨h,hB,hh⟩ := ActualCyclicClosure318.positive_tail U ho hne B
  refine ⟨h,hB,?_⟩
  intro j
  have hp : 0<guard n j ((h • generatorInClosure : cyclicClosure) : Pair) := hh j
  have he : ((h • generatorInClosure : cyclicClosure) : Pair)=pairOrbit (h:ℤ) := by
    simpa only [natCast_zsmul] using coe_integer_multiple (h:ℤ)
  rw [he,guard_pairOrbit,RealGuardAmbient318.guard_orbit] at hp
  exact ne_of_gt (by exact_mod_cast hp)

end ActualCyclicGuards318
