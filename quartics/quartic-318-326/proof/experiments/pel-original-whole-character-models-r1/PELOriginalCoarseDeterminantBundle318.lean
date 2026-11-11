module
public import PELOriginalContinuousDeterminantCocycle318
public import Mathlib.Topology.VectorBundle.Basic
public section
noncomputable section
namespace PELOriginalCoarseDeterminantBundle318
open QuaternionicJointPeriodTopology318 PELEffectiveNormOneAction318
open PELUnlevelledComplexBase318 PELOriginalDeterminantCover318
open PELOriginalContinuousDeterminantCocycle318 Filter
open scoped Topology

/-- Coordinate change from chart a to chart b. The actual exterior
monodromy maps b back to a, so the bundle uses its INVERSE coefficient. -/
@[expose] def transition (a b : HalfPlane) (q : UnlevelledBase) : ℂ :=
  (scalar (shift a b q) (chart a q))⁻¹
lemma transition_self (a : HalfPlane) (q : UnlevelledBase) : transition a a q=1 := by
  simp [transition,shift_self,scalar_one]
lemma transition_ne (a b : HalfPlane) (q : UnlevelledBase) : transition a b q≠0 :=
  inv_ne_zero (scalar_nonzero _ _)
lemma transition_comp (a b c : HalfPlane) (q : UnlevelledBase)
    (ha : q∈baseSet a) (hb : q∈baseSet b) (hc : q∈baseSet c) :
    transition b c q*transition a b q=transition a c q := by
  have he := scalar_cocycle (shift b c q) (shift a b q) (chart a q)
  rw [shift_spec a b q ha hb,shift_comp a b c q ha hb hc] at he
  simp only [transition]
  rw [←he,mul_inv_rev]
lemma transition_continuous (a b : HalfPlane) :
    ContinuousOn (transition a b) (baseSet a∩baseSet b) := by
  intro q hq
  apply ContinuousAt.continuousWithinAt
  have h := ((scalar_continuous (shift a b q)).continuousAt.comp
    ((chart a).continuousAt hq.1)).inv (scalar_nonzero _ _)
  apply h.congr_of_eventuallyEq
  filter_upwards [shift_locally_constant a b q hq.1 hq.2] with r hr
  simp only [transition,hr]

/-- Genuine complex line bundle on the SAME effective coarse original
base. It uses the actual exterior monodromy, whose central sign vanishes;
no rank-two bundle descent is asserted. -/
@[expose] def core : VectorBundleCore ℂ UnlevelledBase ℂ HalfPlane where
  baseSet := baseSet
  isOpen_baseSet a := (chart a).open_source
  indexAt q := (projection_surjective q).choose
  mem_baseSet_at q := by
    have h := covering.isLocalHomeomorph.apply_self_mem_localInverseAt_source
      (x:=(projection_surjective q).choose)
    simpa only [(projection_surjective q).choose_spec] using h
  coordChange a b q := transition a b q • ContinuousLinearMap.id ℂ ℂ
  coordChange_self a q _ v := by simp [transition_self]
  continuousOn_coordChange a b :=
    (transition_continuous a b).smul continuousOn_const
  coordChange_comp a b c q hq v := by
    simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,smul_eq_mul]
    rw [←mul_assoc,transition_comp a b c q hq.1.1 hq.1.2 hq.2]
abbrev Fiber (q : UnlevelledBase) : Type := core.Fiber q
abbrev Total : Type := core.TotalSpace
instance fiberBundle : FiberBundle ℂ Fiber := core.fiberBundle
instance vectorBundle : VectorBundle ℂ ℂ Fiber := core.vectorBundle
lemma rank_one (q : UnlevelledBase) : Module.finrank ℂ (Fiber q)=1 := by
  change Module.finrank ℂ ℂ=1
  exact Module.finrank_self ℂ
lemma projection_continuous : Continuous core.proj := core.continuous_proj
lemma actual_transition (a b : HalfPlane) (q : UnlevelledBase) :
    core.coordChange a b q=(scalar (shift a b q) (chart a q))⁻¹ •
      ContinuousLinearMap.id ℂ ℂ := rfl
end PELOriginalCoarseDeterminantBundle318
