module
public import Mathlib.RingTheory.PowerSeries.Evaluation
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Tactic
public section
noncomputable section
namespace AdicEvaluation318
set_option maxHeartbeats 600000
open PowerSeries
variable {A R:Type*} [CommRing A] [CommRing R] [WithIdeal R]
  [T2Space R] [CompleteSpace R]

/-- The coefficient ring is given the discrete uniformity. Thus any actual
coefficient hom is continuous; no boundedness or residue-characteristic
assumption is introduced. -/
@[expose] def eval (f:A→+*R) (x:R) (hx:x∈(WithIdeal.i:Ideal R)) : A⟦X⟧→+*R := by
  letI : UniformSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  exact PowerSeries.eval₂Hom (continuous_of_discreteTopology : Continuous f)
    (WithIdeal.isTopologicallyNilpotent_of_mem hx)

@[simp] theorem eval_C (f:A→+*R) (x:R) (hx:x∈(WithIdeal.i:Ideal R)) (a:A) :
    eval f x hx (C a)=f a := by
  letI : UniformSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  change PowerSeries.eval₂Hom _ _ (C a)=f a
  rw [PowerSeries.coe_eval₂Hom,PowerSeries.eval₂_C]

@[simp] theorem eval_X (f:A→+*R) (x:R) (hx:x∈(WithIdeal.i:Ideal R)) :
    eval f x hx X=x := by
  letI : UniformSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  change PowerSeries.eval₂Hom _ _ X=x
  rw [PowerSeries.coe_eval₂Hom,PowerSeries.eval₂_X]

end AdicEvaluation318
