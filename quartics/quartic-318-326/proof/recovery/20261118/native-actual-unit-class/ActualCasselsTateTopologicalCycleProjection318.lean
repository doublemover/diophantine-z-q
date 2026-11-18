module
public import Mathlib.Algebra.Category.ModuleCat.Topology.Homology
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public section
noncomputable section

/-! Underlying zero-class criterion in the genuine topological-module
category. Uses the literal algebraic image, not the closure of the image. -/
namespace ActualCasselsTateTopologicalCycleProjection318
open CategoryTheory Limits
variable {k : Type*} [Ring k] [TopologicalSpace k]
variable (S : ShortComplex (TopModuleCat k))

/-- Explicit left homology data, the same kernel and cokernel chosen in
the native construction of CategoryWithHomology for topological modules. -/
set_option backward.isDefEq.respectTransparency false in
def concreteLeft : S.LeftHomologyData :=
  ⟨_,_,_,_,_,TopModuleCat.isLimitKer _,by simp,TopModuleCat.isColimitCoker _⟩

private theorem concrete_projection_zero (a : (concreteLeft S).K) :
    (concreteLeft S).π a = 0 ↔ ∃ x : S.X₁, (concreteLeft S).f' x = a := by
  change (Submodule.Quotient.mk a : _ ⧸ (concreteLeft S).f'.hom.range) = 0 ↔
    a ∈ (concreteLeft S).f'.hom.range
  exact Submodule.Quotient.mk_eq_zero _

/-- This tests the image of the actual canonical projection evaluated
on the specified cycle, not an independently chosen representative. -/
theorem native_class_eq_zero_iff (y : S.cycles) :
    S.homologyπ y = 0 ↔ ∃ x : S.X₁, S.f x = S.iCycles y := by
  let h := concreteLeft S
  have hp := congrArg (fun f : S.cycles ⟶ h.H => f y) h.homologyπ_comp_homologyIso_hom
  change h.homologyIso.hom (S.homologyπ y) = h.π (h.cyclesIso.hom y) at hp
  have hi := congrArg (fun f : S.cycles ⟶ S.X₂ => f y) h.cyclesIso_hom_comp_i
  change h.i (h.cyclesIso.hom y) = S.iCycles y at hi
  have hfi (x : S.X₁) : h.i (h.f' x) = S.f x :=
    congrArg (fun f : S.X₁ ⟶ S.X₂ => f x) h.f'_i
  have hi_inj : Function.Injective h.i := by
    exact Subtype.val_injective
  constructor
  · intro hzero
    have hq : h.π (h.cyclesIso.hom y) = 0 := by
      rw [←hp,hzero]
      exact h.homologyIso.hom.hom.map_zero
    obtain ⟨x,hx⟩ := (concrete_projection_zero S _).mp hq
    exact ⟨x,(hfi x).symm.trans ((congrArg h.i hx).trans hi)⟩
  · rintro ⟨x,hx⟩
    have he : h.f' x = h.cyclesIso.hom y :=
      hi_inj ((hfi x).trans (hx.trans hi.symm))
    have hq := (concrete_projection_zero S _).mpr ⟨x,he⟩
    apply (ConcreteCategory.bijective_of_isIso h.homologyIso.hom).1
    exact (hp.trans hq).trans h.homologyIso.hom.hom.map_zero.symm
end ActualCasselsTateTopologicalCycleProjection318
