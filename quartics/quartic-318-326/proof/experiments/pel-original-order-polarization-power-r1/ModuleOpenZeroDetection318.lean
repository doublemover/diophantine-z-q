module
public import ModuleLocalGluing318
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public section
noncomputable section
namespace ModuleOpenZeroDetection318
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
lemma subopen_zero (U : X.Opens) (h : (Scheme.Modules.restrictFunctor U.ι).map φ=0)
    (W : X.Opens) (hW : W≤U) : φ.app W=0 := by
  have hn := (Scheme.Modules.overFunctorEquiv U).hom.naturality φ
  simp only [Functor.comp_map] at hn
  rw [h,comp_zero] at hn
  have he : (Scheme.Modules.overEquiv U).functor.map
      ((SheafOfModules.overFunctor X.ringCatSheaf U).map φ)=0 := by
    apply (cancel_mono ((Scheme.Modules.overFunctorEquiv U).hom.app N)).1
    simpa only [zero_comp] using hn
  have ho : (SheafOfModules.overFunctor X.ringCatSheaf U).map φ=0 := by
    apply (Scheme.Modules.overEquiv U).functor.map_injective
    simpa only [Functor.map_zero] using he
  exact congrArg (fun ψ => ψ.val.app (op (Over.mk (homOfLE hW)))) ho

/-- The actual open restriction functors detect zero module morphisms
on an arbitrary full open cover, without reducedness or freeness. -/
lemma zero_iff {ι : Type u} (U : ι → X.Opens) (hc : (⊤ : X.Opens)≤⨆ i,U i) :
    φ=0 ↔ ∀ i,(Scheme.Modules.restrictFunctor (U i).ι).map φ=0 := by
  constructor
  · intro h i; rw [h,Functor.map_zero]
  · intro h
    apply Scheme.Modules.hom_ext
    intro W
    ext s
    apply ModuleLocalGluing318.ext_value (N := N) (U := U) hc W
    intro i
    have hn := congrArg (fun f => f s)
      (φ.mapPresheaf.naturality (homOfLE (show W⊓U i≤W from inf_le_left)).op)
    change φ.app (W⊓U i) (M.presheaf.map (homOfLE inf_le_left).op s)=
      N.presheaf.map (homOfLE inf_le_left).op (φ.app W s) at hn
    rw [subopen_zero φ (U i) (h i) (W⊓U i) inf_le_right] at hn
    simpa only [map_zero,zero_apply] using hn.symm
end ModuleOpenZeroDetection318
