module
public import ReducedComplexPointMorphisms318
public import Mathlib.AlgebraicGeometry.Properties
public section
noncomputable section
namespace ReducedSchemeGlobalFunctionSeparation318
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X : Scheme} (π : X ⟶ Spec (CommRingCat.of ℂ)) [LocallyOfFiniteType π]

/-- Genuine regular functions on any reduced finite-type complex scheme,
not only an affine scheme, are determined by ALL complex-valued scheme
points. Closed-point density and the actual basic-open criterion kill
nilpotents only after reducedness has explicitly been supplied. -/
theorem eq_zero [IsReduced X] (s : Γ(X,⊤))
    (h : ∀ p : Spec (CommRingCat.of ℂ) ⟶ X, p≫π=𝟙 _ → p.appTop s=0) : s=0 := by
  letI := LocallyOfFiniteType.jacobsonSpace π
  apply eq_zero_of_basicOpen_eq_bot
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨y,hy,hyc⟩ := nonempty_inter_closedPoints
    (show (X.basicOpen s : Set X).Nonempty from ⟨x,hx⟩)
    (X.basicOpen s).isOpen.isLocallyClosed
  let p := pointOfClosedPoint π y hyc
  have hp : p≫π=𝟙 _ := pointOfClosedPoint_comp π y hyc
  have hm : IsLocalRing.closedPoint ℂ ∈ p ⁻¹ᵁ X.basicOpen s := by
    change p (IsLocalRing.closedPoint ℂ) ∈ X.basicOpen s
    simpa only [p,pointOfClosedPoint_apply] using hy
  rw [Scheme.preimage_basicOpen_top,h p hp,Scheme.basicOpen_zero] at hm
  exact hm.elim

/-- Full equality of global regular functions, retaining exact maps on
Γ(Spec C) instead of silently identifying an arbitrary scalar structure. -/
theorem ext [IsReduced X] (s t : Γ(X,⊤))
    (h : ∀ p : Spec (CommRingCat.of ℂ) ⟶ X, p≫π=𝟙 _ → p.appTop s=p.appTop t) : s=t := by
  apply sub_eq_zero.mp
  apply eq_zero π (s-t)
  intro p hp
  rw [map_sub,h p hp,sub_self]

/-- Nonvanishing at every genuine complex point implies an actual
GLOBAL REGULAR UNIT. The proof treats all nonclosed scheme points via
Jacobson density of the closed vanishing locus, then uses the genuine
ringed-space local criterion for invertibility. -/
theorem isUnit (s : Γ(X,⊤))
    (h : ∀ p : Spec (CommRingCat.of ℂ) ⟶ X, p≫π=𝟙 _ → IsUnit (p.appTop s)) : IsUnit s := by
  letI := LocallyOfFiniteType.jacobsonSpace π
  have hb : X.basicOpen s=⊤ := by
    apply top_le_iff.mp
    intro x hx
    by_contra hx'
    obtain ⟨y,hy,hyc⟩ := nonempty_inter_closedPoints
      (show ((X.basicOpen s : Set X)ᶜ).Nonempty from ⟨x,hx'⟩)
      (X.basicOpen s).isOpen.isClosed_compl.isLocallyClosed
    let p := pointOfClosedPoint π y hyc
    have hp : p≫π=𝟙 _ := pointOfClosedPoint_comp π y hyc
    have hm : IsLocalRing.closedPoint ℂ ∈ p ⁻¹ᵁ X.basicOpen s := by
      rw [Scheme.preimage_basicOpen_top,Scheme.basicOpen_of_isUnit _ (h p hp)]
      trivial
    change p (IsLocalRing.closedPoint ℂ) ∈ X.basicOpen s at hm
    rw [show p (IsLocalRing.closedPoint ℂ)=y from pointOfClosedPoint_apply π y hyc] at hm
    exact hy hm
  apply X.toRingedSpace.isUnit_of_isUnit_germ ⊤ s
  intro x hx
  exact (X.mem_basicOpen_top s x).mp (by rw [hb]; trivial)
end ReducedSchemeGlobalFunctionSeparation318
