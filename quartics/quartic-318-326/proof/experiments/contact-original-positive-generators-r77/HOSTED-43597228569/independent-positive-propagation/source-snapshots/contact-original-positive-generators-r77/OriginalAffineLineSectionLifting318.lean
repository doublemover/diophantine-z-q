module
public import OriginalLineRestrictionAdditive318
public section
noncomputable section
namespace OriginalAffineLineSectionLifting318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open LineSheafClass318 LocalSheafCohomologySections318 Opposite
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : CommRingCat.{0}} [IsDomain R] (L : Line (Spec R))

/-- The genuine kernel line's proved Ext vanishing gives lifting of every
original section in any short exact sequence with that actual kernel. -/
theorem surjective (S : ShortComplex (ASheaf (X:=Spec R))) (hS : S.ShortExact)
    (e : S.X₁ ≅ OriginalLineRestrictionAdditive318.additive L) :
    Function.Surjective (S.g.hom.app (op ⊤)) := by
  intro s
  let y : S.X₃.H' 0 ⊤ := (zeroEquiv S.X₃ ⊤).symm s
  have hz : y.comp hS.extClass (by rfl : 0+1=1) = 0 := by
    apply ExtFiniteRetractVanishing318.eq_zero
      (fun _ : PUnit.{1} => OriginalLineRestrictionAdditive318.additive L)
      (fun _ => e.hom) (fun _ => e.inv) (by simp) 1
    intro i z
    exact OriginalAffineLineLocalHOne318.eq_zero R L ⊤ (isAffineOpen_top _) z
  obtain ⟨z,hz⟩ := Ext.covariant_sequence_exact₃ (generator (⊤ : (Spec R).Opens)) hS y rfl hz
  refine ⟨zeroEquiv S.X₂ ⊤ z,?_⟩
  have h := congrArg (zeroEquiv S.X₃ ⊤) hz
  rw [zeroEquiv_naturality] at h
  exact h.trans ((zeroEquiv S.X₃ ⊤).apply_symm_apply s)
end OriginalAffineLineSectionLifting318
