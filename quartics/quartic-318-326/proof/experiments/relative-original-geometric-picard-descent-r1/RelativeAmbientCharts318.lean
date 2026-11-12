module
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Gluing
public section
noncomputable section
namespace RelativeAmbientCharts318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {C B S T D : Scheme.{u}} (q : C ⟶ S) (b : B ⟶ S)
  (j : T ⟶ B) (a : D ⟶ C) (d : D ⟶ T)
  (h : IsPullback a d q (j ≫ b))

/-- A specified original Cartesian coefficient model maps canonically
into the relative ambient scheme, with both original projections. -/
@[expose] def lift : D ⟶ pullback q b :=
  pullback.lift a (d ≫ j) (by simpa only [Category.assoc] using h.w)
@[reassoc] lemma lift_original : lift q b j a d h ≫ pullback.fst q b=a := pullback.lift_fst ..
@[reassoc] lemma lift_projection : lift q b j a d h ≫ pullback.snd q b=d ≫ j :=
  pullback.lift_snd ..

lemma square : IsPullback (lift q b j a d h) d (pullback.snd q b) j := by
  apply IsPullback.of_right (h₁₂:=pullback.fst q b) (h₂₂:=b)
  · simpa only [lift_original] using h
  · exact lift_projection q b j a d h
  · exact .of_hasPullback _ _

instance openImmersion [IsOpenImmersion j] : IsOpenImmersion (lift q b j a d h) := by
  rw [← (square q b j a d h).isoPullback_hom_fst]
  infer_instance

/-- These are a full ambient open cover whenever the coefficient charts
cover. Actual Cartesian scheme points are used only to prove coverage;
all later comparisons retain their full scheme pullback squares. -/
lemma covers (U : B.OpenCover) (D : U.I₀ → Scheme.{u})
    (a : ∀ i,D i ⟶ C) (d : ∀ i,D i ⟶ U.X i)
    (hs : ∀ i,IsPullback (a i) (d i) q (U.f i ≫ b))
    (x : pullback q b) :
    ∃ i,x ∈ Set.range (lift q b (U.f i) (a i) (d i) (hs i)) := by
  let i := U.idx ((pullback.snd q b) x)
  obtain ⟨t,ht⟩ := U.covers ((pullback.snd q b) x)
  obtain ⟨z,hzx,_⟩ := Scheme.Pullback.exists_preimage_pullback
    (f:=pullback.snd q b) (g:=U.f i) x t ht.symm
  refine ⟨i,(square q b (U.f i) (a i) (d i) (hs i)).isoPullback.inv z,?_⟩
  rw [← Scheme.Hom.comp_apply,(square q b (U.f i) (a i) (d i) (hs i)).isoPullback_inv_fst]
  exact hzx
end RelativeAmbientCharts318
