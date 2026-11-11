module
public import SectionZeroSquareIdeal318
public section
noncomputable section
namespace SectionZeroPullbackCover318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace LineSheafClass318
universe u
variable {Z X Y : Scheme.{u}} (p : Z ⟶ X) (L : Line X) (s : Γ(L.object,⊤))
  (D : SectionZeroChartData318.Data p L s) (g : Y ⟶ X)
@[expose] def oldCover : X.OpenCover where
  I₀ := D.Index
  X i := Spec (D.ring i)
  f := D.into
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_,fun i => inferInstance⟩
    intro x
    obtain ⟨i,hi⟩ := Opens.mem_iSup.mp (D.cover (show x∈(⊤:X.Opens) from trivial))
    exact ⟨i,hi⟩
abbrev pulled := (oldCover p L s D).pullback₁ g
@[expose] def cover : Y.AffineOpenCover := (pulled p L s D g).affineRefinement
abbrev index := (cover p L s D g).I₀
variable (i : index p L s D g)
abbrev ring : CommRingCat.{u} := (cover p L s D g).X i
abbrev into : Spec (ring p L s D g i) ⟶ Y := (cover p L s D g).f i
abbrev toOld : Spec (ring p L s D g i) ⟶ Spec (D.ring i.1) :=
  ((pulled p L s D g).X i.1).affineOpenCover.f i.2 ≫ pullback.snd g (D.into i.1)
@[expose] def ringMap : D.ring i.1 ⟶ ring p L s D g i := Spec.preimage (toOld p L s D g i)
lemma spec_ringMap : Spec.map (ringMap p L s D g i)=toOld p L s D g i := Spec.map_preimage _
lemma square : Spec.map (ringMap p L s D g i) ≫ D.into i.1=into p L s D g i ≫ g := by
  rw [spec_ringMap]
  change (_ ≫ pullback.snd g (D.into i.1)) ≫ D.into i.1=
    (_ ≫ pullback.fst g (D.into i.1)) ≫ g
  rw [Category.assoc,Category.assoc,pullback.condition]
/-- The entire affine refinement of the actual pulled original cover. -/
lemma covers : ⊤≤⨆i : index p L s D g,(into p L s D g i).opensRange := by
  intro x _
  obtain ⟨i,y,hy⟩ := (cover p L s D g).openCover.exists_eq x
  exact (le_iSup (fun i : index p L s D g => (into p L s D g i).opensRange) i) ⟨y,hy⟩
end SectionZeroPullbackCover318
