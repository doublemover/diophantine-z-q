module

public import SelectedGammaOneQuotientArea318
import Mathlib.MeasureTheory.Measure.AEDisjoint

public section

noncomputable section

open Matrix UpperHalfPlane Function Set MeasureTheory MeasureTheory.Measure
open GammaOneAtlas318 GammaOneFiber318 PeterssonQuotient318
open SelectedGammaOneQuotientArea318
open scoped Pointwise MeasureTheory MatrixGroups

namespace SelectedActualAbelExactPeriodSheetArea318

private theorem countableImage (N : ℕ) : Countable (image N) := by
  have hmat : Injective (fun g : SL(2,ℤ) => (fun i j : Fin 2 => g i j)) := by
    intro g h e
    exact Matrix.SpecialLinearGroup.ext g h (fun i j => congrFun (congrFun e i) j)
  letI : Countable (SL(2,ℤ)) := hmat.countable
  let fn (g : CongruenceSubgroup.Gamma1 N) : image N :=
    ⟨positiveMatrix N g,⟨g,rfl⟩⟩
  have hfn : Function.Surjective fn := by
    rintro ⟨g,hg⟩
    obtain ⟨γ,hγ⟩ := hg
    exact ⟨γ,Subtype.ext hγ⟩
  exact hfn.countable

/-- The existing adapted-domain inequality is an equality on restriction to the actual
quotient image of this injective period sheet. This uses the same green canonical
hyperbolic area; no measure on a replacement quotient is introduced. -/
theorem exact_period_sheet_area (N : ℕ) (hN : 5 ≤ N) (B : Set UpperHalfPlane)
    (hB : IsOpen B) (hBI : InjOn (quotientMap N) B) :
    (area N hN).restrict (quotientMap N '' B) =
      (volume.restrict B).map (quotientMap N) := by
  classical
  let q : UpperHalfPlane → Base (image N) := quotientMap N
  let qp := GammaOneAtlas318.quotient_localHomeomorph N hN
  letI : Countable (image N) := countableImage N
  have hq : Measurable q :=
    measurable_quotient_mk' (s := MulAction.orbitRel (image N) UpperHalfPlane)
  have hWopen : IsOpen (q '' B) := qp.isOpenMap _ hB
  have hW : MeasurableSet (q '' B) :=
    measurableSet_quotient.mpr (qp.continuous.isOpen_preimage _ hWopen).measurableSet
  obtain ⟨A,hA,hBA⟩ := adapted_domain N hN B hB hBI
  let C : Set UpperHalfPlane := q ⁻¹' (q '' B) ∩ A
  have hBC : B ⊆ C := fun x hx => ⟨⟨x,hx,rfl⟩,hBA hx⟩
  let D (g : {g : image N // g ≠ 1}) : Set UpperHalfPlane := A ∩ g.val • A
  have hD (g : {g : image N // g ≠ 1}) : volume (D g) = 0 := by
    have h : AEDisjoint (volume : Measure UpperHalfPlane) ((1 : image N) • A) (g.val • A) :=
      hA.aedisjoint (Ne.symm g.property)
    simpa only [D,one_smul] using h.eq
  have hDall : volume (⋃ g, D g) = 0 := by
    exact measure_iUnion_null hD
  have hCD : C \ B ⊆ ⋃ g, D g := by
    rintro x ⟨hxC,hxB⟩
    obtain ⟨b,hb,hbx⟩ := hxC.1
    have hr := @Quotient.exact UpperHalfPlane (MulAction.orbitRel (image N) UpperHalfPlane)
      x b hbx.symm
    obtain ⟨g,hg⟩ := MulAction.orbitRel_apply.mp hr
    have he : g • b = x := hg
    have hg1 : g ≠ 1 := by
      intro hg1
      have hbx' : b = x := by simpa only [hg1,one_smul] using he
      exact hxB (hbx' ▸ hb)
    refine Set.mem_iUnion.mpr ⟨⟨g,hg1⟩,hxC.2,?_⟩
    exact he ▸ Set.smul_mem_smul_set (hBA hb)
  have hCB : volume (C \ B) = 0 := measure_mono_null hCD hDall
  have hBC' : volume (B \ C) = 0 := by
    have he : B \ C = ∅ := by
      ext x
      constructor
      · intro hx
        exact False.elim (hx.2 (hBC hx.1))
      · intro hx
        exact False.elim hx
    rw [he,measure_empty]
  have hC : C =ᵐ[(volume : Measure UpperHalfPlane)] B := ae_eq_set.mpr ⟨hCB,hBC'⟩
  change (area N hN).restrict (q '' B) = (volume.restrict B).map q
  rw [area_from_domain N hN hA]
  change ((volume.restrict A).map q).restrict (q '' B) = (volume.restrict B).map q
  rw [Measure.restrict_map hq hW, Measure.restrict_restrict (hq hW)]
  exact congrArg (Measure.map q) (Measure.restrict_congr_set hC)

end SelectedActualAbelExactPeriodSheetArea318

#print axioms SelectedActualAbelExactPeriodSheetArea318.exact_period_sheet_area
