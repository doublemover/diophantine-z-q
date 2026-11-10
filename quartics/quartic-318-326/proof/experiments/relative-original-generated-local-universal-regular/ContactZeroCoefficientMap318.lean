module
public import ContactZeroCoefficientCharts318
public section
noncomputable section
namespace ContactZeroCoefficientMap318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalSectionZeros318
open ContactCoefficientNativeSections318 ContactRelativeCoefficientChange318
open ContactGlobalSectionZero318 ContactZeroCoefficientCharts318
variable (R S : CommRingCat.{0}) [Algebra ℚ R] [Algebra ℚ S]
  (f : R →ₐ[ℚ] S) (c : Fin 4 → ℚˣ) (L : Line (curve R c)) (s : Γ(L.object,⊤))

lemma finite_into : finiteMap R S f c L s ≫ finiteIntoOriginal R c L s =
    finiteIntoOriginal S c (L' R S f c L) (pulledSection R S f c L s) ≫ curveMap R S f c := by
  have h := (finite_pullback R S f c L s).w
  change _ ≫ (_ ≫ finiteInto R c) = (_ ≫ finiteInto S c) ≫ curveMap R S f c
  rw [← Category.assoc,← h,Category.assoc,ContactRelativeCoefficientChange318.finite_square,Category.assoc]
lemma infinity_into : infinityMap R S f c L s ≫ infinityIntoOriginal R c L s =
    infinityIntoOriginal S c (L' R S f c L) (pulledSection R S f c L s) ≫ curveMap R S f c := by
  have h := (infinity_pullback R S f c L s).w
  change _ ≫ (_ ≫ infinityInto R c) = (_ ≫ infinityInto S c) ≫ curveMap R S f c
  rw [← Category.assoc,← h,Category.assoc,ContactRelativeCoefficientChange318.infinity_square,Category.assoc]

lemma zero_compatibility :
    toFinite S c (L' R S f c L) (pulledSection R S f c L s) ≫
        (finiteMap R S f c L s ≫ finiteChart R c L s) =
    toInfinity S c (L' R S f c L) (pulledSection R S f c L s) ≫
        (infinityMap R S f c L s ≫ infinityChart R c L s) := by
  apply (cancel_mono (ContactGlobalSectionZero318.into R c L s)).mp
  simp only [Category.assoc,finiteChart_into,infinityChart_into]
  rw [finite_into,infinity_into]
  simp only [← Category.assoc]
  rw [ContactGlobalSectionZero318.compatible]

/-- Actual global coefficient morphism of the original section-zero
schemes, glued from quotient maps of the SAME coefficient-pulled section. -/
@[expose] def map : scheme S c (L' R S f c L) (pulledSection R S f c L s) ⟶ scheme R c L s :=
  pushout.desc (finiteMap R S f c L s ≫ finiteChart R c L s)
    (infinityMap R S f c L s ≫ infinityChart R c L s) (zero_compatibility R S f c L s)

@[simp,reassoc] lemma finiteChart_map :
    finiteChart S c (L' R S f c L) (pulledSection R S f c L s) ≫ map R S f c L s =
      finiteMap R S f c L s ≫ finiteChart R c L s := pushout.inl_desc ..
@[simp,reassoc] lemma infinityChart_map :
    infinityChart S c (L' R S f c L) (pulledSection R S f c L s) ≫ map R S f c L s =
      infinityMap R S f c L s ≫ infinityChart R c L s := pushout.inr_desc ..

@[reassoc] lemma map_into : map R S f c L s ≫ ContactGlobalSectionZero318.into R c L s =
    ContactGlobalSectionZero318.into S c (L' R S f c L) (pulledSection R S f c L s) ≫ curveMap R S f c := by
  apply pushout.hom_ext
  · change finiteChart S c (L' R S f c L) (pulledSection R S f c L s) ≫ _ = _
    rw [← Category.assoc,finiteChart_map,Category.assoc,finiteChart_into,
      ← Category.assoc,finiteChart_into,finite_into]
  · change infinityChart S c (L' R S f c L) (pulledSection R S f c L s) ≫ _ = _
    rw [← Category.assoc,infinityChart_map,Category.assoc,infinityChart_into,
      ← Category.assoc,infinityChart_into,infinity_into]
end ContactZeroCoefficientMap318
