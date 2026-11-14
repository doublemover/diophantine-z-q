module
public import OriginalTensorChartRestriction318
public import ContactOriginalLaurentCoordinates318
public section
noncomputable section
namespace ContactOriginalRestrictionCoordinates318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalLineBothCharts318 ContactOriginalLaurentOverlap318
open scoped ChangeOfRings
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private lemma inverse_hom_apply {R : Type*} [Ring R]
    {M N : ModuleCat R} (e : M ≅ N) (x : M) :
    e.toLinearEquiv.symm (e.hom x) = x := by
  rw [← Iso.toLinearEquiv_apply, LinearEquiv.symm_apply_apply]

private lemma inverse_hom_trans_apply {R : Type*} [Ring R]
    {M N P : ModuleCat R} (e : M ≅ P) (g : N ≅ P) (x : N) :
    e.toLinearEquiv.symm (g.hom x) = (g ≪≫ e.symm).toLinearEquiv x := rfl

variable (c : Fin 4 → ℚˣ) (L : Line (ContactProjectiveModel318.model c))

/-- Coordinates on the SAME original common overlap module. -/
def coordinates :=
  (ContactCommonLaurentModule318.finiteIso c L).toLinearEquiv.symm.trans
    (ContactOriginalLaurentCoordinates318.finiteCoordinates c L)

/-- Finite-chart restriction defined geometrically, by the original pullback
unit on the genuine tensor chart and its original overlap recovery. -/
def finiteRestriction (m : finiteSections c L) : ContactCommonLaurentModule318.common c L :=
  (OriginalTensorChartRestriction318.chartRecovery
    (CommRingCat.of (Polynomial ℚ)) (CommRingCat.of OriginalLaurentProjectiveOverlap318.Ring)
    (CommRingCat.of (ContactKummerOrder318.SourceOrder c))
    (finiteLine c L) (projection c) (finiteEdge c)
    (ContactOverlapTensorCharts318.finiteIso c).symm
    (ContactOverlapTensorCharts318.finiteIso_inv_base c)
    (ContactOverlapTensorCharts318.finiteIso_inv_chart c)
    (ContactOriginalLineOverlap318.line c L).object
    (ContactOriginalLineOverlap318.finiteComparison c L)).hom
      ((TildePullback318.globalNatIso
        (AffineModuleBaseChange318.rightMap (CommRingCat.of (Polynomial ℚ))
          (CommRingCat.of OriginalLaurentProjectiveOverlap318.Ring)
          (CommRingCat.of (ContactKummerOrder318.SourceOrder c)))).hom.app _
        (moduleSpecΓFunctor.map
          ((Scheme.Modules.pullbackPushforwardAdjunction
            (Spec.map (AffineModuleBaseChange318.rightMap (CommRingCat.of (Polynomial ℚ))
              (CommRingCat.of OriginalLaurentProjectiveOverlap318.Ring)
              (CommRingCat.of (ContactKummerOrder318.SourceOrder c))))).unit.app
            (finiteLine c L).object) m))

/-- Reciprocal-chart restriction uses the same geometric construction, with
its actual u↦T⁻¹ scalar action, and ends in the SAME common overlap module. -/
def infinityRestriction (m : infinitySections c L) : ContactCommonLaurentModule318.common c L := by
  letI := OriginalLaurentProjectiveOverlap318.infinityHom.toAlgebra
  exact (OriginalTensorChartRestriction318.chartRecovery
    (CommRingCat.of (Polynomial ℚ)) (CommRingCat.of OriginalLaurentProjectiveOverlap318.Ring)
    (CommRingCat.of (ContactWholeInfinityAlgebra318.Ring c))
    (infinityLine c L) (projection c) (infinityEdge c)
    (ContactOverlapTensorCharts318.infinityIso c).symm
    (ContactOverlapTensorCharts318.infinityIso_inv_base c)
    (ContactOverlapTensorCharts318.infinityIso_inv_chart c)
    (ContactOriginalLineOverlap318.line c L).object
    (ContactOriginalLineOverlap318.infinityComparison c L)).hom
      ((TildePullback318.globalNatIso
        (AffineModuleBaseChange318.rightMap (CommRingCat.of (Polynomial ℚ))
          (CommRingCat.of OriginalLaurentProjectiveOverlap318.Ring)
          (CommRingCat.of (ContactWholeInfinityAlgebra318.Ring c)))).hom.app _
        (moduleSpecΓFunctor.map
          ((Scheme.Modules.pullbackPushforwardAdjunction
            (Spec.map (AffineModuleBaseChange318.rightMap (CommRingCat.of (Polynomial ℚ))
              (CommRingCat.of OriginalLaurentProjectiveOverlap318.Ring)
              (CommRingCat.of (ContactWholeInfinityAlgebra318.Ring c))))).unit.app
            (infinityLine c L).object) m))

lemma finiteRestriction_unit (m : finiteSections c L) :
    (ContactCommonLaurentModule318.finiteIso c L).hom
      ((ModuleCat.extendRestrictScalarsAdj OriginalLaurentProjectiveOverlap318.finiteHom).unit.app
        (finiteSections c L) m) = finiteRestriction c L m :=
  OriginalTensorChartRestriction318.overlap_unit
    (CommRingCat.of (Polynomial ℚ)) (CommRingCat.of OriginalLaurentProjectiveOverlap318.Ring)
    (CommRingCat.of (ContactKummerOrder318.SourceOrder c))
    (finiteLine c L) (projection c) (finiteEdge c)
    (ContactOverlapTensorCharts318.finiteIso c).symm
    (ContactOverlapTensorCharts318.finiteIso_inv_base c)
    (ContactOverlapTensorCharts318.finiteIso_inv_chart c)
    (ContactOriginalLineOverlap318.line c L).object
    (ContactOriginalLineOverlap318.finiteComparison c L) m

lemma infinityRestriction_unit (m : infinitySections c L) :
    (ContactCommonLaurentModule318.infinityIso c L).hom
      ((ModuleCat.extendRestrictScalarsAdj OriginalLaurentProjectiveOverlap318.infinityHom).unit.app
        (infinitySections c L) m) = infinityRestriction c L m := by
  letI := OriginalLaurentProjectiveOverlap318.infinityHom.toAlgebra
  exact OriginalTensorChartRestriction318.overlap_unit
    (CommRingCat.of (Polynomial ℚ)) (CommRingCat.of OriginalLaurentProjectiveOverlap318.Ring)
    (CommRingCat.of (ContactWholeInfinityAlgebra318.Ring c))
    (infinityLine c L) (projection c) (infinityEdge c)
    (ContactOverlapTensorCharts318.infinityIso c).symm
    (ContactOverlapTensorCharts318.infinityIso_inv_base c)
    (ContactOverlapTensorCharts318.infinityIso_inv_chart c)
    (ContactOriginalLineOverlap318.line c L).object
    (ContactOriginalLineOverlap318.infinityComparison c L) m

/-- The actual finite restriction has the original polynomial localization
as its coordinate formula, with the SAME old basis coefficients. -/
lemma finite_formula (m : finiteSections c L) :
    coordinates c L (finiteRestriction c L m) =
      LaurentOriginalPolynomialCharts318.finiteMap
        ((Module.finBasis (Polynomial ℚ) (finiteSections c L)).equivFun m) := by
  rw [← finiteRestriction_unit]
  simp only [coordinates, LinearEquiv.trans_apply, inverse_hom_apply]
  funext i
  exact OriginalFiniteBasisBaseChange318.coordinates_unit
    OriginalLaurentProjectiveOverlap318.finiteHom (finiteSections c L) m i

/-- The actual infinity restriction has the original reciprocal polynomial
localization followed by the derived original overlap transition. -/
lemma infinity_formula (m : infinitySections c L) :
    coordinates c L (infinityRestriction c L m) =
      ContactOriginalLaurentCoordinates318.rawTransition c L
        (LaurentOriginalPolynomialCharts318.infinityMap
          ((Module.finBasis (Polynomial ℚ) (infinitySections c L)).equivFun m)) := by
  rw [← infinityRestriction_unit]
  have hi : ContactOriginalLaurentCoordinates318.infinityCoordinates c L
      ((ModuleCat.extendRestrictScalarsAdj OriginalLaurentProjectiveOverlap318.infinityHom).unit.app
        (infinitySections c L) m) =
      LaurentOriginalPolynomialCharts318.infinityMap
        ((Module.finBasis (Polynomial ℚ) (infinitySections c L)).equivFun m) := by
    funext i
    exact OriginalFiniteBasisBaseChange318.coordinates_unit
      OriginalLaurentProjectiveOverlap318.infinityHom (infinitySections c L) m i
  rw [← hi]
  simp only [coordinates, ContactOriginalLaurentCoordinates318.rawTransition,
    LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    ContactCommonLaurentModule318.transition]
  have h := inverse_hom_trans_apply
    (R := OriginalLaurentProjectiveOverlap318.Ring)
    (M := (ModuleCat.extendScalars OriginalLaurentProjectiveOverlap318.finiteHom).obj
      (finiteSections c L))
    (N := (ModuleCat.extendScalars OriginalLaurentProjectiveOverlap318.infinityHom).obj
      (infinitySections c L))
    (P := ContactCommonLaurentModule318.common c L)
    (ContactCommonLaurentModule318.finiteIso c L)
    (ContactCommonLaurentModule318.infinityIso c L)
    ((ModuleCat.extendRestrictScalarsAdj OriginalLaurentProjectiveOverlap318.infinityHom).unit.app
      (infinitySections c L) m)
  exact congrArg (ContactOriginalLaurentCoordinates318.finiteCoordinates c L) h


/-- Every positive Laurent vector is the coordinate image of an actual
finite-chart section, and no additional vector occurs. -/
lemma finite_image : Set.range (fun m => coordinates c L (finiteRestriction c L m)) =
    (LaurentVectorFiltration318.positive (k:=ℚ)
      (n:=ContactOriginalLaurentCoordinates318.finiteRank c L) : Set
      (LaurentVectorFiltration318.V ℚ (ContactOriginalLaurentCoordinates318.finiteRank c L))) := by
  ext v
  constructor
  · rintro ⟨m,rfl⟩
    dsimp only
    rw [finite_formula]
    rw [← LaurentOriginalPolynomialCharts318.finiteMap_range]
    exact ⟨_,rfl⟩
  · intro hv
    rw [← LaurentOriginalPolynomialCharts318.finiteMap_range] at hv
    obtain ⟨p,hp⟩ := hv
    refine ⟨(Module.finBasis (Polynomial ℚ) (finiteSections c L)).equivFun.symm p,?_⟩
    dsimp only
    rw [finite_formula, LinearEquiv.apply_symm_apply]
    exact hp
/-- The other original chart image is exactly the image of the negative
filtration under the actual Laurent transition, without replacing that
transition by one chosen from rank alone. -/
lemma infinity_image : Set.range (fun m => coordinates c L (infinityRestriction c L m)) =
    ((LaurentVectorFiltration318.negative).map
      ((ContactOriginalLaurentCoordinates318.rawTransition c L).toLinearMap.restrictScalars ℚ) :
        Set (LaurentVectorFiltration318.V ℚ
          (ContactOriginalLaurentCoordinates318.finiteRank c L))) := by
  ext v
  constructor
  · rintro ⟨m,rfl⟩
    dsimp only
    rw [infinity_formula]
    refine ⟨LaurentOriginalPolynomialCharts318.infinityMap
      ((Module.finBasis (Polynomial ℚ) (infinitySections c L)).equivFun m),?_,rfl⟩
    rw [← LaurentOriginalPolynomialCharts318.infinityMap_range]
    exact ⟨_,rfl⟩
  · rintro ⟨w,hw,hv⟩
    rw [← LaurentOriginalPolynomialCharts318.infinityMap_range] at hw
    obtain ⟨p,hp⟩ := hw
    refine ⟨(Module.finBasis (Polynomial ℚ) (infinitySections c L)).equivFun.symm p,?_⟩
    dsimp only
    rw [infinity_formula,LinearEquiv.apply_symm_apply,hp]
    exact hv
end ContactOriginalRestrictionCoordinates318
