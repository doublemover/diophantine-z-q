module
public import ContactOriginalModuleOverlap318
public import AffineTensorLinePushforward318

public section
noncomputable section
namespace ContactCommonLaurentModule318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalLaurentOverlap318 ContactOriginalLineBothCharts318
variable (c : Fin 4 → ℚˣ) (L : Line (ContactProjectiveModel318.model c))

/-- One actual Laurent module for the SAME original line on the WHOLE
original overlap, with its original projection to Spec ℚ[T,T⁻¹]. -/
abbrev common : ModuleCat OriginalLaurentProjectiveOverlap318.Ring :=
  moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward (projection c)).obj
    (ContactOriginalLineOverlap318.line c L).object)

/-- Scalar extension of the old finite polynomial sections recovers the
actual common Laurent module, with its original scalar action. -/
@[expose] def finiteIso : (ModuleCat.extendScalars OriginalLaurentProjectiveOverlap318.finiteHom).obj
    (finiteSections c L) ≅ common c L :=
  AffineTensorLinePushforward318.sectionsIso
    (CommRingCat.of (Polynomial ℚ)) (CommRingCat.of OriginalLaurentProjectiveOverlap318.Ring)
    (CommRingCat.of (ContactKummerOrder318.SourceOrder c))
    (projection c) (finiteEdge c) (ContactOverlapTensorCharts318.finiteIso c).symm
    (ContactOverlapTensorCharts318.finiteIso_inv_base c)
    (ContactOverlapTensorCharts318.finiteIso_inv_chart c)
    (finiteLine c L) (ContactOriginalLineOverlap318.line c L).object
    (ContactOriginalLineOverlap318.finiteComparison c L)

/-- The reciprocal scalar extension uses u↦T⁻¹ and recovers the SAME actual
common Laurent module. There is no identification by rank alone. -/
@[expose] def infinityIso : (ModuleCat.extendScalars OriginalLaurentProjectiveOverlap318.infinityHom).obj
    (infinitySections c L) ≅ common c L := by
  letI := OriginalLaurentProjectiveOverlap318.infinityHom.toAlgebra
  exact AffineTensorLinePushforward318.sectionsIso
    (CommRingCat.of (Polynomial ℚ)) (CommRingCat.of OriginalLaurentProjectiveOverlap318.Ring)
    (CommRingCat.of (ContactWholeInfinityAlgebra318.Ring c))
    (projection c) (infinityEdge c) (ContactOverlapTensorCharts318.infinityIso c).symm
    (ContactOverlapTensorCharts318.infinityIso_inv_base c)
    (ContactOverlapTensorCharts318.infinityIso_inv_chart c)
    (infinityLine c L) (ContactOriginalLineOverlap318.line c L).object
    (ContactOriginalLineOverlap318.infinityComparison c L)

/-- Exact Laurent-linear overlap between the scalar extensions of BOTH
original polynomial section modules. -/
@[expose] def transition : (ModuleCat.extendScalars OriginalLaurentProjectiveOverlap318.infinityHom).obj
    (infinitySections c L) ≅
    (ModuleCat.extendScalars OriginalLaurentProjectiveOverlap318.finiteHom).obj (finiteSections c L) :=
  infinityIso c L ≪≫ (finiteIso c L).symm

@[reassoc] lemma transition_recovery : (transition c L).hom ≫ (finiteIso c L).hom =
    (infinityIso c L).hom := by
  simp only [transition,Iso.trans_hom,Iso.symm_hom,Category.assoc,Iso.inv_hom_id,Category.comp_id]
end ContactCommonLaurentModule318
