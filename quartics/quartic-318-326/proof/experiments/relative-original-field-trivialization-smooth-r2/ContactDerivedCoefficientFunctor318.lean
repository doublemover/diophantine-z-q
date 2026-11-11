module
public import ContactOriginalDerivedCoefficientMap318
public section
noncomputable section
namespace ContactDerivedCoefficientFunctor318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open NonreducedLineRestriction318 ContactRelativeCoefficientChange318
open ContactOriginalRelativePolynomialCharts318 ContactRelativeWholeOpenSections318
open ContactOriginalDerivedCoefficientMap318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R S T : CommRingCat.{0}) [Algebra ℚ R] [Algebra ℚ S] [Algebra ℚ T]
  (f : R →ₐ[ℚ] S) (g : S →ₐ[ℚ] T) (c : Fin 4 → ℚˣ) (L : Line (curve R c))

/-- The literal composition isomorphism of the original module pullbacks,
including equality of the actual p-first coefficient maps. -/
@[expose] def compositionIso :
    (pulled S T g c (pulled R S f c L)).object ≅ (pulled R T (g.comp f) c L).object :=
  (Scheme.Modules.pullbackComp (curveMap S T g c) (curveMap R S f c)).app L.object ≪≫
    (Scheme.Modules.pullbackCongr (ContactCoefficientWholeOpens318.composition R S f c T g)).app L.object

lemma composition (x : NonreducedLineMayerVietoris318.H1 L) :
    Sheaf.H.map ((SheafOfModules.toSheaf (curve T c).ringCatSheaf).map
      (compositionIso R S T f g c L).hom) 1
      (map S T g c (pulled R S f c L) 1 (map R S f c L 1 x)) = map R T (g.comp f) c L 1 x := by
  simp only [compositionIso,Iso.trans_hom,Functor.map_comp,Sheaf.H.map_comp_apply]
  rw [OriginalLineDerivedFunctoriality318.composition
    (curveMap S T g c) (curveMap R S f c) L (finiteOpen R c) (infinityOpen R c)
    (finite_affine R c) (infinity_affine R c) (cover R c)]
  exact OriginalLineDerivedFunctoriality318.congr
    (ContactCoefficientWholeOpens318.composition R S f c T g) L 1 x

@[expose] def identityIso : (pulled R R (AlgHom.id ℚ R) c L).object ≅ L.object :=
  (Scheme.Modules.pullbackCongr (ContactCoefficientWholeOpens318.identity R c)).app L.object ≪≫
    (Scheme.Modules.pullbackId (curve R c)).app L.object

lemma identity (x : NonreducedLineMayerVietoris318.H1 L) :
    Sheaf.H.map ((SheafOfModules.toSheaf (curve R c).ringCatSheaf).map
      (identityIso R c L).hom) 1 (map R R (AlgHom.id ℚ R) c L 1 x) = x := by
  simp only [identityIso,Iso.trans_hom,Functor.map_comp,Sheaf.H.map_comp_apply]
  rw [OriginalLineDerivedFunctoriality318.congr]
  exact OriginalLineDerivedFunctoriality318.identity L (finiteOpen R c) (infinityOpen R c)
    (finite_affine R c) (infinity_affine R c) (cover R c) x
end ContactDerivedCoefficientFunctor318
