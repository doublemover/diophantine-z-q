module
public import ContactCoefficientAmbientCharts318
public import ContactHZeroCoefficientFunctor318
public section
noncomputable section
namespace ContactAmbientCoefficientComposition318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactCoefficientNativeSections318
open ContactRelativeWholeOpenSections318 ContactRelativeCoefficientChange318
open OriginalSectionTransport318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R S T : CommRingCat.{0}) [Algebra ℚ R] [Algebra ℚ S] [Algebra ℚ T]
  (f : R →ₐ[ℚ] S) (g : S →ₐ[ℚ] T) (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance (N : Line (curve S c)) (U : (curve S c).Opens) : Module S Γ(N.object,U) :=
  OriginalCoefficientCohomology318.sectionModule S (ContactRelativeStructuralHOne318.projection S c) N U
local instance (N : Line (curve T c)) (U : (curve T c).Opens) : Module T Γ(N.object,U) :=
  OriginalCoefficientCohomology318.sectionModule T (ContactRelativeStructuralHOne318.projection T c) N U

/-- The genuine geometric unit on the whole finite open, with the original
coefficient-composition sheaf isomorphism. -/
@[expose] def finite : Γ((L' R S f c L).object,finiteOpen S c) →+
    Γ((L' R T (g.comp f) c L).object,finiteOpen T c) :=
  ((ContactDerivedCoefficientFunctor318.compositionIso R S T f g c L).hom.app (finiteOpen T c)).hom.comp
    (pullTo (curveMap S T g c) (L' R S f c L).object (finiteOpen S c) (finiteOpen T c)
      (ContactCoefficientWholeOpens318.finite_preimage S T g c))

lemma finite_composition (s : Γ(L.object,finiteOpen R c)) :
    finite R S T f g c L (pullTo (curveMap R S f c) L.object (finiteOpen R c) (finiteOpen S c)
      (ContactCoefficientWholeOpens318.finite_preimage R S f c) s) =
    pullTo (curveMap R T (g.comp f) c) L.object (finiteOpen R c) (finiteOpen T c)
      (ContactCoefficientWholeOpens318.finite_preimage R T (g.comp f) c) s := by
  have hp : (curveMap S T g c ≫ curveMap R S f c) ⁻¹ᵁ finiteOpen R c=finiteOpen T c := by
    rw [ContactCoefficientWholeOpens318.composition]
    exact ContactCoefficientWholeOpens318.finite_preimage R T (g.comp f) c
  change ((Scheme.Modules.pullbackCongr
    (ContactCoefficientWholeOpens318.composition R S f c T g)).hom.app L.object).app (finiteOpen T c)
      (((Scheme.Modules.pullbackComp (curveMap S T g c) (curveMap R S f c)).hom.app L.object).app
        (finiteOpen T c) _) = _
  rw [OriginalSectionTransport318.composition _ _ _ _ _ _ _ _ hp]
  exact OriginalSectionTransport318.congr
    (ContactCoefficientWholeOpens318.composition R S f c T g) L.object _ _ hp _ s

lemma finite_smul (s : S) (x : Γ((L' R S f c L).object,finiteOpen S c)) :
    finite R S T f g c L (s • x)=g s • finite R S T f g c L x := by
  change (ContactDerivedCoefficientFunctor318.compositionIso R S T f g c L).hom.app
    (finiteOpen T c) (pullTo _ _ _ _ _ (s • x))=_
  rw [ContactCoefficientAmbientCharts318.finite_smul]
  exact Scheme.Modules.Hom.app_smul _ _ _

lemma finite_restriction (s : Γ((L' R S f c L).object,⊤)) :
    finite R S T f g c L ((L' R S f c L).object.presheaf.map
      (homOfLE (show finiteOpen S c≤⊤ from le_top)).op s) =
    (L' R T (g.comp f) c L).object.presheaf.map
      (homOfLE (show finiteOpen T c≤⊤ from le_top)).op
      (ContactHZeroCoefficientFunctor318.compositionSections R S f c L T g
        (OriginalSectionPullbackComposition318.pull (curveMap S T g c) (L' R S f c L).object s)) := by
  change (ContactDerivedCoefficientFunctor318.compositionIso R S T f g c L).hom.app (finiteOpen T c)
    (pullTo _ _ _ _ _ (_ s))=_
  rw [← OriginalOpenSectionNaturality318.restrict_top]
  exact congrArg (fun q => q (OriginalSectionPullbackComposition318.pull
    (curveMap S T g c) (L' R S f c L).object s))
    ((ContactDerivedCoefficientFunctor318.compositionIso R S T f g c L).hom.mapPresheaf.naturality
      (homOfLE (show finiteOpen T c≤⊤ from le_top)).op)

/-- The genuine geometric unit on the whole infinity open, with the original
coefficient-composition sheaf isomorphism. -/
@[expose] def infinity : Γ((L' R S f c L).object,infinityOpen S c) →+
    Γ((L' R T (g.comp f) c L).object,infinityOpen T c) :=
  ((ContactDerivedCoefficientFunctor318.compositionIso R S T f g c L).hom.app (infinityOpen T c)).hom.comp
    (pullTo (curveMap S T g c) (L' R S f c L).object (infinityOpen S c) (infinityOpen T c)
      (ContactCoefficientWholeOpens318.infinity_preimage S T g c))

lemma infinity_composition (s : Γ(L.object,infinityOpen R c)) :
    infinity R S T f g c L (pullTo (curveMap R S f c) L.object (infinityOpen R c) (infinityOpen S c)
      (ContactCoefficientWholeOpens318.infinity_preimage R S f c) s) =
    pullTo (curveMap R T (g.comp f) c) L.object (infinityOpen R c) (infinityOpen T c)
      (ContactCoefficientWholeOpens318.infinity_preimage R T (g.comp f) c) s := by
  have hp : (curveMap S T g c ≫ curveMap R S f c) ⁻¹ᵁ infinityOpen R c=infinityOpen T c := by
    rw [ContactCoefficientWholeOpens318.composition]
    exact ContactCoefficientWholeOpens318.infinity_preimage R T (g.comp f) c
  change ((Scheme.Modules.pullbackCongr
    (ContactCoefficientWholeOpens318.composition R S f c T g)).hom.app L.object).app (infinityOpen T c)
      (((Scheme.Modules.pullbackComp (curveMap S T g c) (curveMap R S f c)).hom.app L.object).app
        (infinityOpen T c) _) = _
  rw [OriginalSectionTransport318.composition _ _ _ _ _ _ _ _ hp]
  exact OriginalSectionTransport318.congr
    (ContactCoefficientWholeOpens318.composition R S f c T g) L.object _ _ hp _ s

lemma infinity_smul (s : S) (x : Γ((L' R S f c L).object,infinityOpen S c)) :
    infinity R S T f g c L (s • x)=g s • infinity R S T f g c L x := by
  change (ContactDerivedCoefficientFunctor318.compositionIso R S T f g c L).hom.app
    (infinityOpen T c) (pullTo _ _ _ _ _ (s • x))=_
  rw [ContactCoefficientAmbientCharts318.infinity_smul]
  exact Scheme.Modules.Hom.app_smul _ _ _

lemma infinity_restriction (s : Γ((L' R S f c L).object,⊤)) :
    infinity R S T f g c L ((L' R S f c L).object.presheaf.map
      (homOfLE (show infinityOpen S c≤⊤ from le_top)).op s) =
    (L' R T (g.comp f) c L).object.presheaf.map
      (homOfLE (show infinityOpen T c≤⊤ from le_top)).op
      (ContactHZeroCoefficientFunctor318.compositionSections R S f c L T g
        (OriginalSectionPullbackComposition318.pull (curveMap S T g c) (L' R S f c L).object s)) := by
  change (ContactDerivedCoefficientFunctor318.compositionIso R S T f g c L).hom.app (infinityOpen T c)
    (pullTo _ _ _ _ _ (_ s))=_
  rw [← OriginalOpenSectionNaturality318.restrict_top]
  exact congrArg (fun q => q (OriginalSectionPullbackComposition318.pull
    (curveMap S T g c) (L' R S f c L).object s))
    ((ContactDerivedCoefficientFunctor318.compositionIso R S T f g c L).hom.mapPresheaf.naturality
      (homOfLE (show infinityOpen T c≤⊤ from le_top)).op)
end ContactAmbientCoefficientComposition318
