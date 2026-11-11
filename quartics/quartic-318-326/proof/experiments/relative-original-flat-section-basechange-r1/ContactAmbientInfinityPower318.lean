module
public import ContactAmbientCoefficientComposition318
public import ContactCoefficientCoordinatePowers318
public section
noncomputable section
namespace ContactAmbientInfinityPower318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalCoefficientActions318 ContactCoefficientNativeSections318
open ContactRelativeWholeOpenSections318 ContactRelativeCoefficientChange318
open OriginalSectionTransport318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
local instance (N : Line (curve R c)) : Module R (infinitySections R c N) := infinityModule R c N
local instance (N : Line (curve R c)) (U : (curve R c).Opens) : Module R Γ(N.object,U) :=
  OriginalCoefficientCohomology318.sectionModule R (ContactRelativeStructuralHOne318.projection R c) N U

/-- The original infinity coordinate power on the entire actual ambient open. -/
@[expose] def power (N : Line (curve R c)) (b : ℕ) :
    Γ(N.object,infinityOpen R c) →ₗ[R] Γ(N.object,infinityOpen R c) :=
  (ContactRelativeCoefficientWholeSections318.infinityEquivalence R c N).toLinearMap.comp
    ((ContactRelativeInfinityJet318.power R c N b).comp
      (ContactRelativeCoefficientWholeSections318.infinityEquivalence R c N).symm.toLinearMap)

lemma injective (N : Line (curve R c)) (b : ℕ) : Function.Injective (power R c N b) :=
  (ContactRelativeCoefficientWholeSections318.infinityEquivalence R c N).injective.comp
    ((ContactRelativeInfinityJet318.injective R c N b).comp
      (ContactRelativeCoefficientWholeSections318.infinityEquivalence R c N).symm.injective)

@[expose] def chartMap {L N : Line (curve R c)} (a : L.object ⟶ N.object) :=
  moduleSpecΓFunctor.map ((Scheme.Modules.pullback (infinityInto R c)).map a)

lemma chart_natural {L N : Line (curve R c)} (a : L.object ⟶ N.object)
    (x : infinitySections R c L) :
    infinityEquiv R c N (chartMap R c a x)=a.app (infinityOpen R c) (infinityEquiv R c L x) := by
  have hn := congrArg (fun q => q.app ⊤ x)
    ((Scheme.Modules.restrictFunctorIsoPullback (infinityInto R c)).inv.naturality a)
  exact hn

lemma natural {L N : Line (curve R c)} (a : L.object ⟶ N.object) (b : ℕ)
    (s : Γ(L.object,infinityOpen R c)) :
    a.app (infinityOpen R c) (power R c L b s)=
      power R c N b (a.app (infinityOpen R c) s) := by
  obtain ⟨x,rfl⟩ := (ContactRelativeCoefficientWholeSections318.infinityEquivalence R c L).surjective s
  have hm : chartMap R c a (ContactRelativeInfinityJet318.power R c L b x)=
      ContactRelativeInfinityJet318.power R c N b (chartMap R c a x) := by
    change (chartMap R c a).hom
      (RelativeOriginalPolynomialAlgebra318.polynomialMap ℚ R (infinityRing c)
        (Polynomial.X ^ (b+1)) • x) =
      RelativeOriginalPolynomialAlgebra318.polynomialMap ℚ R (infinityRing c)
        (Polynomial.X ^ (b+1)) • (chartMap R c a).hom x
    exact (chartMap R c a).hom.map_smul _ _
  change a.app (infinityOpen R c)
    (infinityEquiv R c L (ContactRelativeInfinityJet318.power R c L b
      ((infinityEquiv R c L).symm (infinityEquiv R c L x)))) = _
  rw [AddEquiv.symm_apply_apply,← chart_natural,hm]
  rw [← chart_natural R c a x]
  change _=infinityEquiv R c N (ContactRelativeInfinityJet318.power R c N b
    ((infinityEquiv R c N).symm (infinityEquiv R c N (chartMap R c a x))))
  rw [AddEquiv.symm_apply_apply]

variable (S : CommRingCat.{0}) [Algebra ℚ S] (f : R →ₐ[ℚ] S) (L : Line (curve R c))

lemma coefficient (b : ℕ) (s : Γ(L.object,infinityOpen R c)) :
    pullTo (curveMap R S f c) L.object (infinityOpen R c) (infinityOpen S c)
      (ContactCoefficientWholeOpens318.infinity_preimage R S f c) (power R c L b s)=
    power S c (L' R S f c L) b
      (pullTo (curveMap R S f c) L.object (infinityOpen R c) (infinityOpen S c)
        (ContactCoefficientWholeOpens318.infinity_preimage R S f c) s) := by
  obtain ⟨x,rfl⟩ := (infinityEquiv R c L).surjective s
  change pullTo _ _ _ _ _ (infinityEquiv R c L (ContactRelativeInfinityJet318.power R c L b
    ((infinityEquiv R c L).symm (infinityEquiv R c L x))))=_
  rw [AddEquiv.symm_apply_apply,← ContactCoefficientAmbientCharts318.infinity_square,
    ← ContactCoefficientAmbientCharts318.infinity_square]
  change infinityEquiv S c _ (ContactCoefficientLineCharts318.infinityRestriction R S f c L
    ((Polynomial.X ^ (b+1) : Polynomial R) • x))=_
  rw [ContactCoefficientCoordinatePowers318.infinity_restriction_power]
  change _=infinityEquiv S c _ (ContactRelativeInfinityJet318.power S c _ b
    ((infinityEquiv S c _).symm (infinityEquiv S c _ _)))
  rw [AddEquiv.symm_apply_apply]

variable (T : CommRingCat.{0}) [Algebra ℚ T] (g : S →ₐ[ℚ] T)
lemma composition (b : ℕ) (s : Γ((L' R S f c L).object,infinityOpen S c)) :
    ContactAmbientCoefficientComposition318.infinity R S T f g c L
      (power S c (L' R S f c L) b s) =
    power T c (L' R T (g.comp f) c L) b
      (ContactAmbientCoefficientComposition318.infinity R S T f g c L s) := by
  change (ContactDerivedCoefficientFunctor318.compositionIso R S T f g c L).hom.app _
    (pullTo _ _ _ _ _ (power S c (L' R S f c L) b s))=_
  rw [coefficient,natural]
end ContactAmbientInfinityPower318
