module
public import ContactRelativeCoefficientWholeSections318
public import OriginalModuleTwoOpenGluing318
public section
noncomputable section
namespace ContactRelativeOriginalHZero318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalCoefficientActions318 ContactRelativeWholeOpenSections318
open ContactRelativeCoefficientWholeSections318 OriginalCoefficientCohomology318
set_option maxHeartbeats 850000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : Module R (finiteSections R c L) := finiteModule R c L
local instance : Module R (infinitySections R c L) := infinityModule R c L
local instance : Module R (originalSections R c L) := overlapModule R c L
local instance (U : (curve R c).Opens) : Module R Γ(L.object,U) :=
  sectionModule R (ContactRelativeStructuralHOne318.projection R c) L U

@[expose] def restriction (U : (curve R c).Opens) : Γ(L.object,⊤) →ₗ[R] Γ(L.object,U) where
  toFun := L.object.presheaf.map (homOfLE le_top).op
  map_add' := map_add _
  map_smul' r x := by
    change L.object.presheaf.map (homOfLE le_top).op
      (scalar R (ContactRelativeStructuralHOne318.projection R c) ⊤ r • x) = _
    rw [Scheme.Modules.map_smul,scalar_restrict]
    rfl

@[expose] def pair : Γ(L.object,⊤) →ₗ[R] (finiteSections R c L × infinitySections R c L) :=
  ((finiteEquivalence R c L).symm.toLinearMap.comp (restriction R c L (finiteOpen R c))).prod
    ((infinityEquivalence R c L).symm.toLinearMap.comp (restriction R c L (infinityOpen R c)))

lemma compatible (s : Γ(L.object,⊤)) : ContactRelativeCechProjective318.difference R c L (pair R c L s) = 0 := by
  apply (ContactRelativeWholeOpenSections318.overlapEquiv R c L).injective
  change ContactRelativeWholeOpenSections318.overlapEquiv R c L
    (finiteRestriction R c L ((ContactRelativeWholeOpenSections318.finiteEquiv R c L).symm
        (restriction R c L (finiteOpen R c) s)) -
      infinityRestriction R c L ((ContactRelativeWholeOpenSections318.infinityEquiv R c L).symm
        (restriction R c L (infinityOpen R c) s))) = _
  rw [map_sub,ContactRelativeWholeOpenSections318.finite_square,
    ContactRelativeWholeOpenSections318.infinity_square,AddEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply,map_zero]
  change L.object.presheaf.map _ (L.object.presheaf.map _ s) -
    L.object.presheaf.map _ (L.object.presheaf.map _ s) = 0
  rw [← Functor.map_comp_apply,← Functor.map_comp_apply]
  exact sub_self _

/-- Actual original global sections with their structural R action map
to the genuine coefficient Cech kernel, not an invented H0 module. -/
@[expose] def toKernel : Γ(L.object,⊤) →ₗ[R]
    LinearMap.ker (ContactRelativeCechProjective318.difference R c L) :=
  (pair R c L).codRestrict _ (compatible R c L)

lemma injective : Function.Injective (toKernel R c L) := by
  intro s t h
  let W : Fin 2 → (curve R c).Opens := ![finiteOpen R c,infinityOpen R c]
  have hc : ⊤ ≤ iSup W := by
    exact (le_of_eq (cover R c).symm).trans (sup_le (le_iSup W 0) (le_iSup W 1))
  apply TopCat.Sheaf.eq_of_locally_eq'
    (⟨L.object.presheaf,L.object.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat (curve R c))
    W ⊤ (fun _ => homOfLE le_top) hc s t
  intro i
  fin_cases i
  · have h0 := congrArg (fun z : LinearMap.ker (ContactRelativeCechProjective318.difference R c L) =>
        finiteEquivalence R c L z.val.1) h
    simpa only [toKernel,pair,LinearMap.codRestrict_apply,LinearMap.prod_apply,
      LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,restriction] using h0
  · have h1 := congrArg (fun z : LinearMap.ker (ContactRelativeCechProjective318.difference R c L) =>
        infinityEquivalence R c L z.val.2) h
    simpa only [toKernel,pair,LinearMap.codRestrict_apply,LinearMap.prod_apply,
      LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,restriction] using h1

lemma surjective : Function.Surjective (toKernel R c L) := by
  intro z
  have hz : finiteRestriction R c L z.val.1 = infinityRestriction R c L z.val.2 :=
    sub_eq_zero.mp z.property
  have h := congrArg (ContactRelativeWholeOpenSections318.overlapEquiv R c L) hz
  rw [ContactRelativeWholeOpenSections318.finite_square,
    ContactRelativeWholeOpenSections318.infinity_square] at h
  obtain ⟨s,hs0,hs1⟩ := OriginalModuleTwoOpenGluing318.exists_gluing L.object
    (finiteOpen R c) (infinityOpen R c) (cover R c)
    (ContactRelativeWholeOpenSections318.finiteEquiv R c L z.val.1)
    (ContactRelativeWholeOpenSections318.infinityEquiv R c L z.val.2) h
  refine ⟨s,?_⟩
  apply Subtype.ext
  apply Prod.ext
  · change (ContactRelativeWholeOpenSections318.finiteEquiv R c L).symm
      (L.object.presheaf.map (homOfLE le_top).op s) = z.val.1
    rw [hs0,AddEquiv.symm_apply_apply]
  · change (ContactRelativeWholeOpenSections318.infinityEquiv R c L).symm
      (L.object.presheaf.map (homOfLE le_top).op s) = z.val.2
    rw [hs1,AddEquiv.symm_apply_apply]

@[expose] def equivalence : Γ(L.object,⊤) ≃ₗ[R]
    LinearMap.ker (ContactRelativeCechProjective318.difference R c L) :=
  LinearEquiv.ofBijective (toKernel R c L) ⟨injective R c L,surjective R c L⟩

lemma pair_symm (z : LinearMap.ker (ContactRelativeCechProjective318.difference R c L)) :
    pair R c L ((equivalence R c L).symm z) = z.val :=
  congrArg Subtype.val ((equivalence R c L).apply_symm_apply z)

/-- On actual H1 vanishing, genuine original global sections are
projective over R. This does NOT yet claim finite generation or a finite
projective cohomology complex. -/
theorem projective_of_h1_zero (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L, x=0) :
    Module.Projective R Γ(L.object,⊤) := by
  letI := (ContactRelativeCechProjective318.split_kernel R c L hz).2
  exact Module.Projective.of_equiv (equivalence R c L).symm
end ContactRelativeOriginalHZero318
