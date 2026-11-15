module
public import ContactAmbientCoefficientComposition318
public import ProjectiveSectionParameter318
public section
noncomputable section
namespace ContactAmbientTensorNaturality318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalCoefficientActions318 ContactCoefficientNativeSections318
open ContactRelativeWholeOpenSections318 ContactRelativeCoefficientChange318
open OriginalSectionTransport318
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R S : CommRingCat.{0}) [Algebra ℚ R] [Algebra ℚ S]
  (f : R →ₐ[ℚ] S) (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : Algebra R S := f.toAlgebra
local instance (N : Line (curve S c)) (U : (curve S c).Opens) : Module S Γ(N.object,U) :=
  OriginalCoefficientCohomology318.sectionModule S (ContactRelativeStructuralHOne318.projection S c) N U
local instance : Module R (finiteSections R c L) := finiteModule R c L
local instance : Module S (finiteSections S c (L' R S f c L)) := finiteModule S c _

@[expose] def finite : S ⊗[R] finiteSections R c L →ₗ[S]
    Γ((L' R S f c L).object,finiteOpen S c) :=
  (ContactRelativeCoefficientWholeSections318.finiteEquivalence S c (L' R S f c L)).toLinearMap.comp
    (finiteEquivalence R S f c L).toLinearMap

lemma finite_pure (s : S) (x : finiteSections R c L) :
    finite R S f c L (s ⊗ₜ[R] x)=s •
      pullTo (curveMap R S f c) L.object (finiteOpen R c) (finiteOpen S c)
        (ContactCoefficientWholeOpens318.finite_preimage R S f c) (finiteEquiv R c L x) := by
  change ContactRelativeCoefficientWholeSections318.finiteEquivalence S c (L' R S f c L)
    (finiteEquivalence R S f c L (s ⊗ₜ[R] x))=_
  rw [ContactCoefficientNativeSections318.finite_pure,LinearEquiv.map_smul]
  exact congrArg (fun z => s • z) (ContactCoefficientAmbientCharts318.finite_square R S f c L x)
local instance : Module R (infinitySections R c L) := infinityModule R c L
local instance : Module S (infinitySections S c (L' R S f c L)) := infinityModule S c _

@[expose] def infinity : S ⊗[R] infinitySections R c L →ₗ[S]
    Γ((L' R S f c L).object,infinityOpen S c) :=
  (ContactRelativeCoefficientWholeSections318.infinityEquivalence S c (L' R S f c L)).toLinearMap.comp
    (infinityEquivalence R S f c L).toLinearMap

lemma infinity_pure (s : S) (x : infinitySections R c L) :
    infinity R S f c L (s ⊗ₜ[R] x)=s •
      pullTo (curveMap R S f c) L.object (infinityOpen R c) (infinityOpen S c)
        (ContactCoefficientWholeOpens318.infinity_preimage R S f c) (infinityEquiv R c L x) := by
  change ContactRelativeCoefficientWholeSections318.infinityEquivalence S c (L' R S f c L)
    (infinityEquivalence R S f c L (s ⊗ₜ[R] x))=_
  rw [ContactCoefficientNativeSections318.infinity_pure,LinearEquiv.map_smul]
  exact congrArg (fun z => s • z) (ContactCoefficientAmbientCharts318.infinity_square R S f c L x)

variable (T : CommRingCat.{0}) [Algebra ℚ T] (g : S →ₐ[ℚ] T)
local instance : Algebra R T := (g.comp f).toAlgebra
local instance (N : Line (curve T c)) (U : (curve T c).Opens) : Module T Γ(N.object,U) :=
  OriginalCoefficientCohomology318.sectionModule T (ContactRelativeStructuralHOne318.projection T c) N U

lemma finite_natural (z : S ⊗[R] finiteSections R c L) :
    ContactAmbientCoefficientComposition318.finite R S T f g c L (finite R S f c L z)=
      finite R T (g.comp f) c L
        (ProjectiveSectionParameter318.transport R (finiteSections R c L) S
          (ContactHZeroCoefficientFunctor318.coefficientArrow R S f T g) z) := by
  induction z using TensorProduct.inductionOn with
  | tmul s x =>
      rw [finite_pure,ContactAmbientCoefficientComposition318.finite_smul,
        ContactAmbientCoefficientComposition318.finite_composition]
      change _=finite R T (g.comp f) c L (g s ⊗ₜ[R] x)
      exact (finite_pure R T (g.comp f) c L (g s) x).symm
  | add x y hx hy => simp only [map_add,hx,hy]

lemma infinity_natural (z : S ⊗[R] infinitySections R c L) :
    ContactAmbientCoefficientComposition318.infinity R S T f g c L (infinity R S f c L z)=
      infinity R T (g.comp f) c L
        (ProjectiveSectionParameter318.transport R (infinitySections R c L) S
          (ContactHZeroCoefficientFunctor318.coefficientArrow R S f T g) z) := by
  induction z using TensorProduct.inductionOn with
  | tmul s x =>
      rw [infinity_pure,ContactAmbientCoefficientComposition318.infinity_smul,
        ContactAmbientCoefficientComposition318.infinity_composition]
      change _=infinity R T (g.comp f) c L (g s ⊗ₜ[R] x)
      exact (infinity_pure R T (g.comp f) c L (g s) x).symm
  | add x y hx hy => simp only [map_add,hx,hy]
end ContactAmbientTensorNaturality318
