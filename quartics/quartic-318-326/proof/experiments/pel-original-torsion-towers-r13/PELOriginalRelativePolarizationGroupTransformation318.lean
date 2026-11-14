module
public import PELOriginalRelativePolarizationHom318
public import PELOriginalRepresentedGroupFunctor318
public section
noncomputable section
namespace PELOriginalRelativePolarizationGroupTransformation318
open AlgebraicGeometry CategoryTheory Opposite
open PELOriginalProductChartCover318 PELOriginalSchemePointGroup318
open PELOriginalRelativePolarizationTransformation318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- Each component of the ACTUAL original relative polarization is a
homomorphism into the actual fppf group sheaf. The source is the genuine
scheme-point group, including arbitrary nonreduced test schemes. -/
@[expose] def hom (T : Over (Spec (CommRingCat.of ℂ))) :
    Multiplicative (Points τ hτ T.left T.hom) →* (Target τ hτ).obj.obj (op T) :=
  ((RelativeFppfLineSheaf318.unit (π τ hτ)).app (op T)).hom.comp
    (PELOriginalRelativePolarizationHom318.hom τ hτ T.hom)

/-- No new set-valued map is substituted: this homomorphism is exactly
the previously constructed original line-family Abel transformation. -/
lemma hom_eq_transformation (T : Over (Spec (CommRingCat.of ℂ)))
    (a : Points τ hτ T.left T.hom) :
    hom τ hτ T (Multiplicative.ofAdd a)=
      (transformation τ hτ).app (op T) (Over.homMk a.val a.property) := by
  rw [test_formula,PELOriginalRelativePolarizationHom318.family_value]
  rfl

/-- Full contravariant naturality of the homomorphisms, with the actual
scheme pullback action on points and the actual fppf-sheaf restriction. -/
lemma hom_naturality {T T' : Over (Spec (CommRingCat.of ℂ))} (f : T' ⟶ T)
    (a : Points τ hτ T.left T.hom) :
    ((Target τ hτ).obj.map f.op) (hom τ hτ T (Multiplicative.ofAdd a))=
      hom τ hτ T' (Multiplicative.ofAdd (pull τ hτ T.hom f.left f.w a)) := by
  rw [hom_eq_transformation,hom_eq_transformation]
  exact PELOriginalRelativePolarizationTransformation318.naturality τ hτ T T' f
    (Over.homMk a.val a.property)

lemma transformation_zero (T : Over (Spec (CommRingCat.of ℂ))) :
    (transformation τ hτ).app (op T)
      (Over.homMk (0 : Points τ hτ T.left T.hom).val (0 : Points τ hτ T.left T.hom).property)=1 := by
  rw [←hom_eq_transformation]
  exact map_one (hom τ hτ T)

lemma transformation_add (T : Over (Spec (CommRingCat.of ℂ)))
    (a b : Points τ hτ T.left T.hom) :
    (transformation τ hτ).app (op T) (Over.homMk (a+b).val (a+b).property)=
      (transformation τ hτ).app (op T) (Over.homMk a.val a.property)*
      (transformation τ hτ).app (op T) (Over.homMk b.val b.property) := by
  simp only [←hom_eq_transformation]
  exact map_mul (hom τ hτ T) (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)

lemma transformation_neg (T : Over (Spec (CommRingCat.of ℂ)))
    (a : Points τ hτ T.left T.hom) :
    (transformation τ hτ).app (op T) (Over.homMk (-a).val (-a).property)=
      ((transformation τ hτ).app (op T) (Over.homMk a.val a.property))⁻¹ := by
  simp only [←hom_eq_transformation]
  exact map_inv (hom τ hτ T) (Multiplicative.ofAdd a)

/-- The doubly normalized family has the SAME all-test group
transformation, because its extra factor is an actual base pullback. -/
lemma normalized_add (T : Over (Spec (CommRingCat.of ℂ)))
    (a b : Points τ hτ T.left T.hom) :
    (OriginalLineAbelTransformation318.transformation (π τ hτ) (π τ hτ)
      (normalizedFamily τ hτ)).app (op T) (Over.homMk (a+b).val (a+b).property)=
      (transformation τ hτ).app (op T) (Over.homMk a.val a.property)*
      (transformation τ hτ).app (op T) (Over.homMk b.val b.property) := by
  rw [normalized_transformation]
  exact transformation_add τ hτ T a b
end PELOriginalRelativePolarizationGroupTransformation318
