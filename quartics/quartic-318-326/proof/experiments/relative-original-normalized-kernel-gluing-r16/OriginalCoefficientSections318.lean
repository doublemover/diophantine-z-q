module
public import OriginalCoefficientTensor318
public import OriginalCoefficientChartLine318
public section
noncomputable section
namespace OriginalCoefficientSections318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open scoped TensorProduct ChangeOfRings
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (k R S B : CommRingCat.{u}) [Algebra k R] [Algebra k S] [Algebra k B]
  (f : R →ₐ[k] S)
variable {X : Scheme.{u}} (p : X ⟶ Spec k) (j : Spec B ⟶ X)
  (hj : j ≫ p = Spec.map (CommRingCat.ofHom (algebraMap k B)))
  (L : Line (RelativeOriginalAffineChart318.family k R p))

abbrev oldSections := OriginalLineAffineModel318.sections (CommRingCat.of (R ⊗[k] B))
  (LineSheafPullback318.line (RelativeOriginalAffineChart318.into k R B p j hj) L)
abbrev newSections := OriginalLineAffineModel318.sections (CommRingCat.of (S ⊗[k] B))
  (LineSheafPullback318.line (RelativeOriginalAffineChart318.into k S B p j hj)
    (LineSheafPullback318.line (RelativeCoefficientChange318.familyMap k R S f p) L))
local instance : Module R (oldSections k R B p j hj L) :=
  Module.compHom _ (algebraMap R (R ⊗[k] B))
local instance : Module S (newSections k R S B f p j hj L) :=
  Module.compHom _ (algebraMap S (S ⊗[k] B))

/-- Canonical COEFFICIENT-only base change of sections on the entire
original affine chart. The target is the literal pulled-back original
line on the actual S-test. It is not a chart-ring tensor left unconverted. -/
@[expose] def equivalence :
    letI := OriginalCoefficientTensor318.coefficientAlgebra k R S f
    S ⊗[R] oldSections k R B p j hj L ≃ₗ[S]
    newSections k R S B f p j hj L := by
  letI := OriginalCoefficientTensor318.coefficientAlgebra k R S f
  exact (OriginalCoefficientTensor318.categoricalEquivalence k R S B f
    (oldSections k R B p j hj L)).symm.trans
      (((ModuleCat.restrictScalars (algebraMap S (S ⊗[k] B))).mapIso
        (OriginalCoefficientChartLine318.sectionsComparison
          (RelativeCoefficientChange318.familyMap k R S f p)
          (RelativeCoefficientChange318.ringMap k R S B f)
          (RelativeOriginalAffineChart318.into k R B p j hj)
          (RelativeOriginalAffineChart318.into k S B p j hj)
          (RelativeCoefficientChange318.into_square k R S B f p j hj) L)).toLinearEquiv)

lemma unit (m : oldSections k R B p j hj L) :
    letI := OriginalCoefficientTensor318.coefficientAlgebra k R S f
    equivalence k R S B f p j hj L ((1 : S) ⊗ₜ[R] m) =
      OriginalCoefficientChartLine318.originalRestriction
        (RelativeCoefficientChange318.familyMap k R S f p)
        (RelativeCoefficientChange318.ringMap k R S B f)
        (RelativeOriginalAffineChart318.into k R B p j hj)
        (RelativeOriginalAffineChart318.into k S B p j hj)
        (RelativeCoefficientChange318.into_square k R S B f p j hj) L m := by
  letI := OriginalCoefficientTensor318.coefficientAlgebra k R S f
  change (OriginalCoefficientChartLine318.sectionsComparison _ _ _ _ _ L).hom
    ((OriginalCoefficientTensor318.categoricalEquivalence k R S B f
      (oldSections k R B p j hj L)).symm ((1 : S) ⊗ₜ[R] m)) = _
  rw [OriginalCoefficientTensor318.categoricalEquivalence_symm_tmul]
  exact OriginalCoefficientChartLine318.unit _ _ _ _ _ L m

lemma pure_tensor (s : S) (m : oldSections k R B p j hj L) :
    letI := OriginalCoefficientTensor318.coefficientAlgebra k R S f
    equivalence k R S B f p j hj L (s ⊗ₜ[R] m) =
      s • OriginalCoefficientChartLine318.originalRestriction
        (RelativeCoefficientChange318.familyMap k R S f p)
        (RelativeCoefficientChange318.ringMap k R S B f)
        (RelativeOriginalAffineChart318.into k R B p j hj)
        (RelativeOriginalAffineChart318.into k S B p j hj)
        (RelativeCoefficientChange318.into_square k R S B f p j hj) L m := by
  letI := OriginalCoefficientTensor318.coefficientAlgebra k R S f
  have h : s ⊗ₜ[R] m = s • ((1 : S) ⊗ₜ[R] m) := by
    simp only [TensorProduct.smul_tmul',smul_eq_mul,mul_one]
  rw [h,(equivalence k R S B f p j hj L).map_smul,unit]
end OriginalCoefficientSections318
