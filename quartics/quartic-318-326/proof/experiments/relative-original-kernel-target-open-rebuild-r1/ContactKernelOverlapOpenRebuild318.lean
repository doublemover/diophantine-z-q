module
public import ContactKernelOverlapFactorRebuild318
public import ContactKernelSliceOpenRebuild318
public section
noncomputable section
namespace ContactKernelOverlapOpenRebuild318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalCoefficientActions318 ContactCoefficientNativeSections318 ContactOriginalSectionKernel318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : Module R (infinitySections R c L) := infinityModule R c L
local instance (N : Line (curve R c)) : Module R Γ(N.object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule R (ContactRelativeStructuralHOne318.projection R c) N ⊤
local instance : Module.Finite R (zeroTerm R c L) := (projective_terms R c L).1.1
local instance : Module.Projective R (zeroTerm R c L) := (projective_terms R c L).1.2
local instance : Module.Finite R (oneTerm R c L) := (projective_terms R c L).2.1
local instance : Module.Projective R (oneTerm R c L) := (projective_terms R c L).2.2
local notation "P" => zeroTerm R c L
local notation "Q" => oneTerm R c L
local notation "d" => boundary R c L
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "D" => ProjectiveKernelOverlapAlgebras318.ring R P Q d
/-- Equality on the ENTIRE actual overlap, detected by every native
residue field and not just the base-field points of its reduction. -/
lemma agreement (i j : Fin F.size) :
    ProjectiveKernelOverlapAlgebras318.left R P Q d i j ⁻¹ᵁ ContactKernelSliceOpenRebuild318.sliceLocus R c L i =
    ProjectiveKernelOverlapSchemes318.right R P Q d i j ⁻¹ᵁ ContactKernelSliceOpenRebuild318.sliceLocus R c L j := by
  apply SchemeOpenFieldDetectionRebuild318.ext_fields
  intro K _ t
  let b : D i j →+* K := (Spec.preimage t).hom
  letI : Algebra R K := (b.comp (algebraMap R (D i j))).toAlgebra
  letI : Algebra ℚ K := ((algebraMap R K).comp (algebraMap ℚ R)).toAlgebra
  let f : R →ₐ[ℚ] K := { __ := algebraMap R K, commutes' q := rfl }
  let a : D i j →ₐ[R] K := { __ := b, commutes' r := rfl }
  have ht : Spec.map (CommRingCat.ofHom a.toRingHom)=t := Spec.map_preimage t
  dsimp only [ContactKernelSliceOpenRebuild318.sliceLocus]
  rw [SchemeOpenFieldDetectionRebuild318.preimage_factor,
    SchemeOpenFieldDetectionRebuild318.preimage_factor,
    SchemeOpenFieldDetectionRebuild318.preimage_factor,
    SchemeOpenFieldDetectionRebuild318.preimage_factor,←ht]
  simp only [Category.assoc,ContactKernelSliceOpenRebuild318.sliceOriginal,
    ProjectiveKernelOverlapOriginalRebuild318.left_original,
    ProjectiveKernelOverlapOriginalRebuild318.right_original,←Spec.map_comp]
  exact (ContactKernelOverlapFactorRebuild318.factor_iff R c L K f i j a).symm
end ContactKernelOverlapOpenRebuild318
