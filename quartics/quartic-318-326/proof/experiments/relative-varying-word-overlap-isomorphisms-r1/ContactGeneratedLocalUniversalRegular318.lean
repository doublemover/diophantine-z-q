module
public import ContactPositiveChartEvaluation318
public section
noncomputable section
namespace ContactGeneratedLocalUniversalRegular318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalCoefficientActions318 ContactRelativeGeometricTwist318
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))

@[expose] def bound : ℕ := Classical.choose (ContactPositiveChartEvaluation318.exists_bound R c L)
abbrev generatedLine := twist R c L (((bound R c L)+1 : ℕ) : ℤ)

lemma properties :
    (∀ x : NonreducedLineMayerVietoris318.H1 (generatedLine R c L),x=0) ∧
    Submodule.span (R ⊗[ℚ] finiteRing c)
      (Set.range (ContactPositiveChartEvaluation318.finiteRestriction R c (generatedLine R c L)))=⊤ ∧
    Submodule.span (R ⊗[ℚ] infinityRing c)
      (Set.range (ContactPositiveChartEvaluation318.infinityRestriction R c (generatedLine R c L)))=⊤ :=
  Classical.choose_spec (ContactPositiveChartEvaluation318.exists_bound R c L)
    ((bound R c L)+1) (Nat.le_succ _)

abbrev P := Γ((generatedLine R c L).object,⊤)
local instance : Module R (P R c L) := OriginalCoefficientCohomology318.sectionModule R
  (ContactRelativeStructuralHOne318.projection R c) (generatedLine R c L) ⊤
local instance : Module.Finite R (P R c L) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c (generatedLine R c L)
    (properties R c L).1).1
local instance : Module.Projective R (P R c L) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c (generatedLine R c L)
    (properties R c L).1).2

section Finite
variable (B : CommRingCat.{0}) (f : CommRingCat.of (R ⊗[ℚ] finiteRing c) ⟶ B)
  (N : Line (Spec B))
  (e : (Scheme.Modules.pullback (Spec.map f)).obj (finiteLine R c (generatedLine R c L)).object ≅ N.object)
  (v : OriginalLineAffineModel318.sections B N ≃ₗ[B] B)
local instance : Algebra R B := (f.hom.comp (algebraMap R (R ⊗[ℚ] finiteRing c))).toAlgebra

@[expose] def finiteEvaluation : P R c L →ₗ[R] B :=
  OriginalAffineFrameEvaluation318.evaluation R (CommRingCat.of (R ⊗[ℚ] finiteRing c)) B f
    (finiteLine R c (generatedLine R c L)) N e v (P R c L)
    (ContactPositiveChartEvaluation318.finiteRestriction R c (generatedLine R c L))

/-- At ANY genuine original affine finite-chart path and local frame,
the SAME universal section coefficient is regular. Both the positive
index and generating section needed for primitivity are produced. -/
theorem finite_regular (a : B ⊗[R] ProjectiveSectionParameter318.algebra R (P R c L))
    (ha : a * UniversalScalarCoordinate318.coefficient R (P R c L) B
      (finiteEvaluation R c L B f N e v)=0) : a=0 :=
  OriginalAffineFrameEvaluation318.regular R (CommRingCat.of (R ⊗[ℚ] finiteRing c)) B f
    (finiteLine R c (generatedLine R c L)) N e v (P R c L)
    (ContactPositiveChartEvaluation318.finiteRestriction R c (generatedLine R c L))
    (properties R c L).2.1 a ha
end Finite

section Infinity
variable (B : CommRingCat.{0}) (f : CommRingCat.of (R ⊗[ℚ] infinityRing c) ⟶ B)
  (N : Line (Spec B))
  (e : (Scheme.Modules.pullback (Spec.map f)).obj (infinityLine R c (generatedLine R c L)).object ≅ N.object)
  (v : OriginalLineAffineModel318.sections B N ≃ₗ[B] B)
local instance : Algebra R B := (f.hom.comp (algebraMap R (R ⊗[ℚ] infinityRing c))).toAlgebra

@[expose] def infinityEvaluation : P R c L →ₗ[R] B :=
  OriginalAffineFrameEvaluation318.evaluation R (CommRingCat.of (R ⊗[ℚ] infinityRing c)) B f
    (infinityLine R c (generatedLine R c L)) N e v (P R c L)
    (ContactPositiveChartEvaluation318.infinityRestriction R c (generatedLine R c L))

/-- Same conclusion on the whole infinity route; no finite-chart frame
is silently reused on the reciprocal source. -/
theorem infinity_regular (a : B ⊗[R] ProjectiveSectionParameter318.algebra R (P R c L))
    (ha : a * UniversalScalarCoordinate318.coefficient R (P R c L) B
      (infinityEvaluation R c L B f N e v)=0) : a=0 :=
  OriginalAffineFrameEvaluation318.regular R (CommRingCat.of (R ⊗[ℚ] infinityRing c)) B f
    (infinityLine R c (generatedLine R c L)) N e v (P R c L)
    (ContactPositiveChartEvaluation318.infinityRestriction R c (generatedLine R c L))
    (properties R c L).2.2 a ha
end Infinity
end ContactGeneratedLocalUniversalRegular318
