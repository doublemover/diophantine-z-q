module
public import ProjectiveCoefficientRestriction318
public import ContactOriginalCoefficientActions318
public import SplitKernelBaseChange318
public section
noncomputable section
namespace ContactRelativeCechProjective318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeOverlap318
open ContactOriginalRelativeLineOverlap318 ContactOriginalCoefficientActions318
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : Module R (finiteSections R c L) := finiteModule R c L
local instance : Module R (infinitySections R c L) := infinityModule R c L
local instance : Module R (originalSections R c L) := overlapModule R c L

/-- Projectivity concerns the entire original coefficient module; no
finite R-basis of an affine chart is asserted. -/
theorem finite_chart : Module.Projective R (finiteSections R c L) := by
  letI : Module.Projective R (structuralFinite R c L) :=
    ProjectiveCoefficientRestriction318.original_sections R (finiteRing c) (finiteLine R c L)
  exact Module.Projective.of_equiv (finiteIdentity R c L).symm

theorem infinity_chart : Module.Projective R (infinitySections R c L) := by
  letI : Module.Projective R (structuralInfinity R c L) :=
    ProjectiveCoefficientRestriction318.original_sections R (infinityRing c) (infinityLine R c L)
  exact Module.Projective.of_equiv (infinityIdentity R c L).symm

theorem overlap : Module.Projective R (originalSections R c L) := by
  letI : Module.Projective R (structuralOverlap R c L) :=
    ProjectiveCoefficientRestriction318.original_sections R (oldRing c) (line R c L)
  exact Module.Projective.of_equiv (overlapIdentity R c L).symm

/-- Actual original coefficient Cech differential, retaining the sign
of the genuine Mayer-Vietoris restriction difference. -/
@[expose] def difference : (finiteSections R c L × infinitySections R c L) →ₗ[R]
    originalSections R c L :=
  (ContactOriginalRelativeOverlapSpan318.finiteMap R c L).comp (LinearMap.fst R _ _) -
    (ContactOriginalRelativeOverlapSpan318.infinityMap R c L).comp (LinearMap.snd R _ _)

lemma range_difference : (difference R c L).range =
    ContactRelativeOriginalDerivedQuotient318.imageBoundary R c L := by
  ext x
  change (∃ y, finiteRestriction R c L y.1-infinityRestriction R c L y.2=x) ↔ _
  rw [OriginalTwoImageBoundary318.mem_iff]
  constructor
  · rintro ⟨⟨a,b⟩,h⟩
    exact ⟨a,b,h⟩
  · rintro ⟨a,b,h⟩
    exact ⟨(a,b),h⟩

/-- Actual H1 vanishing, not a formal generic kernel hypothesis, makes
the genuine original Cech differential surjective. -/
lemma surjective_of_h1_zero (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L, x=0) :
    Function.Surjective (difference R c L) := by
  intro x
  have hx : x ∈ ContactRelativeOriginalDerivedQuotient318.imageBoundary R c L := by
    have h := hz (ContactRelativeOriginalDerivedQuotient318.boundary R c L x)
    change x ∈ (ContactRelativeOriginalDerivedQuotient318.boundary R c L).ker at h
    rw [ContactRelativeOriginalDerivedQuotient318.kernel_eq_image] at h
    exact h
  rw [← range_difference] at hx
  exact hx

/-- On the ACTUAL H1-vanishing locus, the original two-term Cech
sequence splits and its actual degree-zero kernel is projective. Finiteness
of this kernel and a FINITE projective cohomology model remain separate. -/
theorem split_kernel (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L, x=0) :
    (∃ s : originalSections R c L →ₗ[R] (finiteSections R c L × infinitySections R c L),
      (difference R c L).comp s = LinearMap.id) ∧
    Module.Projective R (LinearMap.ker (difference R c L)) := by
  letI := finite_chart R c L
  letI := infinity_chart R c L
  letI := overlap R c L
  obtain ⟨s,hs⟩ := SplitKernelBaseChange318.exists_splitting R _ _ (difference R c L)
    (surjective_of_h1_zero R c L hz)
  exact ⟨⟨s,hs⟩,SplitKernelBaseChange318.projective R _ _ (difference R c L) s hs⟩
end ContactRelativeCechProjective318
