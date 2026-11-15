module
public import AffineLineSectionsNontrivial318
public import ContactPositiveChartEvaluation318
public import ContactHZeroCoefficientFunctor318
public import SourceScalarExtension318
public section
noncomputable section
namespace ContactGeneratedHZeroFiber318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalCoefficientActions318 ContactCoefficientNativeSections318
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R K : CommRingCat.{0}) [Algebra ℚ R] [Field K] [Algebra ℚ K]
  (f : R →ₐ[ℚ] K) (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : Algebra R K := f.toAlgebra
local instance : Module R Γ(L.object,⊤) := OriginalCoefficientCohomology318.sectionModule R
  (ContactRelativeStructuralHOne318.projection R c) L ⊤
local instance : Module R (finiteSections R c L) := finiteModule R c L
local instance : Module K Γ((L' R K f c L).object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule K
    (ContactRelativeStructuralHOne318.projection K c) (L' R K f c L) ⊤
local instance : Module K (finiteSections K c (L' R K f c L)) := finiteModule K c _

/-- Actual whole finite-chart generation forces a NONZERO original H0
fiber under every field coefficient change. The target affine line is
nontrivial because its original contact ring is geometrically integral;
H1 vanishing supplies the genuine original H0 comparison, not positivity
by itself. -/
theorem exists_nonzero
    (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
    (hg : Submodule.span (R ⊗[ℚ] finiteRing c)
      (Set.range (ContactPositiveChartEvaluation318.finiteRestriction R c L))=⊤) :
    ∃ z : K ⊗[R] Γ(L.object,⊤),z≠0 := by
  let A := CommRingCat.of (R ⊗[ℚ] finiteRing c)
  let D := CommRingCat.of (K ⊗[ℚ] finiteRing c)
  let N := finiteLine R c L
  let N' := finiteLine K c (L' R K f c L)
  let a := ContactRelativeCoefficientChange318.finiteRingMap R K f c
  let e := OriginalCoefficientChartLine318.sheafComparison
    (ContactRelativeCoefficientChange318.curveMap R K f c) a
    (finiteInto R c) (finiteInto K c)
    (ContactRelativeCoefficientChange318.finite_square R K f c) L
  letI : CharZero K := algebraRat.charZero K
  letI : IsDomain (K ⊗[ℚ] finiteRing c) := SourceScalarExtension318.scalarExtension_domain K c
  letI : Nontrivial (OriginalLineAffineModel318.sections D N') :=
    AffineLineSectionsNontrivial318.nontrivial D N'
  have hs := OriginalAffineGeneratorPullback318.span a N N' e
    (ContactPositiveChartEvaluation318.finiteRestriction R c L) hg
  by_contra hn
  push_neg at hn
  have hr (s : Γ(L.object,⊤)) :
      ContactCoefficientLineCharts318.finiteRestriction R K f c L
        ((ContactRelativeOriginalHZero318.pair R c L s).1)=0 := by
    have h := congrArg Prod.fst
      (ContactRelativeHZeroBaseChange318.coordinates R K f c L hz (1:K) s)
    rw [hn ((1:K) ⊗ₜ[R] s),map_zero,map_zero] at h
    simp only [ContactRelativeHZeroBaseChange318.pair_tmul,
      ContactCoefficientNativeSections318.finite_pure,one_smul] at h
    exact h.symm
  have hzspan : Submodule.span (K ⊗[ℚ] finiteRing c)
      (Set.range (fun s => OriginalAffineLinePathSections318.restriction a N N' e
        (ContactPositiveChartEvaluation318.finiteRestriction R c L s)))=⊥ := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro y ⟨s,rfl⟩
      exact hr s
    · exact bot_le
  rw [hzspan] at hs
  have hall (x : OriginalLineAffineModel318.sections D N') : x=0 := by
    have hx : x ∈ (⊤ : Submodule D (OriginalLineAffineModel318.sections D N')) := trivial
    rw [←hs] at hx
    exact hx
  obtain ⟨x,hx⟩ := exists_ne (0 : OriginalLineAffineModel318.sections D N')
  exact hx (hall x)
end ContactGeneratedHZeroFiber318
