module
public import ContactNormalizedAmbientCharts318
public import RelativeAmbientCharts318
public import ContactUniversalRangeCartier318
public import ContactNormalizedGlobalClosedFamily318
public import RestrictedFamilyOriginal318
public import ContactUniversalClassifiedZeroParameter318
public import ContactNormalizedChartZeroFamily318
public section
noncomputable section
namespace ContactNormalizedZeroCartierSquare318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalSectionParameter318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local instance : Module R Γ(L.object,⊤) := OriginalCoefficientCohomology318.sectionModule R
  (ContactRelativeStructuralHOne318.projection R c) L ⊤
local instance : Module.Finite R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).1
local instance : Module.Projective R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).2
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R Γ(L.object,⊤)
local notation "A" => parameterRing R c L
local instance : Algebra ℚ A := ((algebraMap R A).comp (algebraMap ℚ R)).toAlgebra
local instance : IsScalarTower ℚ R A := IsScalarTower.of_algebraMap_eq' rfl
variable (i : Fin F.size)
local notation "S" => ContactNormalizedCartierTest318.ring R c L hz i
local notation "g" => ContactNormalizedCartierTest318.coefficient R c L hz i
local notation "f" => g.comp (parameterCoefficient R c L)
local notation "B" => ContactNormalizedSectionParameter318.scheme R c L hz
local notation "b" => ContactNormalizedSectionParameter318.projection R c L hz
local notation "u" => ProjectiveParameterSliceGluing318.into R Γ(L.object,⊤) i
local notation "q" => ContactRelativeStructuralHOne318.projection R c
local notation "a" => ContactRelativeCoefficientChange318.curveMap R S f c
local notation "d" => ContactRelativeStructuralHOne318.projection S c
local notation "e" => ContactNormalizedCartierTest318.iso R c L hz i
local notation "zt" => ContactNormalizedCartierTest318.into R c L hz i
local notation "pt" => ContactNormalizedCartierTest318.projection R c L hz i
local notation "π" => ContactNormalizedZeroProjection318.projection R c L hz
local notation "zi" => ContactNormalizedGlobalClosedFamily318.into R c L hz
local notation "ci" => ContactNormalizedAmbientCharts318.into R c L hz i

@[expose] def into : ContactNormalizedCartierTest318.scheme R c L hz i ⟶
    ContactNormalizedGlobalZero318.scheme R c L hz :=
  e.hom ≫ ContactNormalizedGlobalZero318.into R c L hz i

lemma projection_square : IsPullback (into R c L hz i) pt π u := by
  let h := ContactNormalizedZeroCartesian318.square R c L hz i
  apply IsPullback.of_iso_pullback (i:=e ≪≫ h.isoPullback)
  · constructor
    rw [into,Category.assoc,ContactNormalizedZeroProjection318.into_projection,
      ← Category.assoc,ContactNormalizedCartierTest318.iso_projection]
  · rw [Iso.trans_hom,Category.assoc,h.isoPullback_hom_fst]
    rfl
  · rw [Iso.trans_hom,Category.assoc,h.isoPullback_hom_snd,
      ContactNormalizedCartierTest318.iso_projection]

lemma comm : zt ≫ ci=into R c L hz i ≫ zi := by
  apply pullback.hom_ext
  · simp only [Category.assoc,ContactNormalizedAmbientCharts318.into_original,
      ContactNormalizedGlobalClosedFamily318.into_original,into,
      ContactNormalizedGlobalOriginal318.into_original,
      ContactNormalizedCartierTest318.iso_original]
  · simp only [Category.assoc,ContactNormalizedAmbientCharts318.into_projection,
      ContactNormalizedGlobalClosedFamily318.into_projection]
    change pt ≫ u=into R c L hz i ≫ π
    exact (projection_square R c L hz i).w.symm

/-- A full Cartesian square for the ACTUAL global closed embedding on
its original coefficient-curve chart. Both ambient and zero projection
squares are used; matching fibers or base points alone would not suffice. -/
lemma square : IsPullback zt (into R c L hz i) ci zi := by
  apply IsPullback.of_right (h₁₂:=d)
    (h₂₂:=ContactNormalizedGlobalClosedFamily318.ambientProjection R c L hz)
  · rw [ContactNormalizedGlobalClosedFamily318.into_projection]
    change IsPullback pt (into R c L hz i) u π
    exact (projection_square R c L hz i).flip
  · exact comm R c L hz i
  · exact (ContactNormalizedAmbientCharts318.square R c L hz i).flip
end ContactNormalizedZeroCartierSquare318
