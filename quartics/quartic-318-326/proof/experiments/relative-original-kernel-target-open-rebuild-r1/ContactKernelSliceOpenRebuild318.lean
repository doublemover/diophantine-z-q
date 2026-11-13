module
public import ContactKernelPrincipalSaturationRebuild318
public import SchemeOpenFieldDetectionRebuild318
public import ProjectiveKernelProjectionPointsRebuild318
public section
noncomputable section
namespace ContactKernelSliceOpenRebuild318
open AlgebraicGeometry CategoryTheory LineSheafClass318
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
local notation "D" => ProjectiveKernelNormalizedAlgebras318.principalRing R P Q d
local notation "C" => ProjectiveKernelNormalizedAlgebras318.sliceRing R P Q d
local notation "N" => ContactArbitraryNowhereZeroOpen318.locus R c L
variable (i : Fin F.size)
abbrev principalOriginal := ProjectiveKernelPrincipalCartesian318.into R P Q d i
abbrev sliceOriginal := ProjectiveKernelSliceOriginalRebuild318.into R P Q d i
/-- A genuine open of the actual normalized kernel slice, pulled from
the OLD nowhere-zero open by its literal coordinate-one original point. -/
def sliceLocus : (Spec (CommRingCat.of (C i))).Opens := sliceOriginal R c L i ⁻¹ᵁ N
def principalLocus : (Spec (CommRingCat.of (D i))).Opens := principalOriginal R c L i ⁻¹ᵁ N
/-- All actual prime points are tested through their native residue
fields. The descended slice open pulls back to EXACTLY the original
nowhere-zero principal open; no rational-point density argument is used. -/
lemma preimage : principalLocus R c L i =
    ProjectiveKernelNormalizedLaurent318.projection R P Q d i ⁻¹ᵁ sliceLocus R c L i := by
  apply SchemeOpenFieldDetectionRebuild318.ext_fields
  intro K _ t
  let b : D i →+* K := (Spec.preimage t).hom
  letI : Algebra R K := (b.comp (algebraMap R (D i))).toAlgebra
  letI : Algebra ℚ K := ((algebraMap R K).comp (algebraMap ℚ R)).toAlgebra
  let f : R →ₐ[ℚ] K := { __ := algebraMap R K, commutes' q := rfl }
  let a : D i →ₐ[R] K := { __ := b, commutes' r := rfl }
  have ht : Spec.map (CommRingCat.ofHom a.toRingHom)=t := Spec.map_preimage t
  have hp : Spec.map (CommRingCat.ofHom a.toRingHom) ≫ principalOriginal R c L i =
      Spec.map (CommRingCat.ofHom
        (a.comp (ProjectiveKernelPrincipalCartesian318.intoAlgebra R P Q d i)).toRingHom) := by
    change Spec.map (CommRingCat.ofHom a.toRingHom) ≫ Spec.map
      (ProjectiveKernelPrincipalCartesian318.intoRing R P Q d i) = _
    rw [←ProjectiveKernelPrincipalCartesian318.intoAlgebra_ring,←Spec.map_comp] <;> rfl
  let z := (ProjectiveKernelNormalizedAlgebras318.points R P Q d i K a).2
  have hz : Spec.map (CommRingCat.ofHom z.toRingHom) ≫ sliceOriginal R c L i =
      Spec.map (CommRingCat.ofHom
        (z.comp (ProjectiveKernelSliceOriginalRebuild318.intoAlgebra R P Q d i)).toRingHom) := by
    change Spec.map (CommRingCat.ofHom z.toRingHom) ≫ Spec.map
      (CommRingCat.ofHom (ProjectiveKernelSliceOriginalRebuild318.intoAlgebra R P Q d i).toRingHom) = _
    rw [←Spec.map_comp] <;> rfl
  dsimp only [principalLocus,sliceLocus]
  rw [SchemeOpenFieldDetectionRebuild318.preimage_factor,
    SchemeOpenFieldDetectionRebuild318.preimage_factor,
    SchemeOpenFieldDetectionRebuild318.preimage_factor,←ht,hp,
    ProjectiveKernelProjectionPointsRebuild318.projection_points]
  change (∃ h : Spec K ⟶ N.toScheme, h ≫ N.ι =
      Spec.map (CommRingCat.ofHom
        (a.comp (ProjectiveKernelPrincipalCartesian318.intoAlgebra R P Q d i)).toRingHom)) ↔
    ∃ h : Spec K ⟶ N.toScheme, h ≫ N.ι = Spec.map (CommRingCat.ofHom z.toRingHom) ≫ sliceOriginal R c L i
  rw [hz]
  exact ContactKernelPrincipalSaturationRebuild318.factor_iff R c L K f i a
end ContactKernelSliceOpenRebuild318
