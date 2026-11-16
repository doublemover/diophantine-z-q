module
public import OriginalNormalAffineDuality318
public section
noncomputable section
namespace OriginalNormalDualSheafSections318
open NumberField Polynomial AlgebraicGeometry CategoryTheory
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318 OriginalAllPlaceNormalModel318
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))
  (D : OriginalAllPlaceNormalizedData318.Data c t w) (M : Realization c t w D)
local notation "R" => V c t w
local notation "P" => Polynomial R
local notation "a" => contacts c t w
local notation "d" => D.coefficients
local notation "B" => SourceOpenRing c t w D
local notation "F" => IntegralDistinctContactOpen318.Base R a d
local notation "N" => IntegralFourRootNormalizationConductor318.normalOrder R a d
local notation "L" => NormalTraceDualModule318.lattice (F:=F) N

/-- Full affine sections expressed as all maps from the actual tilde
unit module to the actual trace-dual sheaf, not selected local frames. -/
abbrev Sections := tilde (R:=CommRingCat.of N) (ModuleCat.of N N) ⟶
  IntegralNormalTraceSheafDuality318.traceSheaf R a d

@[expose] def coefficient (s : Sections c t w D) : B :=
  (AffineTildeHomEquivalence318.equivalence (ModuleCat.of N N) (ModuleCat.of N L) s 1).val

lemma coefficient_mem (s : Sections c t w D) : coefficient c t w D s ∈
    IntegralFourRootNormalizationConductor318.codifferent R a d :=
  (AffineTildeHomEquivalence318.equivalence (ModuleCat.of N N) (ModuleCat.of N L) s 1).property

@[expose] def value (s : Sections c t w D) : K c t :=
  M.fieldPoint (coefficient c t w D s)

lemma value_mem (s : Sections c t w D) : value c t w D M s ∈
    OriginalNormalizationConductorSpecialization318.codifferentValues c t w D M :=
  ⟨coefficient c t w D s,coefficient_mem c t w D s,rfl⟩

/-- Every actual trace-codifferent coefficient supplies a full native
sheaf section by its normal-order multiplication map. -/
@[expose] def section (z : L) : Sections c t w D :=
  (tilde.functor (CommRingCat.of N)).map (ModuleCat.ofHom
    ({ toFun := fun n => n • z
       map_add' := fun n m => add_smul n m z
       map_smul' := fun n m => smul_assoc n m z } : N →ₗ[N] L))

lemma coefficient_section (z : L) : coefficient c t w D (section c t w D z)=z.val := by
  unfold coefficient section
  rw [AffineTildeHomEquivalence318.map_value]
  change ((1:N) • z).val=z.val
  rw [one_smul]

/-- No original-point coefficient is lost by passing from the actual
finite dual to native affine sheaf sections. The image is EXACT. -/
theorem value_range : Set.range (value c t w D M)=
    (OriginalNormalizationConductorSpecialization318.codifferentValues c t w D M : Set (K c t)) := by
  ext x
  constructor
  · rintro ⟨s,rfl⟩
    exact value_mem c t w D M s
  · rintro ⟨z,hz,rfl⟩
    refine ⟨section c t w D ⟨z,hz⟩,?_⟩
    change M.fieldPoint (coefficient c t w D (section c t w D ⟨z,hz⟩))=M.fieldPoint z
    rw [coefficient_section]

/-- Every actual affine dual-sheaf section obeys the proved corrected
cotangent bound at the SAME original signed closed center. This does not
claim the correction is unnecessary or that affine duality is Hodge. -/
theorem corrected_mem (ht : w (t : K c t) ≤ 1) (s : Sections c t w D) :
    OriginalNormalizationDifferentValue318.differentValue c t w D M*value c t w D M s ∈
      OriginalNormalCenterCoordinateLattice318.scalarLattice c t w D M :=
  OriginalCotangentDifferentBound318.different_mul_mem c t w D M ht _ (value_mem c t w D M s)

theorem corrected_pairing (ht : w (t : K c t) ≤ 1) (s : Sections c t w D)
    (q : K c t) (hq : q ∈ OriginalNormalCenterDualImage318.dual c t w D M) :
    w (q*(OriginalNormalizationDifferentValue318.differentValue c t w D M*value c t w D M s)) ≤ 1 :=
  OriginalCotangentDifferentBound318.corrected_pairing c t w D M ht _
    (value_mem c t w D M s) q hq
end OriginalNormalDualSheafSections318
