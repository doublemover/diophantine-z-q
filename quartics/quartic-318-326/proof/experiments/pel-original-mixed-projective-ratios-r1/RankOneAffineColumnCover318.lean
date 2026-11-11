module
public import AffineComplexProjectiveVector318
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Gluing
public section
noncomputable section
namespace RankOneAffineColumnCover318
open AlgebraicGeometry CategoryTheory
variable {ι κ A : Type*} [CommRing A] [Algebra ℂ A]
variable (w : ι → κ → A)
local instance standardGrading : GradedAlgebra (ComplexProjectiveMarkerPoint318.grading (ι := ι)) :=
  MvPolynomial.gradedAlgebra

abbrev EntryRing (rs : ι × κ) := Localization.Away (w rs.1 rs.2)
@[expose] def entryMap (rs : ι × κ) :
    Spec (CommRingCat.of (EntryRing w rs)) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (EntryRing w rs)))
instance entry_open (rs : ι × κ) : IsOpenImmersion (entryMap w rs) :=
  IsOpenImmersion.of_isLocalization (w rs.1 rs.2)

@[reassoc] theorem entry_base (rs : ι × κ) :
    entryMap w rs≫AffineComplexProjectiveVector318.structureMap=
      AffineComplexProjectiveVector318.structureMap (A := EntryRing w rs) := by
  rw [entryMap,AffineComplexProjectiveVector318.structureMap,
    AffineComplexProjectiveVector318.structureMap,←Spec.map_comp]
  congr 1
  ext c
  exact (IsScalarTower.algebraMap_apply ℂ A (EntryRing w rs) c).symm

@[expose] def column (rs : ι × κ) (i : ι) : EntryRing w rs :=
  algebraMap A (EntryRing w rs) (w i rs.2)
lemma column_span (rs : ι × κ) : Ideal.span (Set.range (column w rs))=⊤ := by
  apply Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (Set.mem_range_self rs.1))
  exact IsLocalization.Away.algebraMap_isUnit (w rs.1 rs.2)

@[expose] def localMap (rs : ι × κ) : Spec (CommRingCat.of (EntryRing w rs)) ⟶
    Proj (ComplexProjectiveMarkerPoint318.grading (ι := ι)) :=
  AffineComplexProjectiveVector318.morphism (column w rs) (column_span w rs)

lemma prime_nonvanishing (hw : Ideal.span (Set.range (fun rs : ι × κ => w rs.1 rs.2))=⊤)
    (p : PrimeSpectrum A) : ∃ rs : ι × κ, w rs.1 rs.2∉p.asIdeal := by
  by_contra h
  push_neg at h
  have hi : Ideal.span (Set.range (fun rs : ι × κ => w rs.1 rs.2))≤p.asIdeal := by
    apply Ideal.span_le.mpr
    rintro _ ⟨rs,rfl⟩
    exact h rs
  rw [hw] at hi
  exact p.isPrime.ne_top (top_le_iff.mp hi)

/-- The actual principal localizations at ALL matrix entries cover
Spec(A) whenever the full entry ideal is the unit ideal. No closed-point
or rank assertion is used to drop any prime from this cover. -/
@[expose] def cover (hw : Ideal.span (Set.range (fun rs : ι × κ => w rs.1 rs.2))=⊤) :
    (Spec (CommRingCat.of A)).OpenCover where
  I₀ := ι × κ
  X rs := Spec (CommRingCat.of (EntryRing w rs))
  f := entryMap w
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    constructor
    · intro p
      obtain ⟨rs,hrs⟩ := prime_nonvanishing w hw p
      have hr : p∈Set.range (entryMap w rs) := by
        change p∈Set.range (PrimeSpectrum.comap (algebraMap A (EntryRing w rs)))
        rw [PrimeSpectrum.localization_away_comap_range (EntryRing w rs) (w rs.1 rs.2)]
        exact hrs
      obtain ⟨q,hq⟩ := hr
      exact ⟨rs,q,hq⟩
    · intro rs
      infer_instance

/-- The underlying A-point of any actual localized complex point. -/
@[expose] def baseEvaluation (rs : ι × κ) (f : EntryRing w rs →ₐ[ℂ] ℂ) : A →ₐ[ℂ] ℂ :=
  f.comp (IsScalarTower.toAlgHom ℂ A (EntryRing w rs))

lemma base_nonzero (rs : ι × κ) (f : EntryRing w rs →ₐ[ℂ] ℂ) :
    baseEvaluation w rs f (w rs.1 rs.2)≠0 := by
  exact isUnit_iff_ne_zero.mp ((IsLocalization.Away.algebraMap_isUnit
    (w rs.1 rs.2) (S := EntryRing w rs)).map f.toRingHom)

@[reassoc] lemma base_point (rs : ι × κ) (f : EntryRing w rs →ₐ[ℂ] ℂ) :
    Spec.map (CommRingCat.ofHom f.toRingHom)≫entryMap w rs=
      Spec.map (CommRingCat.ofHom (baseEvaluation w rs f).toRingHom) := by
  rw [entryMap,←Spec.map_comp]
  rfl

lemma local_point_action [Finite ι] (rs : ι × κ) (f : EntryRing w rs →ₐ[ℂ] ℂ) :
    Spec.map (CommRingCat.ofHom f.toRingHom)≫localMap w rs=
      ComplexProjectiveSchemePoint318.point
        (fun i => baseEvaluation w rs f (w i rs.2))
        ⟨rs.1,base_nonzero w rs f⟩ :=
  AffineComplexProjectiveVector318.point_action (column w rs) (column_span w rs) f
end RankOneAffineColumnCover318
