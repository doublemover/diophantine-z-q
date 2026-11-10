module
public import IntegralGenericIso318
public import NormalizationSourceIso318
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public section
noncomputable section
namespace NormalizationBirationalComparison318
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u v
variable {X Y B : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (j : X ⟶ Y) (p : Y ⟶ B) [IsDominant j] [IsIntegralHom p]
  [QuasiCompact (j ≫ p)] [QuasiSeparated (j ≫ p)]
  [IsIso (DominantFunctionField318.map j)]

/-- The already specified map into the original integral model, extended by
the actual normalization universal property. -/
@[expose] def comparison : (j ≫ p).normalization ⟶ Y :=
  (j ≫ p).normalizationDesc j p rfl

@[reassoc] theorem comparison_source :
    (j ≫ p).toNormalization ≫ comparison j p = j :=
  (j ≫ p).toNormalization_normalizationDesc j p rfl

@[reassoc] theorem comparison_base : comparison j p ≫ p = (j ≫ p).fromNormalization :=
  (j ≫ p).normalizationDesc_comp j p rfl

instance comparison_integral : IsIntegralHom (comparison j p) :=
  inferInstanceAs (IsIntegralHom ((j ≫ p).normalizationDesc j p rfl))

instance comparison_dominant : IsDominant (comparison j p) := by
  haveI : IsDominant ((j ≫ p).toNormalization ≫ comparison j p) := by
    rw [comparison_source]
    infer_instance
  exact IsDominant.of_comp (j ≫ p).toNormalization (comparison j p)

/-- Generic pullback is the SAME map, not a chosen abstract field equivalence.
The composite is the original generic isomorphism and the second field map
is injective, which forces the first field map to be surjective. -/
theorem comparison_generic : IsIso (DominantFunctionField318.map (comparison j p)) := by
  let a := DominantFunctionField318.map (comparison j p)
  let b := DominantFunctionField318.map (j ≫ p).toNormalization
  have he : DominantFunctionField318.map j = a ≫ b := by
    rw [← comparison_source j p, DominantFunctionField318.map_comp]
  have hs := (ConcreteCategory.bijective_of_isIso (DominantFunctionField318.map j)).surjective
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  refine ⟨a.hom.injective, ?_⟩
  intro y
  obtain ⟨x, hx⟩ := hs (b y)
  refine ⟨x, b.hom.injective ?_⟩
  rw [he] at hx
  exact hx

/-- The genuine normalization comparison is an isomorphism on an actual
normal affine cover, hence on the entire original integral model. -/
theorem comparison_isIso {ι : Type v} (V : ι → Y.affineOpens)
    (hcover : ⨆ i, (V i).1 = ⊤)
    (hnormal : ∀ i, IsIntegrallyClosed Γ(Y, (V i).1)) : IsIso (comparison j p) := by
  letI := comparison_generic j p
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := MorphismProperty.isomorphisms Scheme)
  intro y
  have hy : y ∈ ⨆ i, (V i).1 := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hy
  letI : Nonempty (V i).1 := ⟨⟨y, hi⟩⟩
  letI := hnormal i
  exact ⟨(V i).1, hi, IntegralGenericIso318.restrict_isIso (comparison j p) (V i).1 (V i).2⟩

@[expose] def iso {ι : Type v} (V : ι → Y.affineOpens)
    (hcover : ⨆ i, (V i).1 = ⊤)
    (hnormal : ∀ i, IsIntegrallyClosed Γ(Y, (V i).1)) : (j ≫ p).normalization ≅ Y := by
  letI := comparison_isIso j p V hcover hnormal
  exact asIso (comparison j p)

@[reassoc] theorem iso_source {ι : Type v} (V : ι → Y.affineOpens)
    (hcover : ⨆ i, (V i).1 = ⊤) (hnormal : ∀ i, IsIntegrallyClosed Γ(Y, (V i).1)) :
    (j ≫ p).toNormalization ≫ (iso j p V hcover hnormal).hom = j :=
  comparison_source j p
@[reassoc] theorem iso_base {ι : Type v} (V : ι → Y.affineOpens)
    (hcover : ⨆ i, (V i).1 = ⊤) (hnormal : ∀ i, IsIntegrallyClosed Γ(Y, (V i).1)) :
    (iso j p V hcover hnormal).hom ≫ p = (j ≫ p).fromNormalization :=
  comparison_base j p
end NormalizationBirationalComparison318
