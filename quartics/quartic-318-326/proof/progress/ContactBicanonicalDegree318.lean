module
public import ContactBicanonicalProjectiveMap318
public section
noncomputable section
namespace ContactBicanonicalDegree318
open AlgebraicGeometry CategoryTheory Polynomial
open scoped TensorProduct
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ)

@[expose] def affineMap : Spec (CommRingCat.of (ContactKummerOrder318.SourceOrder c)) ⟶
    Spec (CommRingCat.of ℚ[X]) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ[X] (ContactKummerOrder318.SourceOrder c)))

theorem affine_square : affineMap c ≫ JLineAtlas318.chart ℚ 1=
    SourceGlobalAffine318.chartEmbedding c ≫ ContactBicanonicalProjectiveMap318.projectiveMap c := by
  rw [ContactBicanonicalProjectiveMap318.projectiveMap_eq]
  exact (SourceGlobalAffine318.chartEmbedding_over_contact_line c).symm

/-- This is the actual entire base change to the standard t-chart. Thus the
rank-sixteen ring below belongs to this section-constructed Scheme map. -/
theorem affine_pullback : IsPullback (affineMap c) (SourceGlobalAffine318.chartEmbedding c)
    (JLineAtlas318.chart ℚ 1) (ContactBicanonicalProjectiveMap318.projectiveMap c) := by
  apply IsOpenImmersion.isPullback
  · exact (affine_square c).symm
  · rw [ContactBicanonicalProjectiveMap318.projectiveMap_eq,
      SourceGlobalAffine318.chartEmbedding_range,←Scheme.Hom.image_top_eq_opensRange]
    rfl

/-- On the whole standard affine t-chart, the actual map has finite free
coordinate algebra of rank sixteen, including all four finite contacts. -/
theorem affine_finite_free_rank_sixteen :
    Module.Finite ℚ[X] (ContactKummerOrder318.SourceOrder c) ∧
    Module.Free ℚ[X] (ContactKummerOrder318.SourceOrder c) ∧
    Module.finrank ℚ[X] (ContactKummerOrder318.SourceOrder c)=16 :=
  ⟨(ContactKummerOrder318.source_finite_free c).1,
    (ContactKummerOrder318.source_finite_free c).2,
    ContactKummerOrder318.source_rank_sixteen c⟩

/-- The generic fiber of that same actual affine map is the specified
original full field, not a field chosen solely by its degree. -/
@[expose] def genericFiberEquiv :
    RatFunc ℚ ⊗[ℚ[X]] ContactKummerOrder318.SourceOrder c ≃ₐ[RatFunc ℚ]
      SourceFractionField318.L c := ContactKummerOrder318.genericFiber c

theorem generic_degree_sixteen : Module.finrank (RatFunc ℚ) (SourceFractionField318.L c)=16 :=
  KummerTensorField318.source_raw_degree c
end ContactBicanonicalDegree318
