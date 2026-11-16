module
public import PELOriginalOrbitRelation318
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.IsLocalHomeomorph
public section
noncomputable section
namespace PELOriginalComparisonHomeomorph318
open PELOriginalSideQuotient318 PELUnlevelledComplexBase318
open PELEffectiveNormOneAction318 PELOriginalOrbitRelation318

/-- Every actual arithmetic identification between polygon representatives
already belongs to the ORIGINAL generated side relation. -/
theorem arithmeticComparison_injective : Function.Injective arithmeticComparison := by
  intro x y h
  obtain ⟨a,rfl⟩ := Quotient.mk_surjective x
  obtain ⟨b,rfl⟩ := Quotient.mk_surjective y
  change projection a.val=projection b.val at h
  obtain ⟨g,hg⟩ := (show ∃ g : effectiveGroup, g • b.val=a.val from Quotient.exact h)
  obtain ⟨u,rfl⟩ := effectiveMap_surjective g
  exact (polygon_orbit_quotient b a u hg).symm

/-- The literal generated polygon quotient is homeomorphic to the SAME
original norm-one arithmetic curve. No abstract fundamental-domain,
local-cover, cellulation, genus or Riemann–Hurwitz assumption occurs. -/
@[expose] def originalPolygonArithmeticHomeomorph : PairedPolygon ≃ₜ UnlevelledBase :=
  (Equiv.ofBijective arithmeticComparison
    ⟨arithmeticComparison_injective,arithmeticComparison_surjective⟩).toHomeomorphOfContinuousClosed
      arithmeticComparison_continuous arithmeticComparison_continuous.isClosedMap

theorem homeomorph_is_original_comparison (x : PairedPolygon) :
    originalPolygonArithmeticHomeomorph x=arithmeticComparison x := rfl

theorem comparison_local_homeomorph : IsLocalHomeomorph arithmeticComparison :=
  originalPolygonArithmeticHomeomorph.isLocalHomeomorph

/-- Exact equality of the generated relation with the full original
arithmetic orbit relation, rather than defining the former to be the latter. -/
theorem side_relation_iff_arithmetic (a b : PELOriginalDirichletPolygon318.originalDomain) :
    Relation.EqvGen sideRelation a b ↔ projection a.val=projection b.val := by
  constructor
  · exact generated_projection_eq a b
  · intro h
    have he : arithmeticComparison (polygonProjection a)=arithmeticComparison (polygonProjection b) := h
    exact Quotient.exact (arithmeticComparison_injective he)
end PELOriginalComparisonHomeomorph318
