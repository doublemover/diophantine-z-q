module
public import ActualTwoDescentOriginalTwoChartCubicScheme318
public section
noncomputable section
namespace ActualTwoDescentOriginalCubicChartCover318
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ActualTwoDescentInfinityChartRing318 ActualTwoDescentOriginalTwoChartCubicScheme318
variable {K : Type*} [Field K] [CharZero K]

/-- The native chart inclusions cover EVERY scheme point, not only
K-rational projective triples or the three marked roots. -/
theorem actual_original_charts_cover (n : K) (p : originalCubicScheme n) :
    (∃ a,affineChart n a=p) ∨ (∃ b,infinityChart n b=p) := by
  obtain ⟨i,q,hq⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective
    (span (intoAffine n) (intoInfinity n)) p
  cases i with
  | none =>
    left
    refine ⟨intoAffine n q,?_⟩
    change (intoAffine n ≫ affineChart n) q=p
    rw [show intoAffine n ≫ affineChart n=
      colimit.ι (span (intoAffine n) (intoInfinity n)) WalkingSpan.zero from
        colimit.w (span (intoAffine n) (intoInfinity n)) WalkingSpan.Hom.fst]
    exact hq
  | some j =>
    cases j with
    | left => exact Or.inl ⟨q,hq⟩
    | right => exact Or.inr ⟨q,hq⟩

/-- The original infinity evaluation supplies an actual section of the
same glued cubic scheme over K. -/
def infinitySection (n : K) : Spec (CommRingCat.of K) ⟶ originalCubicScheme n :=
  Spec.map (CommRingCat.ofHom (originEvaluation n)) ≫ infinityChart n
lemma actual_infinity_section (n : K) : infinitySection n ≫ structureMap n=𝟙 _ := by
  have he : (originEvaluation n).comp (chartCoefficient n)=RingHom.id K := by
    ext a
    exact actual_origin_coefficient n a
  unfold infinitySection
  rw [Category.assoc,actual_infinity_chart_structure]
  unfold infinityStructure
  rw [←Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((originEvaluation n).comp (chartCoefficient n)))=𝟙 _
  rw [he]
  simp
end ActualTwoDescentOriginalCubicChartCover318
