module
public import ThreeRationalModuliCompletion318
public import DedekindAffineFlat318
public import FiniteFlatGenericRank318
public section
noncomputable section
namespace ThreeJFiniteFlatRank318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance : IsFinite ThreeProjectiveJMap318.map := ThreeJGlobalFinite318.map_finite

/-- Flatness on both entire original target charts, using actual finite
preimages and the injective section maps supplied by dominance. -/
theorem map_flat : Flat ThreeProjectiveJMap318.map := by
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P:=@Flat)
  intro p
  obtain ⟨i,q,hq⟩ := ThreeProjectiveJMap318.sourceCover.exists_eq p
  have hp : p ∈ (JLineAtlas318.chart ℚ i).opensRange := ⟨q,hq⟩
  letI : Nonempty (JLineAtlas318.chart ℚ i).opensRange := ⟨⟨p,hp⟩⟩
  refine ⟨(JLineAtlas318.chart ℚ i).opensRange,hp,?_⟩
  exact DedekindAffineFlat318.restrict_chart_flat ThreeProjectiveJMap318.map
    (CommRingCat.of (Polynomial ℚ)) (JLineAtlas318.chart ℚ i)
local instance : Flat ThreeProjectiveJMap318.map := map_flat

/-- Rank four at every target scheme point, including both exceptional
elliptic values and infinity. The generic scalar action is the actual j pullback. -/
theorem rank_four (y : ProjectiveJLine318.scheme ℚ) : ThreeProjectiveJMap318.map.finrank y=4 := by
  rw [FiniteFlatGenericRank318.finrank_eq_generic_degree]
  exact ThreeJActualGenericDegree318.actual_generic_degree_four

theorem finite_flat_surjective_rank_four :
    IsFinite ThreeProjectiveJMap318.map ∧ Flat ThreeProjectiveJMap318.map ∧
      Surjective ThreeProjectiveJMap318.map ∧
      ∀ y : ProjectiveJLine318.scheme ℚ, ThreeProjectiveJMap318.map.finrank y=4 :=
  ⟨ThreeJGlobalFinite318.map_finite,map_flat,ThreeJActualDominance318.map_surjective,rank_four⟩

end ThreeJFiniteFlatRank318
