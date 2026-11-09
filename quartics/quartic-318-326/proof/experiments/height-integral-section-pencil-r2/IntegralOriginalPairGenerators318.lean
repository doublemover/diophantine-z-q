module
public import IntegralScaledCoefficientUnits318
public section
noncomputable section
namespace IntegralOriginalPairGenerators318
open AlgebraicGeometry CategoryTheory Opposite
open IntegralGluedModel318 IntegralGluedDifferentialFrames318 IntegralGlobalBicanonicalPair318
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)
variable (hN : IsUnit (IntegralBranchDenominatorCover318.separationInteger:R))

theorem branch_generator (i : Fin 4) (V : (scheme R c).Opens)
    (hV : V≤branchEmbedding R c i ''ᵁ ⊤) :
    Function.Bijective (fun a : Γ(scheme R c,V) => a •
      (tensor R c).presheaf.map (homOfLE hV).op (branchQ R c i 0)) :=
  IntrinsicTensorGenerator318.weighted_generator_bijective
    (R:=R) (S:=IntegralBranchCoordinates318.B R c i)
    (branchEmbedding R c i) (structureMap R c) (branch_structure R c i)
    (IntegralBranchLocalization318.sourceFrame R c i (IntegralSmoothProperBicanonical318.two_unit R hN))
    (IntegralBranchCoordinates318.sourceCoordinate R c i) (branchCoefficient R c i 0)
    (IntegralBranchCoordinates318.source_normalized R c i (IntegralSmoothProperBicanonical318.two_unit R hN))
    (IntegralScaledCoefficientUnits318.branch_zero_unit R c hN i) V hV

theorem infinity_generator (V : (scheme R c).Opens)
    (hV : V≤infinityChart R c ''ᵁ ⊤) :
    Function.Bijective (fun a : Γ(scheme R c,V) => a •
      (tensor R c).presheaf.map (homOfLE hV).op (infinityQ R c 1)) :=
  IntrinsicTensorGenerator318.weighted_generator_bijective
    (R:=R) (S:=IntegralInfinityChart318.Order R c)
    (infinityChart R c) (structureMap R c) (infinityChart_structure R c)
    (IntegralInfinityChart318.frame R c (IntegralSmoothProperBicanonical318.two_unit R hN))
    (IntegralInfinityChart318.coordinate R c) (infinityCoefficient R c 1)
    (IntegralInfinityChart318.frame_D R c (IntegralSmoothProperBicanonical318.two_unit R hN))
    (IntegralScaledCoefficientUnits318.infinity_one_unit R c hN) V hV

/-- Restriction from the actual global q pair agrees on every subopen with
the original local tensor section, through the actual composed sheaf maps. -/
theorem q_restrict_subopen (n : Fin 2) (i : Option (Fin 4))
    (V : (scheme R c).Opens) (hV : V≤opens R c i) :
    (tensor R c).presheaf.map (homOfLE (show V≤⊤ from le_top)).op (q R c hN n)=
      (tensor R c).presheaf.map (homOfLE hV).op (localQ R c n i) := by
  have h := congrArg (fun f => f (q R c hN n))
    ((tensor R c).presheaf.map_comp
      (homOfLE (show opens R c i≤⊤ from le_top)).op (homOfLE hV).op)
  exact h.trans (congrArg ((tensor R c).presheaf.map (homOfLE hV).op)
    (q_restrict R c hN n i))

theorem global_branch_generator (i : Fin 4) (V : (scheme R c).Opens)
    (hV : V≤opens R c (some i)) :
    Function.Bijective (fun a : Γ(scheme R c,V) => a •
      (tensor R c).presheaf.map (homOfLE (show V≤⊤ from le_top)).op (q R c hN 0)) := by
  rw [q_restrict_subopen R c hN 0 (some i) V hV]
  exact branch_generator R c hN i V hV

theorem global_infinity_generator (V : (scheme R c).Opens)
    (hV : V≤opens R c none) :
    Function.Bijective (fun a : Γ(scheme R c,V) => a •
      (tensor R c).presheaf.map (homOfLE (show V≤⊤ from le_top)).op (q R c hN 1)) := by
  rw [q_restrict_subopen R c hN 1 none V hV]
  exact infinity_generator R c hN V hV
end IntegralOriginalPairGenerators318
