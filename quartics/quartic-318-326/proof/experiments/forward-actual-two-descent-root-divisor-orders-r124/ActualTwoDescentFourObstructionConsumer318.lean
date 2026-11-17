module
public import ActualTwoDescentRationalPointObstruction318
public section
noncomputable section
namespace ActualTwoDescentFourObstructionConsumer318
set_option maxHeartbeats 16000000

open ActualTwoDescentTorsionKummerValues318 ActualTwoDescentEightClassCube318
open ActualTwoDescentPointExtraction318 ActualTwoDescentAllPlacesIntersection318
open ActualTwoDescentConcreteLocalObstruction318 ActualTwoDescentBetaObstructionConsumer318

/-- The all-place obstruction is retained for each of the two actual twists at
all four fixed poles. A new source index cannot be selected by this consumer. -/
theorem actual_four_realizations_of_obstruction (b β θ c d n : Fin 4 → ℚ)
    (hβ : ∀ i, β i ≠ 0) (hn : ∀ i, n i ≠ 0) (hnθ : ∀ i, n i*θ i ≠ 0)
    (hc : ∀ i, c i ≠ 0) (hd : ∀ i, d i ≠ 0)
    (hB : ∀ i, 17*b i=β i*(c i)^2)
    (hV : ∀ i, (17*b i)^2*(1-b i/17)=θ i*(d i)^2)
    (hi : ∀ i, Function.Injective (cubeClass (n i) (β i) (hn i) (hβ i)))
    (hiθ : ∀ i, Function.Injective (cubeClass (n i*θ i) (β i) (hnθ i) (hβ i)))
    (hloc : ∀ i, retainedBetaClass (β i) (hβ i) ∈ allPlacesImage (n i) (hn i))
    (hlocθ : ∀ i, retainedBetaClass (β i) (hβ i) ∈ allPlacesImage (n i*θ i) (hnθ i))
    (hobs : ∀ i, (QuotientGroup.mk ⟨retainedBetaClass (β i) (hβ i),hloc i⟩ :
      LocalObstruction (n i) (hn i))=1)
    (hobsθ : ∀ i, (QuotientGroup.mk ⟨retainedBetaClass (β i) (hβ i),hlocθ i⟩ :
      LocalObstruction (n i*θ i) (hnθ i))=1) :
    Nonempty (∀ i, TwoTwistPointRealization318.Realization (b i)) := by
  have hP : ∀ i, Nonempty (KummerPoint (β i) (n i)) := fun i =>
    actual_beta_point_of_obstruction_vanishes (n i) (β i) (hn i) (hβ i) (hi i) (hloc i) (hobs i)
  have hQ : ∀ i, Nonempty (KummerPoint (β i) (n i*θ i)) := fun i =>
    actual_beta_point_of_obstruction_vanishes (n i*θ i) (β i) (hnθ i) (hβ i) (hiθ i) (hlocθ i) (hobsθ i)
  exact ⟨actual_four_realizations b β θ c d n hβ hc hd hB hV
    (fun i => Classical.choice (hP i)) (fun i => Classical.choice (hQ i))⟩

end ActualTwoDescentFourObstructionConsumer318
