module
public import ActualTwoDescentContinuousHOneEmbedding318
public section
noncomputable section
namespace ActualTwoDescentSelmerInActualHOne318
set_option maxHeartbeats 16000000

open ActualTwoDescentContinuousHOneEmbedding318 ActualTwoDescentCohomologicalSelmer318
open ActualTwoDescentFieldActualGaloisCohomology318

/-- The actual Selmer subgroup inside ACTUAL H1, restricted to locally constant representatives. -/
def actualHOneSelmer (n : ℚ) (hn : n ≠ 0) : Subgroup (Multiplicative (groupCohomology.H1 (actualTwoTorsionRep n))) :=
  (cohomologicalSelmer n hn).map (continuousHOneMap n)

def selmerActualHOneEquiv (n : ℚ) (hn : n ≠ 0) : cohomologicalSelmer n hn ≃* actualHOneSelmer n hn :=
  MulEquiv.ofBijective
    { toFun := fun χ => ⟨continuousHOneMap n χ,⟨χ,χ.property,rfl⟩⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun χ ψ => Subtype.ext (map_mul _ χ ψ) }
    ⟨fun χ ψ h => Subtype.ext (actual_continuous_hone_injective n (congrArg Subtype.val h)),by
      rintro ⟨z,χ,hχ,hz⟩
      exact ⟨⟨χ,hχ⟩,Subtype.ext hz⟩⟩

lemma actual_hone_selmer_card (n : ℚ) (hn : n ≠ 0) :
    Nat.card (actualHOneSelmer n hn)=Nat.card (cohomologicalSelmer n hn) :=
  (Nat.card_congr (selmerActualHOneEquiv n hn).toEquiv).symm

end ActualTwoDescentSelmerInActualHOne318
