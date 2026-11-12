module
public import AnchorLocalSquareProduction318
public section
noncomputable section
namespace ActualLocalAnchorWitness318
open FixedDetectorScales318 PreparedAnchorLabels318
set_option maxHeartbeats 1000000
local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

lemma scaled_square {F : Type*} [Field F] (S T r : F)
    (ht : T=S*r) (hs : IsSquare (3*r^2-2)) : ∃ x : F, x^2=3*T^2-2*S^2 := by
  obtain ⟨z,hz⟩ := hs
  refine ⟨S*z,?_⟩
  rw [ht]
  linear_combination -S^2*hz

lemma physical_square (p : ℕ) [Fact p.Prime] (ns : Fin 4 → ℤ) (N : ℕ)
    (hs : IsSquare ((3*(ActualAnchorRatio318.ratio ns N)^2-2:ℚ):ℚ_[p])) :
    ∃ x : ℚ_[p], x^2=
      3*(4096*(normProduct ns:ℚ_[p])*(3:ℚ_[p])^N+
        (ActualScalarRoot318.inverseNorm (ns 1):ℚ_[p]))^2-2*((3:ℚ_[p])^N)^2 := by
  have he := congrArg (Rat.castHom ℚ_[p]) (ActualAnchorRatio318.physical_identity ns N)
  simp only [map_add,map_mul,map_pow,map_ofNat] at he
  apply scaled_square ((3:ℚ_[p])^N) _ (ActualAnchorRatio318.ratio ns N:ℚ_[p]) he
  simpa only [Rat.cast_sub,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat] using hs

/-- Both exceptional local physical-anchor witnesses are actually produced
on the same fixed arithmetic labels. The rational Hasse–Minkowski/global
representation step is not assumed or inferred by this theorem. -/
theorem actual_local_anchors (a : ℤ) (A B N d : ℕ) (hd : d≠0) :
    let ns := FixedArithmeticLabels318.labels a A B (multiplier N d) (multiplier_ne N d hd)
    (∃ x : ℚ_[2], x^2=
      3*(4096*(normProduct ns:ℚ_[2])*(3:ℚ_[2])^N+
        (ActualScalarRoot318.inverseNorm (ns 1):ℚ_[2]))^2-2*((3:ℚ_[2])^N)^2) ∧
    (∃ x : ℚ_[3], x^2=
      3*(4096*(normProduct ns:ℚ_[3])*(3:ℚ_[3])^N+
        (ActualScalarRoot318.inverseNorm (ns 1):ℚ_[3]))^2-2*((3:ℚ_[3])^N)^2) := by
  dsimp only
  obtain ⟨hr,h2,h3⟩ := actual_anchor_depths a A B N d hd
  exact ⟨physical_square 2 _ N (AnchorLocalSquareProduction318.at_two _ hr h2),
    physical_square 3 _ N (AnchorLocalSquareProduction318.at_three _ h3)⟩

end ActualLocalAnchorWitness318
