module
public import ActualGaussianReducedResidues318
public section
noncomputable section
namespace ActualGaussianIntegerFibers318
open TernaryQuadraticLineCover318 TernaryCongruenceLattices318 LiteralAdjacentNormSlice318
open OriginalWholeBasisCoordinates318 OriginalReducedResidueBounds318
open OriginalAnisotropicResidueFibers318 ActualGaussianChartObstruction318 ActualGaussianReducedResidues318
set_option maxHeartbeats 6500000

@[expose] def integerActual (side : Bool) (κ t : ℤ) (u v z c : Vector ℤ) (p : ℕ) : Prop :=
  Obstruction side κ t (synthesis u v z c) p

lemma reduction (side : Bool) (κ t : ℤ) (u v z c : Vector ℤ)
    (p : ℕ) [Fact p.Prime] :
    integerActual side κ t u v z c p ↔ reduce p c∈
      (if side then reducedActual p κ t u v z else reducedFirst p κ t u v z) := by
  cases side
  · exact (first_abstract_iff κ t (synthesis u v z c) p).trans
      (OriginalSmallPrimeRectangleTail318.obstruction_reduction false κ t u v z c p)
  · have hP : (P' κ t (synthesis u v z c):ZMod p)=P' (κ:ZMod p) (t:ZMod p)
        (fieldSynthesis (reduce p u) (reduce p v) (reduce p z) (reduce p c)) := by
      rw [←reduction_synthesis]
      simp [P',reduce]
    have hK : (K κ t (synthesis u v z c):ZMod p)=K (κ:ZMod p) (t:ZMod p)
        (fieldSynthesis (reduce p u) (reduce p v) (reduce p z) (reduce p c)) := by
      rw [←reduction_synthesis]
      simp [K,reduce]
    simp only [integerActual,Obstruction,ite_true,reducedActual,
      Finset.mem_filter,Finset.mem_univ,true_and,←ZMod.intCast_zmod_eq_zero_iff_dvd,hP,hK]

lemma actual_card (side : Bool) (κ t : ℤ) (u v z : Vector ℤ)
    (p : ℕ) [Fact p.Prime] (A B C : ℕ) :
    Nat.card {c : Rectangle A B C // integerActual side κ t u v z (coordinates c) p}=
      Nat.card (ResidueRectangle A B C p
        (if side then reducedActual p κ t u v z else reducedFirst p κ t u v z)) := by
  let e : {c : Rectangle A B C // integerActual side κ t u v z (coordinates c) p} ≃
      ResidueRectangle A B C p
        (if side then reducedActual p κ t u v z else reducedFirst p κ t u v z) :=
    { toFun := fun c => ⟨c.1,(reduction side κ t u v z (coordinates c.1) p).mp c.2⟩
      invFun := fun c => ⟨c.1,(reduction side κ t u v z (coordinates c.1) p).mpr c.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Nat.card_congr e

/-- Actual integer fibers for both original Gaussian charts, retaining
all anisotropic floors and boundary terms and every t+2 prime. -/
theorem rectangle_bound (side : Bool) (κ t : ℤ)
    (s : ∀ i : LiteralSliceModulus318.PrimeIndex κ t,
      Option (ZMod (LiteralSliceModulus318.prime κ t i)))
    (u v z : Vector ℤ)
    (hb : OriginalControlledIntegralBasis318.IntegralBasisTriple
      (LiteralSliceModulus318.prime κ t) κ s u v z)
    (p : ℕ) [Fact p.Prime] (hκ : ¬(p:ℤ)∣κ) (ht : ¬(p:ℤ)∣t) (A B C : ℕ) :
    Nat.card {c : Rectangle A B C // integerActual side κ t u v z (coordinates c) p}≤
      8*p*(2*A/p+1)*(2*B/p+1)*(2*C/p+1) := by
  rw [actual_card]
  have hc : (if side then reducedActual p κ t u v z else reducedFirst p κ t u v z).card≤8*p := by
    cases side
    · exact (original_slice_residue_bounds κ t s u v z hb p hκ ht).1
    · exact original_label_basis_bound κ t s u v z hb p hκ ht
  exact (rectangle_residue_count A B C p (Fact.out : p.Prime).pos _).trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hc)))

end ActualGaussianIntegerFibers318
