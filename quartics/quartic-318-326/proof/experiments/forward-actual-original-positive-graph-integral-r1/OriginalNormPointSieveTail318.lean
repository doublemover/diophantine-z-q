module
public import OriginalSieveFrame318
public section
noncomputable section
namespace OriginalNormPointSieveTail318
open TernaryQuadraticLineCover318 LiteralAdjacentNormSlice318
open OriginalAnisotropicRectangle318 OriginalAnisotropicResidueFibers318 OriginalSieveFrame318
open OriginalSmallPrimeRectangleTail318 OriginalReducedRectangleVolume318
set_option maxHeartbeats 4500000

@[expose] def pointObstruction (side : Bool) (κ t : ℤ) (y : Vector ℤ) (p : ℕ) : Prop :=
  (p:ℤ)∣(if side then P' κ t y else P κ t y) ∧ (p:ℤ)∣D t y

/-- Restrict the exact original-point injection to the actual obstruction
union. All multiplicities and all original values are preserved. -/
theorem actual_norm_point_tail (side : Bool) (κ label : ℤ)
    (s : ∀ i : LiteralSliceModulus318.PrimeIndex κ label,
      Option (ZMod (LiteralSliceModulus318.prime κ label i)))
    (d : Frame (LiteralSliceModulus318.prime κ label) κ s)
    (R : ℝ) (hR : 0≤R) (Y : ℕ) (hY : 0<Y) (S : Finset ℕ)
    (hprime : ∀ p∈S, p.Prime) (hκ : ∀ p∈S, ¬(p:ℤ)∣κ)
    (ht : ∀ p∈S, ¬(p:ℤ)∣label) (hcut : ∀ p∈S, Y<p)
    (hsize : ∀ p∈S, p≤d.firstRadius R ∧ p≤d.secondRadius R ∧ p≤d.thirdRadius R) :
    (Nat.card {y : NormPoints (LiteralSliceModulus318.prime κ label) κ s R //
      ∃ p : ↥S, pointObstruction side κ label y.1.1 p.1}:ℝ)*
      (LiteralSliceModulus318.modulus κ label:ℝ)^2*(Y:ℝ)≤110592*R^3 := by
  classical
  obtain ⟨f,hf,he⟩ := norm_rectangle_map (LiteralSliceModulus318.prime_is_prime κ label) d R hR
  let X := {y : NormPoints (LiteralSliceModulus318.prime κ label) κ s R //
    ∃ p : ↥S, pointObstruction side κ label y.1.1 p.1}
  let Z := {c : Rectangle (d.firstRadius R) (d.secondRadius R) (d.thirdRadius R) //
    ∃ p : ↥S, integerObstruction side κ label d.u d.v d.z (coordinates c) p.1}
  let g : X → Z := fun y => ⟨f y.1,by
    obtain ⟨p,hp⟩ := y.2
    refine ⟨p,?_⟩
    simpa only [integerObstruction,he y.1,pointObstruction] using hp⟩
  have hg : Function.Injective g := by
    intro a b hh
    exact Subtype.ext (hf (congrArg Subtype.val hh))
  have hcard : (Nat.card X:ℝ)≤(Nat.card Z:ℝ) := by
    exact_mod_cast Nat.card_le_card_of_injective g hg
  have htail := actual_volume_small_prime_tail side κ label s d.u d.v d.w d.z d.basis
    d.first_second d.second_third d.last_bound R hR Y hY S hprime hκ ht hcut hsize
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcard (sq_nonneg _)) (Nat.cast_nonneg Y)).trans htail

end OriginalNormPointSieveTail318
