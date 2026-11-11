module
public import OriginalGoodMinimumConsumer318
public section
noncomputable section
namespace OriginalReducedBasisResidues318
open TernaryQuadraticLineCover318 LiteralTernaryReduction318 OriginalEuclideanLattice318
open OriginalControlledIntegralBasis318 OriginalWholeBasisCoordinates318
open TernaryCongruenceLattices318
set_option maxHeartbeats 3000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Residue surjectivity of the ACTUAL reduced whole-basis map away from
its original modulus. The proof constructs a preimage using modulus
axes and whole integer spanning; it does not assume a matrix inverse. -/
theorem residue_surjective (q : ι → ℕ) (κ : ℤ) (s : ∀ i, Option (ZMod (q i)))
    (u v z : Vector ℤ) (hb : IntegralBasisTriple q κ s u v z)
    (p : ℕ) [Fact p.Prime] (hM : ¬(p:ℤ)∣(FixedSquarefreeCRT318.modulus q:ℤ)) :
    Function.Surjective (fun c : Vector ℤ => reduce p (synthesis u v z c)) := by
  let M : ℤ := FixedSquarefreeCRT318.modulus q
  have hMZ : (M:ZMod p)≠0 := by
    intro h
    exact hM ((ZMod.intCast_zmod_eq_zero_iff_dvd M p).mp h)
  intro y
  obtain ⟨x,hx⟩ := reduce_surjective p ((M:ZMod p)⁻¹*y.1,
    (M:ZMod p)⁻¹*y.2.1,(M:ZMod p)⁻¹*y.2.2)
  let b : Vector ℤ := (M*x.1,M*x.2.1,M*x.2.2)
  have hbmem : b∈literalLattice q κ s := modulus_multiple_mem q κ s x
  obtain ⟨a₀,a₁,a₂,ha⟩ := hb.2 b hbmem
  refine ⟨(a₀,a₁,a₂),?_⟩
  change reduce p (a₀ • u+a₁ • v+a₂ • z)=y
  rw [←ha]
  have hx0 := congrArg Prod.fst hx
  have hx1 := congrArg (fun a : Vector (ZMod p) => a.2.1) hx
  have hx2 := congrArg (fun a : Vector (ZMod p) => a.2.2) hx
  change (x.1:ZMod p)=(M:ZMod p)⁻¹*y.1 at hx0
  change (x.2.1:ZMod p)=(M:ZMod p)⁻¹*y.2.1 at hx1
  change (x.2.2:ZMod p)=(M:ZMod p)⁻¹*y.2.2 at hx2
  apply Prod.ext
  · change ((M*x.1:ℤ):ZMod p)=y.1
    rw [Int.cast_mul,hx0,←mul_assoc,mul_inv_cancel₀ hMZ,one_mul]
  · apply Prod.ext
    · change ((M*x.2.1:ℤ):ZMod p)=y.2.1
      rw [Int.cast_mul,hx1,←mul_assoc,mul_inv_cancel₀ hMZ,one_mul]
    · change ((M*x.2.2:ℤ):ZMod p)=y.2.2
      rw [Int.cast_mul,hx2,←mul_assoc,mul_inv_cancel₀ hMZ,one_mul]

/-- Same original slice condition p does not divide label; no new bad
content prime is introduced by replacing triangular with reduced basis. -/
theorem original_slice_residue_surjective (κ label : ℤ)
    (s : ∀ i : LiteralSliceModulus318.PrimeIndex κ label,
      Option (ZMod (LiteralSliceModulus318.prime κ label i)))
    (u v z : Vector ℤ)
    (hb : IntegralBasisTriple (LiteralSliceModulus318.prime κ label) κ s u v z)
    (p : ℕ) [Fact p.Prime] (hp : ¬(p:ℤ)∣label) :
    Function.Surjective (fun c : Vector ℤ => reduce p (synthesis u v z c)) := by
  apply residue_surjective (LiteralSliceModulus318.prime κ label) κ s u v z hb p
  intro h
  exact hp (dvd_trans h (LiteralSliceModulus318.modulus_divides_label κ label))

/-- Any literal residue evaluation witness transports through the actual
reduced coordinates. This is pointwise surjectivity, including every
residue vector, not merely a determinant nonzero assertion. -/
theorem transport_nonzero_value (q : ι → ℕ) (κ : ℤ) (s : ∀ i, Option (ZMod (q i)))
    (u v z : Vector ℤ) (hb : IntegralBasisTriple q κ s u v z)
    (p : ℕ) [Fact p.Prime] (hM : ¬(p:ℤ)∣(FixedSquarefreeCRT318.modulus q:ℤ))
    (F : Vector (ZMod p) → ZMod p) (hF : ∃ y, F y≠0) :
    ∃ c : Vector ℤ, F (reduce p (synthesis u v z c))≠0 := by
  obtain ⟨y,hy⟩ := hF
  obtain ⟨c,hc⟩ := residue_surjective q κ s u v z hb p hM y
  exact ⟨c,by rwa [hc]⟩

end OriginalReducedBasisResidues318
