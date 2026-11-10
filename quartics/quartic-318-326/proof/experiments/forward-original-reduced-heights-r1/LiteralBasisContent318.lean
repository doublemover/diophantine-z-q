module
public import LiteralAdjacentNormSlice318
public section
noncomputable section
namespace LiteralBasisContent318
open TernaryQuadraticLineCover318 LiteralAdjacentNormSlice318 LiteralSliceModulus318
open TernaryChartModuli318 TriangularTernaryBasis318
set_option maxHeartbeats 1000000

@[expose] def fieldBasis {F : Type*} [Field F] (q r A D : F) (u : Vector F) : Vector F :=
  (r*u.1,A*r*u.1+q*u.2.1,D*r*u.1+q*r*u.2.2)

/-- Explicit inverse on residue coordinates, not determinant nonvanishing
used as a proxy for an unconstructed inverse. -/
theorem field_basis_surjective {F : Type*} [Field F] (q r A D : F)
    (hq : q≠0) (hr : r≠0) : Function.Surjective (fieldBasis q r A D) := by
  intro v
  refine ⟨(v.1/r,(v.2.1-A*v.1)/q,(v.2.2-D*v.1)/(q*r)),?_⟩
  apply Prod.ext
  · dsimp [fieldBasis]
    field_simp [hq,hr]
  · apply Prod.ext <;> dsimp [fieldBasis] <;> field_simp [hq,hr] <;> ring

/-- K has an actual nonzero residue value whenever t is a unit. This also
covers t=-2, where its constant term vanishes: use the explicit x=1 point. -/
theorem K_nonzero_value {F : Type*} [Field F] (κ t : F) (ht : t≠0) :
    ∃ v : Vector F, K κ t v≠0 := by
  by_cases ht2 : t+2=0
  · refine ⟨(1,0,0),?_⟩
    have he : K κ t (1,0,0)=(t*(t+2))^2+t^2 := by dsimp [K]; ring
    rw [he,ht2,mul_zero,zero_pow (by decide : 2≠0),zero_add]
    exact pow_ne_zero 2 ht
  · refine ⟨(0,0,0),?_⟩
    have he : K κ t (0,0,0)=t^2*(t+2)^2 := by dsimp [K]; ring
    rw [he]
    exact mul_ne_zero (pow_ne_zero 2 ht) (pow_ne_zero 2 ht2)

lemma reduce_basis (p : ℕ) [Fact p.Prime] (q r A D : ℤ) (u : Vector ℤ) :
    TernaryCongruenceLattices318.reduce p (basisMap q r A D u)=
      fieldBasis (q:ZMod p) (r:ZMod p) (A:ZMod p) (D:ZMod p)
        (TernaryCongruenceLattices318.reduce p u) := by
  apply Prod.ext
  · simp [TernaryCongruenceLattices318.reduce,basisMap,fieldBasis]
  · apply Prod.ext <;> simp [TernaryCongruenceLattices318.reduce,basisMap,fieldBasis]

lemma K_cast (p : ℕ) (κ t : ℤ) (v : Vector ℤ) :
    (K κ t v:ZMod p)=K (κ:ZMod p) (t:ZMod p) (TernaryCongruenceLattices318.reduce p v) := by
  simp [K,TernaryCongruenceLattices318.reduce]

/-- Surjectivity of the ACTUAL integer basis after reduction at a prime
outside the original t. The constructed product q*r divides t. -/
theorem actual_basis_surjective (p : ℕ) [Fact p.Prime] (κ t : ℤ)
    (ht : ¬(p:ℤ)∣t)
    (s : ∀ i : PrimeIndex κ t, Option (ZMod (prime κ t i))) (A D : ℤ) :
    Function.Surjective (fun u : Vector ℤ =>
      TernaryCongruenceLattices318.reduce p
        (basisMap (finiteModulus (prime κ t) s:ℤ) (infinityModulus (prime κ t) s:ℤ) A D u)) := by
  let q := finiteModulus (prime κ t) s
  let r := infinityModulus (prime κ t) s
  have hqr : q*r=modulus κ t := moduli_product (prime κ t) s
  have hM : ¬(p:ℤ)∣(modulus κ t:ℤ) := fun hh => ht (dvd_trans hh (modulus_divides_label κ t))
  have hM' : (modulus κ t:ZMod p)≠0 := by
    intro hh
    exact hM ((ZMod.intCast_zmod_eq_zero_iff_dvd (modulus κ t:ℤ) p).mp (by simpa only [Int.cast_natCast] using hh))
  have hqr' : (q:ZMod p)*(r:ZMod p)=(modulus κ t:ZMod p) := by rw [←Nat.cast_mul,hqr]
  have hq : (q:ZMod p)≠0 := by
    intro hh
    rw [hh,zero_mul] at hqr'
    exact hM' hqr'.symm
  have hr : (r:ZMod p)≠0 := by
    intro hh
    rw [hh,mul_zero] at hqr'
    exact hM' hqr'.symm
  intro y
  obtain ⟨z,hz⟩ := field_basis_surjective (q:ZMod p) (r:ZMod p) (A:ZMod p) (D:ZMod p) hq hr y
  obtain ⟨u,hu⟩ := TernaryCongruenceLattices318.reduce_surjective p z
  refine ⟨u,?_⟩
  rw [reduce_basis,hu]
  simpa only [Int.cast_natCast] using hz

/-- Explicit integer evaluation witnessing that the actual substituted K
has no content prime outside t. No generic lattice is substituted here. -/
theorem actual_basis_nonzero_value (p : ℕ) [Fact p.Prime] (κ t : ℤ)
    (ht : ¬(p:ℤ)∣t)
    (s : ∀ i : PrimeIndex κ t, Option (ZMod (prime κ t i))) (A D : ℤ) :
    ∃ u : Vector ℤ, ¬(p:ℤ)∣K κ t
      (basisMap (finiteModulus (prime κ t) s:ℤ) (infinityModulus (prime κ t) s:ℤ) A D u) := by
  have ht' : (t:ZMod p)≠0 := by
    intro hh
    exact ht ((ZMod.intCast_zmod_eq_zero_iff_dvd t p).mp hh)
  obtain ⟨y,hy⟩ := K_nonzero_value (κ:ZMod p) (t:ZMod p) ht'
  obtain ⟨u,hu⟩ := actual_basis_surjective p κ t ht s A D y
  refine ⟨u,?_⟩
  intro hd
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hd
  rw [K_cast,hu] at hz
  exact hy hz

end LiteralBasisContent318
