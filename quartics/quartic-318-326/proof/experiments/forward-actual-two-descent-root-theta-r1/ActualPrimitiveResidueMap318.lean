module
public import FiniteWeightedResidueDiscrepancy318
public section
noncomputable section
namespace ActualPrimitiveResidueMap318
open scoped BigOperators
open QuadricCRTAssembly318 PrimitiveSieveCRT318 OriginalSieveCRTProduct318
set_option maxHeartbeats 18000000
variable {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J]

/-- Literal coefficient-wise reduction on the ORIGINAL integer quadric. -/
@[expose] def reduction (κ : ℤ) (p : ℕ) (v : Quadric κ) : Quadric (κ : ZMod p) :=
  ⟨mapCoordinates (Int.castRingHom (ZMod p)) v.1,by
    rw [←map_intCast (Int.castRingHom (ZMod p)) κ,equation_map,v.2,map_zero]⟩

@[expose] def PrimitiveAt (p : ι → ℕ) (κ : ℤ) (v : Quadric κ) : Prop :=
  ∀ i,reduction κ (p i) v≠origin (κ : ZMod (p i))
@[expose] def Residues (p : ι → ℕ) (κ : ℤ) :=
  ∀ i,{z : Quadric (κ : ZMod (p i)) // z≠origin (κ : ZMod (p i))}
@[expose] def residueMap (p : ι → ℕ) (κ : ℤ) (v : {v : Quadric κ // PrimitiveAt p κ v}) :
    Residues p κ := fun i => ⟨reduction κ (p i) v.1,v.2 i⟩
@[expose] def Bad (p : ι → ℕ) (κ : ℤ) (γ : J → ℤ) (r : Residues p κ) : Prop :=
  ∀ i,∃ j,(r i).1.1.1.1^2+(r i).1.1.1.2^2+(γ j:ZMod (p i))*(r i).1.1.2.2^2=0

/-- The product of NONZERO original residues is exactly the original
single-modulus primitive CRT space, not a replacement lattice. -/
@[expose] def primitiveEquiv (p : ι → ℕ) (hp : ∀i,(p i).Prime) (hd : Function.Injective p)
    (κ : ℤ) : Primitive p hp hd κ ≃ Residues p κ :=
  admissibleEquiv p hp hd κ (fun i => {z | z≠origin (κ : ZMod (p i))})

@[expose] def badEquiv (p : ι → ℕ) (hp : ∀i,(p i).Prime) (hd : Function.Injective p)
    (κ : ℤ) (γ : J → ℤ) :
    {r : Residues p κ // Bad p κ γ r} ≃ SimultaneousBad p hp hd κ γ := by
  let e : {r : Residues p κ // Bad p κ γ r} ≃
      (∀i,badSet (κ : ZMod (p i)) (fun j => (γ j:ZMod (p i)))) := {
    toFun := fun r i => ⟨(r.1 i).1,⟨(r.1 i).2,r.2 i⟩⟩
    invFun := fun r => ⟨fun i => ⟨(r i).1,(r i).2.1⟩,fun i => (r i).2.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  exact e.trans (admissibleEquiv p hp hd κ
    (fun i => badSet (κ : ZMod (p i)) (fun j => (γ j:ZMod (p i))))).symm

/-- Exact local density on the very residues produced by the original
integer reduction map. Primitive at EACH selected prime is essential. -/
theorem actual_residue_density (p : ι → ℕ) (hp : ∀i,(p i).Prime)
    (hd : Function.Injective p) (κ : ℤ) (hp2 : ∀i,p i≠2) (hκ : ∀i,¬(p i:ℤ)∣κ)
    (γ : J → ℤ) (j₀ : J) :
    (Nat.card {r : Residues p κ // Bad p κ γ r}:ℝ)/(Nat.card (Residues p κ):ℝ)=
      ∏ i,(densityAt (p i) (hp i) κ γ j₀:ℝ) := by
  have hh := simultaneous_density p hp hd κ hp2 hκ γ j₀
  rw [←Nat.card_congr (badEquiv p hp hd κ γ),Nat.card_congr (primitiveEquiv p hp hd κ)] at hh
  exact_mod_cast hh

/-- Divisibility of the ORIGINAL integer prime-form product is exactly
vanishing of one original form at the actual prime reduction. -/
lemma original_prime_key (κ : ℤ) (γ : J → ℤ) (p : ℕ) (hp : p.Prime) (v : Quadric κ) :
    p∣OriginalWeightedSelberg318.key κ γ v ↔
      ∃j,(reduction κ p v).1.1.1^2+(reduction κ p v).1.1.2^2+
        (γ j:ZMod p)*(reduction κ p v).1.2.2^2=0 := by
  rw [OriginalWeightedSelberg318.key,hp.prime.dvd_finsetProd_iff]
  simp only [Finset.mem_univ,true_and]
  apply exists_congr
  intro j
  rw [←Int.natCast_dvd_natCast,Int.dvd_natAbs]
  rw [←ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [OriginalWeightedSelberg318.form,reduction,mapCoordinates,Int.cast_add,Int.cast_pow,Int.cast_mul]

/-- Actual imprimitive reductions are exactly simultaneous divisibility
of all FIVE original integer coordinates; no nonzero-vector convention
or alternative source model is hidden in the correction. -/
lemma reduction_eq_origin_iff (κ : ℤ) (p : ℕ) (v : Quadric κ) :
    reduction κ p v=origin (κ : ZMod p) ↔
      ((p:ℤ)∣v.1.1.1 ∧ (p:ℤ)∣v.1.1.2) ∧
      ((p:ℤ)∣v.1.2.1.1 ∧ (p:ℤ)∣v.1.2.1.2) ∧ (p:ℤ)∣v.1.2.2 := by
  simp only [reduction,origin,Subtype.mk.injEq,mapCoordinates,Prod.mk.injEq,
    Int.castRingHom_apply,ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- The same reduction test at ALL original primes is equivalent to
divisibility by their actual squarefree product, including the empty set. -/
lemma original_product_key (p : ι → ℕ) (hp : ∀i,(p i).Prime) (hd : Function.Injective p)
    (κ : ℤ) (γ : J → ℤ) (v : {v : Quadric κ // PrimitiveAt p κ v}) :
    (∏i,p i)∣OriginalWeightedSelberg318.key κ γ v.1 ↔
      Bad p κ γ (residueMap p κ v) := by
  have he : (∏i,p i)∣OriginalWeightedSelberg318.key κ γ v.1 ↔
      ∀i,p i∣OriginalWeightedSelberg318.key κ γ v.1 := by
    constructor
    · intro h i
      exact (Finset.dvd_prod_of_mem p (Finset.mem_univ i)).trans h
    · intro h
      have hc : Pairwise (fun i j => IsCoprime (p i:ℤ) (p j:ℤ)) := by
        intro i j hij
        apply Int.isCoprime_iff_nat_coprime.mpr
        simpa only [Int.natAbs_natCast] using
          (Nat.coprime_primes (hp i) (hp j)).mpr (fun he => hij (hd he))
      have hh := Fintype.prod_dvd_of_coprime hc
        (fun i => Int.natCast_dvd_natCast.mpr (h i))
      exact_mod_cast hh
  rw [he]
  apply forall_congr'
  intro i
  exact original_prime_key κ γ (p i) (hp i) v.1

/-- A finite product of actual distinct local densities is exactly the
original multiplicative nu at the SAME integer modulus. -/
lemma original_product_density (p : ι → ℕ) (hp : ∀i,(p i).Prime)
    (hd : Function.Injective p) (κ : ℤ) (γ : J → ℤ) (j₀ : J) :
    ActualSieveMultiplicativeDensity318.nu κ γ j₀ (∏i,p i)=
      ∏i,(densityAt (p i) (hp i) κ γ j₀:ℝ) := by
  have hc : (↑(Finset.univ : Finset ι) : Set ι).Pairwise
      (fun i j => Nat.Coprime (p i) (p j)) := by
    intro i _ j _ hij
    exact (Nat.coprime_primes (hp i) (hp j)).mpr (fun he => hij (hd he))
  rw [(ActualSieveMultiplicativeDensity318.nu_multiplicative κ γ j₀).map_prod _ _ hc]
  apply Finset.prod_congr rfl
  intro i _
  exact ActualSieveMultiplicativeDensity318.nu_at_prime κ γ j₀ (p i) (hp i)

@[expose] def residueFintype (p : ι → ℕ) (hp : ∀i,(p i).Prime) (κ : ℤ) :
    Fintype (Residues p κ) := by
  classical
  letI : ∀i,NeZero (p i) := fun i => ⟨(hp i).ne_zero⟩
  unfold Residues Quadric Coordinates
  infer_instance

end ActualPrimitiveResidueMap318
