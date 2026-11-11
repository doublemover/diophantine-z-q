module
public import PELOriginalTorsionRepresentatives318
public import Mathlib.Data.Int.DivMod
public section
noncomputable section
namespace PELOriginalTorsionEnumeration318
open QuaternionicRealPeriod318 PELOriginalPeriodLattice318 PELComplexPeriodSurface318
open DiscreteComplexPeriodAtlas318 PELOriginalPeriodIntegerCoordinates318
open PELOriginalTorsionRepresentatives318
variable (τ : ℂ) (hτ : 0 < τ.im) (n : ℕ) (hn : 0<n)
@[expose] def residues (x : Fin 4 → ℤ) : Labels n := fun i =>
  ⟨(x i % (n : ℤ)).toNat,by
    have h0 := Int.emod_nonneg (x i) (show (n : ℤ)≠0 by exact_mod_cast hn.ne')
    have h1 := Int.emod_lt_of_pos (x i) (show (0 : ℤ)<n by exact_mod_cast hn)
    omega⟩
lemma residue_value (x : Fin 4 → ℤ) (i : Fin 4) :
    (((residues n hn x i).val : ℤ))=x i%(n : ℤ) :=
  Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hn.ne'))

/-- Every original torsion point has one of the actual n^4 lattice
representatives. The reduction is performed in the exact original
integral order coordinates, not in a replacement abstract torus. -/
lemma point_surjective : Function.Surjective (point τ hτ n hn) := by
  intro q
  obtain ⟨z,hz⟩ := (QuotientAddGroup.mk'_surjective (Periods τ)) q.val
  have hperiod : n • z∈Periods τ := by
    apply (QuotientAddGroup.eq_zero_iff _).mp
    rw [map_nsmul,hz]
    exact q.property
  obtain ⟨x,hx⟩ := (mem_iff τ hτ _).mp hperiod
  let a := residues n hn x
  let k : Fin 4 → ℤ := fun i => x i/(n : ℤ)
  have hnR : (n : ℝ)≠0 := by exact_mod_cast hn.ne'
  have hd : (fun i : Fin 4 => (x i : ℝ))=
      (fun i => ((a i).val : ℝ))+(n : ℝ) • (fun i => (k i : ℝ)) := by
    funext i
    change (x i : ℝ)=((a i).val : ℝ)+(n : ℝ)*(k i : ℝ)
    have h := Int.emod_add_mul_ediv (x i) (n : ℤ)
    rw [←residue_value n hn x i] at h
    exact_mod_cast h.symm
  have hv : z=vector τ hτ n a+coordinates τ hτ (fun i => (k i : ℝ)) := by
    have hm : (n : ℝ) • z=(n : ℝ) •
        (vector τ hτ n a+coordinates τ hτ (fun i => (k i : ℝ))) := by
      have hmult : (n : ℝ) • vector τ hτ n a=
          coordinates τ hτ (fun i => ((a i).val : ℝ)) := by
        simpa only [Nat.cast_smul_eq_nsmul ℝ] using multiple_vector τ hτ n hn a
      calc
        _ = coordinates τ hτ (fun i => (x i : ℝ)) := by
          rw [Nat.cast_smul_eq_nsmul ℝ,hx]
        _ = coordinates τ hτ (fun i => ((a i).val : ℝ))+
            (n : ℝ) • coordinates τ hτ (fun i => (k i : ℝ)) := by rw [hd,map_add,map_smul]
        _ = _ := by rw [smul_add,hmult]
    have hc := congrArg (fun w : ComplexVectors => (n : ℝ)⁻¹ • w) hm
    simpa only [smul_smul,inv_mul_cancel₀ hnR,one_smul] using hc
  refine ⟨a,?_⟩
  apply Subtype.ext
  change (QuotientAddGroup.mk' (Periods τ)) (vector τ hτ n a)=q.val
  rw [←hz,hv,map_add]
  have hk : (QuotientAddGroup.mk' (Periods τ)) (coordinates τ hτ (fun i => (k i : ℝ)))=0 :=
    (QuotientAddGroup.eq_zero_iff _).mpr (coordinates_mem τ hτ k)
  rw [hk,add_zero]

@[expose] def equivalence : Labels n ≃ {q : Surface τ // n • q=0} :=
  Equiv.ofBijective (point τ hτ n hn)
    ⟨point_injective τ hτ n hn,point_surjective τ hτ n hn⟩
include hτ hn in
lemma finite : Finite {q : Surface τ // n • q=0} :=
  Finite.of_equiv (Labels n) (equivalence τ hτ n hn)
include hτ hn in
lemma cardinality : Nat.card {q : Surface τ // n • q=0}=n^4 := by
  rw [←Nat.card_congr (equivalence τ hτ n hn)]
  simp only [Labels,Nat.card_eq_fintype_card,Fintype.card_fun,Fintype.card_fin]
end PELOriginalTorsionEnumeration318
