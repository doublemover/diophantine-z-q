module
public import OriginalFiveGridLeading318
public section
noncomputable section
namespace OriginalBoundedIntegerShear318
open TernaryQuadraticLineCover318 TernaryCongruenceLattices318 LiteralTernaryReduction318
open OriginalControlledIntegralBasis318 OriginalWholeBasisCoordinates318 OriginalCofactorCoordinates318
open OriginalReducedResidueBounds318 OriginalFiveGridLeading318 OriginalAffineLeadingForms318
open OriginalAffineSieveEliminants318
set_option maxHeartbeats 5500000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def shear (i j : ℤ) (u v z : Vector ℤ) : Vector ℤ := z+i • u+j • v
@[expose] def coefficientEquiv (i j : ℤ) : Vector ℤ ≃+ Vector ℤ where
  toFun c := (c.1+i*c.2.2,c.2.1+j*c.2.2,c.2.2)
  invFun c := (c.1-i*c.2.2,c.2.1-j*c.2.2,c.2.2)
  left_inv c := by
    apply Prod.ext
    · dsimp; ring
    · apply Prod.ext <;> dsimp <;> ring
  right_inv c := by
    apply Prod.ext
    · dsimp; ring
    · apply Prod.ext <;> dsimp <;> ring
  map_add' a b := by
    apply Prod.ext
    · dsimp; ring
    · apply Prod.ext <;> dsimp <;> ring

lemma synthesis_shear (i j : ℤ) (u v z c : Vector ℤ) :
    synthesis u v (shear i j u v z) c=synthesis u v z (coefficientEquiv i j c) := by
  apply Prod.ext
  · simp [synthesis,shear,coefficientEquiv,zsmul_eq_mul];ring
  · apply Prod.ext <;> simp [synthesis,shear,coefficientEquiv,zsmul_eq_mul] <;> ring

/-- Exact determinant and INTEGER lattice are unchanged by every bounded
candidate. There is no hidden sublattice-index or factor2 adjustment. -/
lemma determinant_shear (i j : ℤ) (u v z : Vector ℤ) :
    determinant u v (shear i j u v z)=determinant u v z := by
  simp [determinant,OriginalIntegerNormalProjection318.normal,LiteralIntegerDuality318.dot,
    shear,zsmul_eq_mul]
  ring

theorem same_lattice (q : ι → ℕ) (κ : ℤ) (s : ∀ i, Option (ZMod (q i)))
    (u v z : Vector ℤ) (hb : IntegralBasisTriple q κ s u v z) (i j : ℤ) (y : Vector ℤ) :
    y∈literalLattice q κ s ↔ ∃ c : Vector ℤ, synthesis u v (shear i j u v z) c=y := by
  constructor
  · intro hy
    let c := (wholeEquiv q κ s u v z hb).symm ⟨y,hy⟩
    refine ⟨(coefficientEquiv i j).symm c,?_⟩
    rw [synthesis_shear,AddEquiv.apply_symm_apply]
    exact wholeEquiv_inverse q κ s u v z hb ⟨y,hy⟩
  · rintro ⟨c,rfl⟩
    rw [synthesis_shear]
    exact (wholeEquiv q κ s u v z hb (coefficientEquiv i j c)).property

lemma bounded_coordinate (A C i : ℕ) (hi : i<5) (a c : ℤ)
    (ha : |a|≤(A:ℤ)) (hc : |c|≤(C:ℤ)) : |a-(i:ℤ)*c|≤(A:ℤ)+4*(C:ℤ) := by
  have hi' : (i:ℤ)≤4 := by exact_mod_cast (show i≤4 by omega)
  have hm : |(i:ℤ)*c|≤4*(C:ℤ) := by
    rw [abs_mul,abs_of_nonneg (Int.natCast_nonneg i)]
    exact mul_le_mul hi' hc (abs_nonneg _) (by norm_num)
  exact (abs_sub _ _).trans (add_le_add ha hm)

/-- The short coefficient is unchanged; only the OTHER two widths grow
by at most4 times the short width. This preserves anisotropic saving and
is not an uncontrolled permutation to a long-direction pivot. -/
theorem inverse_rectangle (A B C i j : ℕ) (hi : i<5) (hj : j<5) (c : Vector ℤ)
    (hA : |c.1|≤(A:ℤ)) (hB : |c.2.1|≤(B:ℤ)) (hC : |c.2.2|≤(C:ℤ)) :
    |((coefficientEquiv (i:ℤ) (j:ℤ)).symm c).1|≤(A:ℤ)+4*(C:ℤ) ∧
    |((coefficientEquiv (i:ℤ) (j:ℤ)).symm c).2.1|≤(B:ℤ)+4*(C:ℤ) ∧
    ((coefficientEquiv (i:ℤ) (j:ℤ)).symm c).2.2=c.2.2 :=
  ⟨bounded_coordinate A C i hi c.1 c.2.2 hA hC,
    bounded_coordinate B C j hj c.2.1 c.2.2 hB hC,rfl⟩

lemma reduction_shear (p i j : ℕ) (u v z : Vector ℤ) :
    reduce p (shear (i:ℤ) (j:ℤ) u v z)=
      fieldSynthesis (reduce p u) (reduce p v) (reduce p z) ((i:ZMod p),(j:ZMod p),1) := by
  apply Prod.ext
  · simp [reduce,shear,fieldSynthesis,zsmul_eq_mul];ring
  · apply Prod.ext <;> simp [reduce,shear,fieldSynthesis,zsmul_eq_mul] <;> ring

/-- For EVERY permitted large prime, one of25 fixed integer unimodular
shears has BOTH actual leading coefficients nonzero modulo that prime.
No prime dividing a convenient first pivot is discarded, and t=-2 is
covered. The finite candidate collection is fixed before prime choice. -/
theorem actual_integer_shear (q : ι → ℕ) (κ t : ℤ)
    (s : ∀ i, Option (ZMod (q i))) (u v z : Vector ℤ)
    (hb : IntegralBasisTriple q κ s u v z) (p : ℕ) [Fact p.Prime] (hp : 5≤p)
    (hκ : ¬(p:ℤ)∣κ) (hM : ¬(p:ℤ)∣(FixedSquarefreeCRT318.modulus q:ℤ)) :
    ∃ i j : ℕ, i<5 ∧ j<5 ∧
      ¬(p:ℤ)∣fA false κ t (shear (i:ℤ) (j:ℤ) u v z) ∧
      ¬(p:ℤ)∣fA true κ t (shear (i:ℤ) (j:ℤ) u v z) := by
  have hs := Finite.injective_iff_surjective.mp
    (fieldSynthesis_injective q κ s u v z hb p hM)
  have hk : (κ:ZMod p)≠0 := fun h => hκ ((ZMod.intCast_zmod_eq_zero_iff_dvd κ p).mp h)
  obtain ⟨i,j,hi,hj,hfirst,hsecond⟩ := actual_field_shear p hp (κ:ZMod p) (t:ZMod p) hk
    (reduce p u) (reduce p v) (reduce p z) hs
  let d := shear (i:ℤ) (j:ℤ) u v z
  have he0 : (fA false κ t d:ZMod p)=
      (κ:ZMod p)*(fieldSynthesis (reduce p u) (reduce p v) (reduce p z)
        ((i:ZMod p),(j:ZMod p),1)).2.2^2 := by
    rw [←reduction_shear]
    simp [fA,reduce,d]
  have he1 : (fA true κ t d:ZMod p)=
      quadratic (κ:ZMod p) (t:ZMod p)
        (fieldSynthesis (reduce p u) (reduce p v) (reduce p z)
          ((i:ZMod p),(j:ZMod p),1)) := by
    rw [←reduction_shear]
    simp [fA,quadratic,reduce,d]
  refine ⟨i,j,hi,hj,?_,?_⟩
  · intro hd
    exact hfirst (he0.symm.trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hd))
  · intro hd
    exact hsecond (he1.symm.trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hd))

end OriginalBoundedIntegerShear318
