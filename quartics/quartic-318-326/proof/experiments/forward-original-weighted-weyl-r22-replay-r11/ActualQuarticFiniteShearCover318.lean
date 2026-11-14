module
public import ActualQuarticUniformHeight318
public section
noncomputable section
namespace ActualQuarticFiniteShearCover318
open scoped BigOperators
open TernaryQuadraticLineCover318 OriginalWholeBasisCoordinates318
open OriginalAnisotropicResidueFibers318 OriginalNormPointSieveTail318
open OriginalBoundedIntegerShear318 OriginalAffineSieveEliminants318 ActualQuarticPointTail318
open OriginalOffsetEliminant318 ActualQuarticRectangleTail318 OriginalShearBoxBudget318
open OriginalControlledIntegralBasis318 OriginalEuclideanLattice318 IntegerResidueBoxCount318
open ActualGaussianChartObstruction318 ActualQuarticUniformHeight318
set_option maxHeartbeats 12000000

@[expose] def Eligible (κ t : ℤ) (u v z : Vector ℤ) (ij : Fin 5×Fin 5) : Prop :=
  fA true κ t (shear (ij.1:ℤ) (ij.2:ℤ) u v z)≠0
@[expose] def Index (κ t : ℤ) (u v z : Vector ℤ) := {ij : Fin 5×Fin 5 // Eligible κ t u v z ij}

lemma index_card (κ t : ℤ) (u v z : Vector ℤ) : Nat.card (Index κ t u v z)≤25 := by
  have hh := Nat.card_le_card_of_injective
    (Subtype.val : Index κ t u v z → Fin 5×Fin 5) Subtype.val_injective
  simpa only [Nat.card_eq_fintype_card,Fintype.card_prod,Fintype.card_fin] using hh

/-- The original coefficient-point set, defined BEFORE choosing a shear
or a witness prime. Both leading-prime divisibilities are absent from its
hypotheses; only original retained-modulus and kappa primes are excluded. -/
@[expose] def OriginalBad (κ t : ℤ) (u v z : Vector ℤ)
    (M A B C Y : ℕ) :=
  {c : Rectangle A B C // ∃ p : ℕ, p.Prime ∧ 5≤p ∧ Y<p ∧ 2*C<p ∧
    ¬(p:ℤ)∣κ ∧ ¬(p:ℤ)∣(M:ℤ) ∧
    Obstruction true κ t (synthesis u v z (coordinates c)) p}

@[expose] def Covered (κ t : ℤ) (u v z : Vector ℤ) (A B C Y : ℕ) :=
  Σ ij : Index κ t u v z, RectangleBad κ t u v
    (shear (ij.1.1:ℤ) (ij.1.2:ℤ) u v z) (A+4*C) (B+4*C) C Y

@[expose] def restore {κ t : ℤ} {u v z : Vector ℤ} {A B C Y : ℕ}
    (x : Covered κ t u v z A B C Y) : Vector ℤ :=
  coefficientEquiv (x.1.1.1:ℤ) (x.1.1.2:ℤ)
    (x.2.1.1.1,x.2.1.2.1,x.2.2.1.1)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every original bad coefficient point has an actual SAME-POINT image
in the fixed25 candidate rectangles. The selected member may depend on
the original witness prime, but the collection was fixed in advance. -/
theorem covered_point (q : ι → ℕ) (κ t : ℤ) (s : ∀ k, Option (ZMod (q k)))
    (u v z : Vector ℤ) (hb : IntegralBasisTriple q κ s u v z)
    (A B C Y : ℕ)
    (c : OriginalBad κ t u v z (FixedSquarefreeCRT318.modulus q) A B C Y) :
    ∃ x : Covered κ t u v z A B C Y, restore x=coordinates c.1 := by
  classical
  obtain ⟨p,hp,h5,hY,hC,hκ,hM,ho⟩ := c.2
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨i,j,hi,hj,hfirst,hsecond⟩ := actual_integer_shear q κ t s u v z hb p h5 hκ hM
  let ij : Index κ t u v z := ⟨(⟨i,hi⟩,⟨j,hj⟩),by
    intro he
    apply hsecond
    rw [he]
    exact dvd_zero _⟩
  let r := (coefficientEquiv (i:ℤ) (j:ℤ)).symm (coordinates c.1)
  have hA : |(coordinates c.1).1|≤(A:ℤ) := abs_le.mpr (Finset.mem_Icc.mp c.1.1.2)
  have hB : |(coordinates c.1).2.1|≤(B:ℤ) := abs_le.mpr (Finset.mem_Icc.mp c.1.2.1.2)
  have hCC : |(coordinates c.1).2.2|≤(C:ℤ) := abs_le.mpr (Finset.mem_Icc.mp c.1.2.2.2)
  obtain ⟨hrA,hrB,hrC⟩ := inverse_rectangle A B C i j hi hj (coordinates c.1) hA hB hCC
  have hA' : r.1∈Finset.Icc (-((A+4*C:ℕ):ℤ)) ((A+4*C:ℕ):ℤ) := by
    apply Finset.mem_Icc.mpr
    have hh := abs_le.mp hrA
    push_cast
    exact hh
  have hB' : r.2.1∈Finset.Icc (-((B+4*C:ℕ):ℤ)) ((B+4*C:ℕ):ℤ) := by
    apply Finset.mem_Icc.mpr
    have hh := abs_le.mp hrB
    push_cast
    exact hh
  have hC' : r.2.2∈Finset.Icc (-(C:ℤ)) (C:ℤ) := by
    rw [show r.2.2=(coordinates c.1).2.2 from hrC]
    exact c.1.2.2.2
  have he : affine (offset u v r.1 r.2.1) (shear (i:ℤ) (j:ℤ) u v z) r.2.2=
      synthesis u v z (coordinates c.1) := by
    change synthesis u v (shear (i:ℤ) (j:ℤ) u v z) r=_
    rw [synthesis_shear,AddEquiv.apply_symm_apply]
  have hlead : ¬(p:ℤ)∣fA true κ t (shear (i:ℤ) (j:ℤ) u v z) := hsecond
  let x : Covered κ t u v z A B C Y := ⟨ij,
    (⟨r.1,hA'⟩,⟨r.2.1,hB'⟩),⟨⟨r.2.2,hC'⟩,p,hp,hY,hC,hlead,by rw [he];exact ho⟩⟩
  refine ⟨x,?_⟩
  change coefficientEquiv (i:ℤ) (j:ℤ) ((coefficientEquiv (i:ℤ) (j:ℤ)).symm (coordinates c.1))=_
  exact AddEquiv.apply_symm_apply _ _

/-- Injectivity follows by recovering the SAME integer coefficients,
not by assuming the chosen primes or shears are unique. -/
theorem original_bad_card (q : ι → ℕ) (κ t : ℤ) (s : ∀ k, Option (ZMod (q k)))
    (u v z : Vector ℤ) (hb : IntegralBasisTriple q κ s u v z)
    (A B C Y : ℕ) :
    Nat.card (OriginalBad κ t u v z (FixedSquarefreeCRT318.modulus q) A B C Y)≤
      Nat.card (Covered κ t u v z A B C Y) := by
  classical
  let f := fun c => Classical.choose (covered_point q κ t s u v z hb A B C Y c)
  have hf (c) : restore (f c)=coordinates c.1 :=
    Classical.choose_spec (covered_point q κ t s u v z hb A B C Y c)
  apply Nat.card_le_card_of_injective f
  intro a b he
  have hh : coordinates a.1=coordinates b.1 := (hf a).symm.trans ((congrArg restore he).trans (hf b))
  apply Subtype.ext
  apply Prod.ext
  · exact Subtype.ext (congrArg Prod.fst hh)
  · apply Prod.ext
    · exact Subtype.ext (congrArg (fun c : Vector ℤ => c.2.1) hh)
    · exact Subtype.ext (congrArg (fun c : Vector ℤ => c.2.2) hh)


/-- Full true-quartic tail for actual second Gaussian source points,
without a leading-prime filter in its definition. The prime may choose
one member of the fixed25 family, but restore proves SAME-POINT injection.
Every height and zero cylinder is already constructed for the true K. -/
theorem actual_large_prime_rectangle (κ t : ℤ) (hκ : κ≠0) (ht : t≠0)
    (s : ∀ k : LiteralSliceModulus318.PrimeIndex κ t,
      Option (ZMod (LiteralSliceModulus318.prime κ t k)))
    (u v w z : Vector ℤ)
    (hb : IntegralBasisTriple (LiteralSliceModulus318.prime κ t) κ s u v z)
    (huv : ‖embed u‖≤‖embed v‖) (hvw : ‖embed v‖≤‖embed w‖)
    (hz : ‖embed z‖≤2*‖embed w‖) (A B C Y : ℕ) (hY : 2≤Y) :
    let A' := A+4*C
    let B' := B+4*C
    let N := fullHeight κ t A' B' (heightRadius A' B' ‖embed w‖)
    (Nat.card (OriginalBad κ t u v z (LiteralSliceModulus318.modulus κ t) A B C Y):ℝ)*Real.log (Y:ℝ)≤
      25*(((2*A'+1:ℕ):ℝ)*(2*B'+1)*2*Real.log N+
        8*((2*A'+1:ℕ)+(2*B'+1):ℝ)*(2*C+1)*Real.log (Y:ℝ)) := by
  classical
  let A' := A+4*C
  let B' := B+4*C
  let N := fullHeight κ t A' B' (heightRadius A' B' ‖embed w‖)
  let H := ((2*A'+1:ℕ):ℝ)*(2*B'+1)*2*Real.log N+
    8*((2*A'+1:ℕ)+(2*B'+1):ℝ)*(2*C+1)*Real.log (Y:ℝ)
  have hN : 1≤N := full_one κ t A' B' _
  have hl : 0≤Real.log (Y:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤Y by omega))
  have hlogN : 0≤Real.log N := Real.log_nonneg hN
  have hH : 0≤H := by dsimp [H];positivity
  have hbound (ij : Index κ t u v z) :
      (Nat.card (RectangleBad κ t u v (shear (ij.1.1:ℤ) (ij.1.2:ℤ) u v z) A' B' C Y):ℝ)*
        Real.log (Y:ℝ)≤H := by
    have hh := actual_original_rectangle κ t hκ ht s u v z hb
      (ij.1.1:ℤ) (ij.1.2:ℤ) ij.2 A' B' C Y (by omega)
    have hheight := actual_rectangle_height κ t u v w z huv hvw hz A' B'
      ij.1.1.val ij.1.2.val ij.1.1.isLt ij.1.2.isLt
    have hpos : 0<rectangleHeight κ t u v (shear (ij.1.1:ℤ) (ij.1.2:ℤ) u v z) A' B' :=
      zero_lt_one.trans_le (height_one κ t u v _ A' B')
    have hlog := Real.log_le_log hpos hheight
    have hmul := mul_le_mul_of_nonneg_left hlog
      (show 0≤((2*A'+1:ℕ):ℝ)*(2*B'+1)*2 by positivity)
    change _≤H
    dsimp [H]
    nlinarith only [hh,hmul]
  have hs := Finset.sum_le_sum (fun ij (_ : ij∈Finset.univ) => hbound ij)
  rw [←Finset.sum_mul] at hs
  have he : (Nat.card (Covered κ t u v z A B C Y):ℝ)=
      ∑ ij : Index κ t u v z, (Nat.card (RectangleBad κ t u v
        (shear (ij.1.1:ℤ) (ij.1.2:ℤ) u v z) A' B' C Y):ℝ) := by
    simp only [Covered,Nat.card_eq_fintype_card,Fintype.card_sigma,Nat.cast_sum]
  rw [←he] at hs
  have hc : (Nat.card (OriginalBad κ t u v z (LiteralSliceModulus318.modulus κ t) A B C Y):ℝ)≤
      (Nat.card (Covered κ t u v z A B C Y):ℝ) := by
    exact_mod_cast original_bad_card (LiteralSliceModulus318.prime κ t) κ t s u v z hb A B C Y
  have hi : (Fintype.card (Index κ t u v z):ℝ)≤25 := by
    exact_mod_cast index_card κ t u v z
  have hsmall := mul_le_mul_of_nonneg_right hc hl
  have hindex := mul_le_mul_of_nonneg_right hi hH
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hs
  change _≤25*H
  exact hsmall.trans (hs.trans hindex)

end ActualQuarticFiniteShearCover318
