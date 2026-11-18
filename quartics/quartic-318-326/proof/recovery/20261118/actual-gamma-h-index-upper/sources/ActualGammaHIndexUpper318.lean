module
public import ResidueProjectiveSlopes318
public import GammaHDiamond318
public import EulerIndex318
public section
noncomputable section
namespace ActualGammaHIndexUpper318
open scoped MatrixGroups
open ResidueProjectiveSlopes318 CongruenceSubgroup GammaHGroup318
open Finset
local instance pf (N : ℕ) (p : N.primeFactors) : Fact p.val.Prime :=
  ⟨Nat.prime_of_mem_primeFactors p.property⟩
private theorem ep (N : ℕ) (p : N.primeFactors) : 0<N.factorization p.val :=
  (Nat.prime_of_mem_primeFactors p.property).factorization_pos_of_dvd
    (Nat.mem_primeFactors.mp p.property).2.2 (Nat.dvd_of_mem_primeFactors p.property)
local instance ez (N : ℕ) (p : N.primeFactors) : NeZero (N.factorization p.val) :=
  ⟨(ep N p).ne'⟩
local instance pz (N : ℕ) (p : N.primeFactors) : NeZero p.val :=
  ⟨(Nat.prime_of_mem_primeFactors p.property).ne_zero⟩

abbrev R (N : ℕ) (p : N.primeFactors) := ZMod (p.val ^ N.factorization p.val)

private theorem unimod (N : ℕ) (p : N.primeFactors) (g : SL(2,ℤ)) :
    IsUnit (g 0 0:R N p) ∨ IsUnit (g 1 0:R N p) := by
  have hd : (g 0 0:R N p)*(g 1 1:R N p) + (-(g 0 1:R N p))*(g 1 0:R N p)=1 := by
    have h := congrArg (Int.castRingHom (R N p)) g.det_coe
    rw [Matrix.det_fin_two] at h
    simpa [sub_eq_add_neg,neg_mul] using h
  exact (IsLocalRing.isUnit_or_isUnit_of_add_one hd).imp
    isUnit_of_mul_isUnit_left isUnit_of_mul_isUnit_right

private def label (N : ℕ) (g : SL(2,ℤ)) (p : N.primeFactors) : Charts (R N p) :=
  code (g 0 0:R N p) (g 1 0:R N p) (unimod N p g)

/-- Identical local affine/reciprocal labels force the SL2 cosets to agree.
Only the first columns are used. In particular no assumption that all local
residue label tuples are attained by integral SL2 matrices is needed. -/
private theorem coset_eq (N : ℕ) [NeZero N] (g h : SL(2,ℤ))
    (H : label N g=label N h) :
    (g:SL(2,ℤ) ⧸ Gamma0 N)=(h:SL(2,ℤ) ⧸ Gamma0 N) := by
  have hc : ((g 0 0*h 1 0-g 1 0*h 0 0:ℤ):ZMod N)=0 := by
    apply (ZMod.equivPi N (NeZero.ne N)).injective
    rw [map_intCast,map_zero]
    funext p
    change ((g 0 0*h 1 0-g 1 0*h 0 0:ℤ):R N p)=0
    push_cast
    exact cross (unimod N p g) (unimod N p h) (congrFun H p)
  rw [QuotientGroup.eq,Gamma0_mem]
  have he : (g⁻¹*h) 1 0=g 0 0*h 1 0-g 1 0*h 0 0 := by
    change ((↑(g⁻¹*h):Matrix (Fin 2) (Fin 2) ℤ) 1 0)=_
    simp [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
      Matrix.mul_apply,Fin.sum_univ_two,Matrix.adjugate_fin_two] <;> ring
  rwa [he]

theorem gamma0_card (N : ℕ) [NeZero N] :
    (Gamma0 N).index≤∏p : N.primeFactors,(p.val^(N.factorization p.val)+p.val^(N.factorization p.val-1)) := by
  classical
  let f (x : SL(2,ℤ) ⧸ Gamma0 N) := label N x.out
  have hinj : Function.Injective f := by
    intro x y h
    exact x.out_eq.symm.trans ((coset_eq N x.out y.out h).trans y.out_eq)
  have hc := Nat.card_le_card_of_injective f hinj
  rw [Nat.card_pi] at hc
  exact hc.trans (Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _) fun p _ => charts_card_le p.val (N.factorization p.val)
    (Nat.prime_of_mem_primeFactors p.property) (ep N p))

/-- The bound is sharp; only the inequality direction is asserted here. -/
theorem gamma0 (N : ℕ) [NeZero N] :
    ((Gamma0 N).index:ℝ) ≤ (N:ℝ)*EulerIndex318.eulerProduct N := by
  classical
  have h : ((Gamma0 N).index:ℝ) ≤
    ∏p : N.primeFactors,((p.val:ℝ)^N.factorization p.val + (p.val:ℝ)^(N.factorization p.val-1)) := by
    exact_mod_cast gamma0_card N
  apply h.trans_eq
  have localFactor (p : N.primeFactors) : (p.val:ℝ)^N.factorization p.val+
      (p.val:ℝ)^(N.factorization p.val-1)=(p.val:ℝ)^N.factorization p.val*EulerIndex318.eulerFactor p.val := by
    obtain ⟨e,he⟩ := Nat.exists_eq_succ_of_ne_zero (ep N p).ne'
    rw [he]
    simp only [Nat.succ_sub_succ_eq_sub,Nat.sub_zero,pow_succ,EulerIndex318.eulerFactor]
    have hp : (p.val:ℝ)≠0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors p.property).ne_zero
    field_simp [hp] <;> ring
  simp_rw [localFactor,Finset.prod_mul_distrib]
  have hp : (∏p : N.primeFactors,(p.val:ℝ)^N.factorization p.val)=(N:ℝ) := by
    exact_mod_cast (Nat.prod_primeFactors_coe_pow_factorization (n:=N) (NeZero.ne N)).symm
  rw [hp]
  simp [EulerIndex318.eulerProduct,Finset.prod_coe_sort]

/-- Relative index from the true Gamma0 lower-right quotient, then absolute
index using the finite residue slope bound. The geometric degree must still
be compared to the group index in a separate analytic/algebraic map. -/
theorem gammaH_index (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) :
    ((gammaH N H).index:ℝ) ≤ (N:ℝ)*H.index*EulerIndex318.eulerProduct N := by
  have he : (gammaH N H).index=H.index*(Gamma0 N).index := by
    rw [gammaH,Subgroup.index_map_subtype,H.index_comap_of_surjective (GammaHDiamond318.diagonal_surjective N)]
  rw [he,Nat.cast_mul]
  calc _ ≤ (H.index:ℝ)*((N:ℝ)*EulerIndex318.eulerProduct N) :=
        mul_le_mul_of_nonneg_left (gamma0 N) (by positivity)
       _ = _ := by ring
end ActualGammaHIndexUpper318
