module
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic.FinCases
public import RationalSectionHeight318
public import InducedLattice318
public section
noncomputable section
namespace SmallActualPELHeight318
open NumberField SectionHeight318 Height
set_option maxHeartbeats 1500000

@[expose] def B : ℝ := 2765952000^2*(4*12540153541944538512)

private theorem budget : 2*Real.log Real.pi+Real.log (210*B)+Real.log 32<120 := by
  have hB : 0<B := by norm_num [B]
  have hn : (210:ℝ)*B*32*16<2^145 := by norm_num [B]
  have hl := Real.log_lt_log (by positivity : (0:ℝ)<210*B*32*16) hn
  rw [Real.log_pow,Real.log_mul (by positivity : (210:ℝ)*B*32≠0) (by norm_num : (16:ℝ)≠0),
    Real.log_mul (by positivity : (210:ℝ)*B≠0) (by norm_num : (32:ℝ)≠0)] at hl
  have h16 : Real.log (16:ℝ)=2*Real.log 4 := by
    rw [show (16:ℝ)=4^2 by norm_num,Real.log_pow] <;> norm_num
  rw [h16] at hl
  norm_num only [Nat.cast_ofNat] at hl
  linarith [Real.log_lt_log Real.pi_pos Real.pi_lt_four,Real.log_two_lt_d9]

private theorem unscale (s : ℚ) : logHeight₁ s≤logHeight₁ (32*s)+Real.log 32 := by
  have h:=logHeight₁_mul_le (32*s) ((1:ℚ)/32)
  rw [show (32*s)*((1:ℚ)/32)=s by ring] at h
  have hc : logHeight₁ ((1:ℚ)/32)=Real.log 32 := by norm_num [Rat.logHeight₁_eq_log_max]
  rwa [hc] at h

/-- Upper bound for the actual two evaluated vectors in one bicanonical fiber.
φ is the composition of the Hodge-square frame with the *actual squared KS
isomorphism on the generic fiber*. The genuine finite image inclusion and
the actual Petersson calibration are required pointwise, not a pre-given
degree or bound for the quotient coordinate. The 210 multiplier sends the
sections into the Hodge-square lattice at each finite place. -/
theorem via_scaled_vectors {L V : Type*} [Field L] [NumberField L]
    [AddCommGroup V] [Module L V] (φ : L ≃ₗ[L] V) (H : FrameNorms L)
    (s : ℚ) (s₀ s₁ : V) (hnz : s₀≠0) (hr : s₁=((32*s:ℚ):L) • s₀)
    (C : FinitePlace L → Set V)
    (hk : ∀ (w : FinitePlace L) x, x∈C w → (210:L) • x ∈
      φ '' {z : L | w z*(H.finiteNorm w)^2≤1})
    (hi : ∀ (w : FinitePlace L) (i : Fin 2), ![s₀,s₁] i∈C w)
    (Pet : InfinitePlace L → V → ℝ)
    (hiso : ∀ (w : InfinitePlace L) (z : L), Pet w (φ z)=w z*(H.arch w)^2)
    (hsup : ∀ (w : InfinitePlace L) (i : Fin 2), Pet w (![s₀,s₁] i)≤B) :
    logHeight₁ s<2*(H.normalizedDegree-Real.log Real.pi)+120 := by
  let z₀ : L:=φ.symm s₀
  let z₁ : L:=φ.symm s₁
  have hz : z₀≠0 := by
    intro he
    exact hnz (φ.symm.injective (he.trans φ.symm.map_zero.symm))
  have hpair (i : Fin 2) :
      ![(210:L)*z₀,(210:L)*z₁] i=(210:L)*φ.symm (![s₀,s₁] i) := by
    fin_cases i <;> rfl
  have hr' : (210:L)*z₁=((32*s:ℚ):L)*((210:L)*z₀) := by
    change (210:L)*φ.symm s₁=((32*s:ℚ):L)*((210:L)*φ.symm s₀)
    rw [hr,map_smul,smul_eq_mul]
    ring
  have ha (w : InfinitePlace L) (i : Fin 2) :
      w (![(210:L)*z₀,(210:L)*z₁] i)*(InducedLattice318.square H).arch w≤210*B := by
    rw [hpair,map_mul]
    have hw : w (210:L)=(210:ℝ) := w.map_natCast 210
    rw [hw]
    have hv := hiso w (φ.symm (![s₀,s₁] i))
    rw [φ.apply_symm_apply] at hv
    change 210*w (φ.symm (![s₀,s₁] i))*(H.arch w)^2≤210*B
    calc
      _ = 210*Pet w (![s₀,s₁] i) := by rw [hv]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hsup w i) (by norm_num)
  have hf (w : FinitePlace L) (i : Fin 2) :
      w (![(210:L)*z₀,(210:L)*z₁] i)*(InducedLattice318.square H).finiteNorm w≤1 := by
    rw [hpair]
    obtain ⟨x,hx,he⟩ := hk w _ (hi w i)
    have hx' : x=(210:L)*φ.symm (![s₀,s₁] i) := by
      apply φ.injective
      change φ x=φ ((210:L) • φ.symm (![s₀,s₁] i))
      rw [map_smul,φ.apply_symm_apply]
      exact he
    exact hx' ▸ hx
  have hh := rational_section_height ((210:L)*z₀) ((210:L)*z₁) (32*s)
    (mul_ne_zero (by norm_num) hz) hr' (InducedLattice318.square H) (210*B) ha hf
  rw [InducedLattice318.square_degree] at hh
  linarith [unscale s,budget]

/-- The numerical height on this left-hand side is definitionally the literal
old ContactHeight318.pointHeight u v. Deliberately no import of the global
CM/non-CM or 49/8 infrastructure is needed to state this conversion. -/
theorem projective_of_ratio (u v : ℤ) (h : ℝ)
    (hr : logHeight₁ ((u:ℚ)/(v:ℚ))<h) :
    logHeight (![(u:ℚ),(v:ℚ)] : Fin 2 → ℚ)<h := by
  rwa [logHeight₁_div_eq_logHeight] at hr

end SmallActualPELHeight318
