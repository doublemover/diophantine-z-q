module
public import OriginalSieveCRTProduct318
public section
noncomputable section
namespace OriginalSieveCRTSurvivors318
open QuadricCRTAssembly318 PrimitiveSieveCRT318 OriginalSieveCRTProduct318
open scoped BigOperators
set_option maxHeartbeats 1000000
variable {J : Type*} [Fintype J] [DecidableEq J]

@[expose] def goodSet {R : Type*} [CommRing R] (κ : R) (γ : J → R) : Set (Quadric κ) :=
  {z | z≠PrimitiveSieveCRT318.origin κ ∧
    ¬∃ j, z.1.1.1^2+z.1.1.2^2+γ j*z.1.2.2^2=0}

/-- Partition the original nonzero quadric, not the whole affine quadric. -/
@[expose] def partitionEquiv {R : Type*} [CommRing R] (κ : R) (γ : J → R) :
    {z : Quadric κ // z≠PrimitiveSieveCRT318.origin κ} ≃ (badSet κ γ ⊕ goodSet κ γ) := by
  classical
  let P (z : Quadric κ) := ∃ j, z.1.1.1^2+z.1.1.2^2+γ j*z.1.2.2^2=0
  exact {
    toFun := fun z => if h : P z.1 then Sum.inl ⟨z.1,z.2,h⟩ else Sum.inr ⟨z.1,z.2,h⟩
    invFun := fun z => match z with
      | Sum.inl z => ⟨z.1,z.2.1⟩
      | Sum.inr z => ⟨z.1,z.2.1⟩
    left_inv := by intro z; dsimp; split <;> rfl
    right_inv := by
      intro z
      cases z with
      | inl z => simp only [dif_pos z.2.2]
      | inr z => simp only [dif_neg z.2.2] }

theorem local_good_density (p : ℕ) [Fact p.Prime] (hp2 : p≠2)
    (κ : ℤ) (hκ : ¬(p:ℤ)∣κ) (γ : J → ℤ) (j₀ : J) :
    (Nat.card (goodSet (κ : ZMod p) (fun j => (γ j : ZMod p))):ℚ)/((p^4-1:ℕ):ℚ)=
      1-FiniteSieveDensity318.density (κ : ZMod p) (fun j => (γ j : ZMod p)) j₀ := by
  classical
  have hF : ringChar (ZMod p)≠2 := by simpa only [ringChar_zmod_n] using hp2
  have hk : (κ : ZMod p)≠0 := by
    intro he
    exact hκ ((ZMod.intCast_zmod_eq_zero_iff_dvd κ p).mp he)
  have hc : Nat.card {z : Quadric (κ : ZMod p) // z≠PrimitiveSieveCRT318.origin _}=p^4-1 := by
    rw [Nat.card_congr (nonzeroFieldEquiv (κ : ZMod p))]
    simpa only [ZMod.card] using FiniteFiveQuadricCount318.nonzero_quadric_card hF
      (GoodReductionResidue318.two_residue_ne p hp2) (κ : ZMod p) hk
  have hsum : Nat.card (badSet (κ : ZMod p) (fun j => (γ j : ZMod p)))+
      Nat.card (goodSet (κ : ZMod p) (fun j => (γ j : ZMod p)))=p^4-1 := by
    rw [←hc,Nat.card_congr (partitionEquiv (κ : ZMod p) (fun j => (γ j : ZMod p))),Nat.card_sum]
  have hp : 2≤p := (Fact.out : p.Prime).two_le
  have hpq : (2:ℚ)≤p := by exact_mod_cast hp
  have hp4 : 1≤p^4 := by have hh : 0<p^4 := pow_pos (by omega) 4; omega
  have hden : ((p^4-1:ℕ):ℚ)≠0 := by
    rw [Nat.cast_sub hp4,Nat.cast_pow,Nat.cast_one]
    have hh : (4:ℚ)≤(p:ℚ)^2 := by nlinarith
    nlinarith [sq_nonneg ((p:ℚ)^2-4)]
  have hs : (Nat.card (badSet (κ : ZMod p) (fun j => (γ j : ZMod p))):ℚ)+
      (Nat.card (goodSet (κ : ZMod p) (fun j => (γ j : ZMod p))):ℚ)=((p^4-1:ℕ):ℚ) :=
    by exact_mod_cast hsum
  rw [←local_density p hp2 κ hκ γ j₀]
  field_simp [hden]
  linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hd : Function.Injective p)

@[expose] def Survivors (κ : ℤ) (γ : J → ℤ) :=
  Admissible p hp hd κ (fun i => goodSet (κ : ZMod (p i)) (fun j => (γ j : ZMod (p i))))

/-- Exact finite Euler factor for simultaneous avoidance on the original
primitive quadric. Infinite products and integer-point estimates are NOT
conclusions of finite CRT. -/
theorem survivor_density (κ : ℤ) (hp2 : ∀ i, p i≠2) (hκ : ∀ i, ¬(p i:ℤ)∣κ)
    (γ : J → ℤ) (j₀ : J) :
    (Nat.card (Survivors p hp hd κ γ):ℚ)/(Nat.card (Primitive p hp hd κ):ℚ)=
      ∏ i, (1-densityAt (p i) (hp i) κ γ j₀) := by
  rw [Survivors,normalized_card p hp hd κ hp2 hκ]
  apply Finset.prod_congr rfl
  intro i hi
  letI : Fact (p i).Prime := ⟨hp i⟩
  exact local_good_density (p i) (hp2 i) κ (hκ i) γ j₀

end OriginalSieveCRTSurvivors318
