module
public import FiniteCoefficientFiberCount318
public section
noncomputable section
namespace FiniteSieveDensity318
open FiniteFiveQuadricCount318 FiniteCoefficientVanishing318 FiniteCoefficientFiberCount318
open scoped BigOperators
set_option maxHeartbeats 1000000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def Total (κ : F) (γ : ι → F) := {z : Quadric κ //
  ∃ i, z.1.1.1^2+z.1.1.2^2+γ i*z.1.2.2^2=0}

@[expose] def totalFibers (κ : F) (γ : ι → F) : Total κ γ ≃ (Σ w : F, Locus κ γ w) where
  toFun z := ⟨z.1.1.2.2,⟨⟨(z.1.1.1,z.1.1.2.1),z.1.2⟩,z.2⟩⟩
  invFun z := ⟨⟨(z.2.1.1.1,z.2.1.1.2,z.1),z.2.1.2⟩,z.2.2⟩
  left_inv z := by cases z; rfl
  right_inv z := by cases z; rfl

@[expose] def totalOrigin (κ : F) (γ : ι → F) (i₀ : ι) : Total κ γ :=
  ⟨origin κ,⟨i₀,by simp [origin]⟩⟩

@[expose] def nuZero : ℤ := (Fintype.card F:ℤ)+((Fintype.card F:ℤ)-1)*quadraticChar F (-1:F)
@[expose] def nonzeroCount : ℤ := (Fintype.card F:ℤ)-quadraticChar F (-1:F)

/-- Sum the complete original vanishing locus, counting w0 only once. -/
theorem total_card (hF : ringChar F≠2) (h2 : (2:F)≠0)
    (κ : F) (hκ : κ≠0) (γ : ι → F) (hγ : Function.Injective γ)
    (i₀ i₁ : ι) (h0 : γ i₀=0) (h1 : γ i₁= -κ) :
    (Nat.card (Total κ γ):ℤ)=((Fintype.card F:ℤ)-1)*
      (2*nuZero (F:=F)*nonzeroCount (F:=F)+
        ((Fintype.card ι:ℤ)-2)*(nonzeroCount (F:=F))^2)+(nuZero (F:=F))^2 := by
  classical
  let K : ℤ := 2*nuZero (F:=F)*nonzeroCount (F:=F)+
    ((Fintype.card ι:ℤ)-2)*(nonzeroCount (F:=F))^2
  have hf (w : F) : (Nat.card (Locus κ γ w):ℤ)=K+
      if w=0 then (nuZero (F:=F))^2-K else 0 := by
    by_cases hw : w=0
    · subst w
      rw [zero_card hF κ γ i₀,if_pos rfl]
      dsimp [nuZero]
      ring
    · rw [nonzero_card hF h2 κ hκ γ hγ i₀ i₁ h0 h1 w hw,if_neg hw,add_zero]
      rfl
  have he : (Nat.card (Total κ γ):ℤ)=∑ w : F, (Nat.card (Locus κ γ w):ℤ) := by
    rw [Nat.card_congr (totalFibers κ γ)]
    simp only [Nat.card_eq_fintype_card,Fintype.card_sigma,Nat.cast_sum]
  rw [he]
  simp_rw [hf]
  rw [Finset.sum_add_distrib]
  simp
  dsimp [K]
  ring

/-- Exact original local-sieve numerator on the nonzero quadric. -/
theorem primitive_card (hF : ringChar F≠2) (h2 : (2:F)≠0)
    (κ : F) (hκ : κ≠0) (γ : ι → F) (hγ : Function.Injective γ)
    (i₀ i₁ : ι) (h0 : γ i₀=0) (h1 : γ i₁= -κ) :
    (Nat.card {z : Total κ γ // z≠totalOrigin κ γ i₀}:ℤ)=
      ((Fintype.card F:ℤ)-1)*nonzeroCount (F:=F)*
        (2*nuZero (F:=F)+((Fintype.card ι:ℤ)-2)*nonzeroCount (F:=F))+
        (nuZero (F:=F))^2-1 := by
  classical
  letI : Nonempty (Total κ γ) := ⟨totalOrigin κ γ i₀⟩
  have hcard : 1≤Fintype.card (Total κ γ) := by
    have hp := Fintype.card_pos (α:=Total κ γ)
    omega
  rw [Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl (fun z : Total κ γ => z=totalOrigin κ γ i₀),
    Fintype.card_subtype_eq,Nat.cast_sub hcard,Nat.cast_one,
    ←Nat.card_eq_fintype_card,total_card hF h2 κ hκ γ hγ i₀ i₁ h0 h1]
  ring

@[expose] def density (κ : F) (γ : ι → F) (i₀ : ι) : ℚ :=
  (Nat.card {z : Total κ γ // z≠totalOrigin κ γ i₀}:ℚ)/
    (Nat.card {z : Quadric κ // z≠origin κ}:ℚ)

/-- Numerator and denominator are cardinalities of the literal local sets. -/
theorem density_formula (hF : ringChar F≠2) (h2 : (2:F)≠0)
    (κ : F) (hκ : κ≠0) (γ : ι → F) (hγ : Function.Injective γ)
    (i₀ i₁ : ι) (h0 : γ i₀=0) (h1 : γ i₁= -κ) :
    density κ γ i₀=
      (((Fintype.card F:ℚ)-1)*(nonzeroCount (F:=F):ℚ)*
        (2*(nuZero (F:=F):ℚ)+((Fintype.card ι:ℚ)-2)*(nonzeroCount (F:=F):ℚ))+
        (nuZero (F:=F):ℚ)^2-1)/((Fintype.card F:ℚ)^4-1) := by
  have hn := primitive_card hF h2 κ hκ γ hγ i₀ i₁ h0 h1
  have hnq : (Nat.card {z : Total κ γ // z≠totalOrigin κ γ i₀}:ℚ)=
      ((Fintype.card F:ℚ)-1)*(nonzeroCount (F:=F):ℚ)*
        (2*(nuZero (F:=F):ℚ)+((Fintype.card ι:ℚ)-2)*(nonzeroCount (F:=F):ℚ))+
        (nuZero (F:=F):ℚ)^2-1 := by exact_mod_cast hn
  have hq : 1≤Fintype.card F^4 := by
    have hp := Fintype.one_lt_card (α:=F)
    have hpos : 0<Fintype.card F^4 := pow_pos (by omega) 4
    omega
  rw [density,hnq,nonzero_quadric_card hF h2 κ hκ,Nat.cast_sub hq,Nat.cast_pow,Nat.cast_one]

/-- In particular the two-form inert density is NOT zero: its surviving
exceptional fibers give exactly2/(q²+1), as required by the original audit. -/
theorem two_inert_density (hF : ringChar F≠2) (h2 : (2:F)≠0)
    (κ : F) (hκ : κ≠0) (γ : ι → F) (hγ : Function.Injective γ)
    (i₀ i₁ : ι) (h0 : γ i₀=0) (h1 : γ i₁= -κ)
    (hk : Fintype.card ι=2) (hχ : quadraticChar F (-1:F)= -1) :
    density κ γ i₀=2/((Fintype.card F:ℚ)^2+1) := by
  have hν : nuZero (F:=F)=1 := by dsimp [nuZero]; rw [hχ]; ring
  have hn : nonzeroCount (F:=F)=(Fintype.card F:ℤ)+1 := by
    dsimp [nonzeroCount]; rw [hχ]; ring
  rw [density_formula hF h2 κ hκ γ hγ i₀ i₁ h0 h1,hν,hn,hk]
  push_cast
  have hq : (1:ℚ)<Fintype.card F := by exact_mod_cast (Fintype.one_lt_card (α:=F))
  have hq2 : (1:ℚ)<(Fintype.card F:ℚ)^2 := by nlinarith
  have hq4 : (Fintype.card F:ℚ)^4-1≠0 := by
    nlinarith [sq_nonneg ((Fintype.card F:ℚ)^2-1)]
  have hplus : (Fintype.card F:ℚ)^2+1≠0 := by positivity
  field_simp [hq4,hplus]
  <;> ring

end FiniteSieveDensity318
