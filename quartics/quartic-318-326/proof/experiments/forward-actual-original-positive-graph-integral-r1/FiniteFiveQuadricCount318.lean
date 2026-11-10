module
public import FiniteNormDifferenceCount318
public section
noncomputable section
namespace FiniteFiveQuadricCount318
open FiniteNormDifferenceCount318
open scoped BigOperators
set_option maxHeartbeats 1000000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The literal five-variable local-sieve quadric, with all original coordinates. -/
@[expose] def Quadric (κ : F) :=
  {z : (F×F)×(F×F)×F // z.1.1^2+z.1.2^2-(z.2.1.1^2+z.2.1.2^2)=κ*z.2.2^2}

@[expose] def quadricFibers (κ : F) : Quadric κ ≃ (Σ w : F, NormDifference (κ*w^2)) where
  toFun z := ⟨z.1.2.2,⟨(z.1.1,z.1.2.1),z.2⟩⟩
  invFun z := ⟨(z.2.1.1,z.2.1.2,z.1),z.2.2⟩
  left_inv z := by cases z; rfl
  right_inv z := by cases z; rfl

/-- The full five-variable quadric has exactly q⁴ points for every nonzero
κ in odd characteristic, in both split and inert norm cases. -/
theorem quadric_card (hF : ringChar F≠2) (h2 : (2:F)≠0) (κ : F) (hκ : κ≠0) :
    Nat.card (Quadric κ)=Fintype.card F^4 := by
  classical
  have hsum : (Nat.card (Quadric κ):ℤ)=
      ∑ w : F, (Nat.card (NormDifference (κ*w^2)):ℤ) := by
    rw [Nat.card_congr (quadricFibers κ)]
    simp only [Nat.card_eq_fintype_card,Fintype.card_sigma,Nat.cast_sum]
  have he (w : F) : κ*w^2=0 ↔ w=0 := by simp [hκ]
  have hz : (Nat.card (Quadric κ):ℤ)=(Fintype.card F:ℤ)^4 := by
    rw [hsum]
    simp_rw [difference_count hF h2,he]
    rw [Finset.sum_add_distrib]
    simp
    <;> ring
  exact_mod_cast hz

@[expose] def origin (κ : F) : Quadric κ := ⟨((0,0),(0,0),0),by ring⟩

/-- Removing exactly the original zero vector gives the primitive local
fiber size q⁴−1 used by the analytic local-density normalization. -/
theorem nonzero_quadric_card (hF : ringChar F≠2) (h2 : (2:F)≠0) (κ : F) (hκ : κ≠0) :
    Nat.card {z : Quadric κ // z≠origin κ}=Fintype.card F^4-1 := by
  classical
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl (fun z : Quadric κ => z=origin κ),
    Fintype.card_subtype_eq,←Nat.card_eq_fintype_card,quadric_card hF h2 κ hκ]

end FiniteFiveQuadricCount318
