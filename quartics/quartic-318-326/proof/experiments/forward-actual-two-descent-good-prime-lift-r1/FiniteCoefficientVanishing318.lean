module
public import FiniteSplitAdjacentBound318
public section
noncomputable section
namespace FiniteCoefficientVanishing318
open FiniteGaussianNormCount318 FiniteNormDifferenceCount318
set_option maxHeartbeats 1000000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def Locus (κ : F) (γ : ι → F) (w : F) :=
  {z : NormDifference (κ*w^2) // ∃ i, z.1.1.1^2+z.1.1.2^2+γ i*w^2=0}

@[expose] def Fiber (κ : F) (γ : ι → F) (w : F) (i : ι) :=
  NormFiber (-γ i*w^2) × NormFiber (-(γ i+κ)*w^2)

@[expose] def intoLocus (κ : F) (γ : ι → F) (w : F) :
    (Σ i : ι, Fiber κ γ w i) → Locus κ γ w := fun z =>
  ⟨⟨(z.2.1.1,z.2.2.1),by linear_combination z.2.1.2-z.2.2.2⟩,
    ⟨z.1,by linear_combination z.2.1.2⟩⟩

/-- Nonzero w and distinct original coefficients make the vanishing loci
disjoint. Every original index is kept, rather than merged after counting. -/
theorem intoLocus_injective (κ : F) (γ : ι → F) (hγ : Function.Injective γ)
    (w : F) (hw : w≠0) : Function.Injective (intoLocus κ γ w) := by
  rintro ⟨i,⟨a,ha⟩,⟨b,hb⟩⟩ ⟨j,⟨c,hc⟩,⟨d,hd⟩⟩ he
  have hraw := congrArg (fun z : Locus κ γ w => z.1.1) he
  change (a,b)=(c,d) at hraw
  have hf := congrArg (fun z : (F×F)×(F×F) => z.1.1^2+z.1.2^2) hraw
  change a.1^2+a.2^2=c.1^2+c.2^2 at hf
  rw [ha,hc] at hf
  have hij : i=j := by
    apply hγ
    apply (mul_right_inj' (pow_ne_zero 2 hw)).mp
    linear_combination -hf
  subst j
  rcases Prod.mk.inj hraw with ⟨hac,hbd⟩
  cases hac
  cases hbd
  rfl

theorem intoLocus_surjective (κ : F) (γ : ι → F) (w : F) :
    Function.Surjective (intoLocus κ γ w) := by
  intro z
  obtain ⟨i,hi⟩ := z.2
  have ha : z.1.1.1.1^2+z.1.1.1.2^2= -γ i*w^2 := by linear_combination hi
  have hb : z.1.1.2.1^2+z.1.1.2.2^2= -(γ i+κ)*w^2 := by
    linear_combination hi-z.1.2
  refine ⟨⟨i,⟨z.1.1.1,ha⟩,⟨z.1.1.2,hb⟩⟩,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  rfl

@[expose] def locusFibers (κ : F) (γ : ι → F) (hγ : Function.Injective γ)
    (w : F) (hw : w≠0) : Locus κ γ w ≃ (Σ i : ι, Fiber κ γ w i) :=
  (Equiv.ofBijective (intoLocus κ γ w)
    ⟨intoLocus_injective κ γ hγ w hw,intoLocus_surjective κ γ w⟩).symm

open scoped BigOperators in
theorem locus_card_sum (κ : F) (γ : ι → F) (hγ : Function.Injective γ)
    (w : F) (hw : w≠0) : (Nat.card (Locus κ γ w):ℤ)=
      ∑ i : ι, (Nat.card (NormFiber (-γ i*w^2)):ℤ)*
        (Nat.card (NormFiber (-(γ i+κ)*w^2)):ℤ) := by
  classical
  rw [Nat.card_congr (locusFibers κ γ hγ w hw)]
  simp only [Fiber,Nat.card_eq_fintype_card,Fintype.card_sigma,Fintype.card_prod,
    Nat.cast_sum,Nat.cast_mul]

/-- At w0 all indexed equations coincide, so use one actual index and do
not multiply the zero fiber by the number of coefficients. -/
@[expose] def zeroLocus (κ : F) (γ : ι → F) (i₀ : ι) :
    Locus κ γ 0 ≃ NormFiber (0:F) × NormFiber (0:F) where
  toFun z := by
    have hi := Classical.choose_spec z.2
    have ha : z.1.1.1.1^2+z.1.1.1.2^2=0 := by simpa using hi
    have hb : z.1.1.2.1^2+z.1.1.2.2^2=0 := by
      have h := z.1.2
      simp only [zero_pow (by decide : (2:ℕ)≠0),mul_zero] at h
      linear_combination ha-h
    exact ⟨⟨z.1.1.1,ha⟩,⟨z.1.1.2,hb⟩⟩
  invFun z := ⟨⟨(z.1.1,z.2.1),by simpa using sub_eq_zero.mpr (z.1.2.trans z.2.2.symm)⟩,
    ⟨i₀,by simpa using z.1.2⟩⟩
  left_inv z := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv z := by apply Prod.ext <;> apply Subtype.ext <;> rfl

theorem zero_card (hF : ringChar F≠2) (κ : F) (γ : ι → F) (i₀ : ι) :
    (Nat.card (Locus κ γ 0):ℤ)=
      ((Fintype.card F:ℤ)+((Fintype.card F:ℤ)-1)*quadraticChar F (-1:F))^2 := by
  rw [Nat.card_congr (zeroLocus κ γ i₀),Nat.card_prod,Nat.cast_mul,norm_zero hF]
  ring

end FiniteCoefficientVanishing318
