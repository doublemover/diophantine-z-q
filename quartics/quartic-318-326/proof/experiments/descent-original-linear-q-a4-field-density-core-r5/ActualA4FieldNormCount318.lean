module
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic
public section
noncomputable section
namespace ActualA4FieldNormCount318
open scoped BigOperators
set_option maxHeartbeats 1000000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Cardinal of the literal square fibre, with no curve dependency. -/
theorem fiber_count (hF : ringChar F ≠ 2) (a : F) :
    (Nat.card {r : F // r^2=a}:ℤ)=quadraticChar F a+1 := by
  let T : Set F := {r : F | r^2=a}
  have hT : T.toFinset.card=Fintype.card T := Set.toFinset_card T
  have hN : Nat.card {r : F // r^2=a}=T.toFinset.card := calc
    _ = Nat.card ↥T := rfl
    _ = Fintype.card ↥T := Nat.card_eq_fintype_card
    _ = _ := hT.symm
  rw [hN]
  exact quadraticChar_card_sqrts hF a

@[expose] def Hyperbola (t : F) := {z : F×F // z.1*z.2=t}
@[expose] def Difference (t : F) := {z : F×F // z.1^2-z.2^2=t}

lemma first_ne (t : F) (ht : t≠0) (z : Hyperbola t) : z.1.1≠0 := by
  intro he
  apply ht
  rw [←z.2,he,zero_mul]

@[expose] def hyperbolaUnits (t : F) (ht : t≠0) : Hyperbola t ≃ Fˣ where
  toFun z := Units.mk0 z.1.1 (first_ne t ht z)
  invFun u := ⟨((u:F),t*(u:F)⁻¹),by
    calc
      _ = t*((u:F)*(u:F)⁻¹) := by ring
      _ = t := by rw [mul_inv_cancel₀ (Units.ne_zero u),mul_one]⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change t*z.1.1⁻¹=z.1.2
      calc
        t*z.1.1⁻¹=(z.1.1*z.1.2)*z.1.1⁻¹ :=
          congrArg (fun k : F => k*z.1.1⁻¹) z.2.symm
        _ = _ := by
          rw [mul_comm z.1.1 z.1.2,mul_assoc,mul_inv_cancel₀ (first_ne t ht z),mul_one]
  right_inv u := by apply Units.ext; rfl

/-- Exact change from the difference conic to a nonzero product fiber. -/
@[expose] def differenceHyperbola (h2 : (2:F)≠0) (t : F) : Difference t ≃ Hyperbola t where
  toFun z := ⟨(z.1.1-z.1.2,z.1.1+z.1.2),by linear_combination z.2⟩
  invFun z := ⟨((z.1.1+z.1.2)/2,(z.1.2-z.1.1)/2),by
    calc
      _ = z.1.1*z.1.2 := by field_simp [h2] <;> ring
      _ = t := z.2⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext <;> dsimp <;> field_simp [h2] <;> ring
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext <;> dsimp <;> field_simp [h2] <;> ring

@[expose] def differenceFibers (t : F) : Difference t ≃ (Σ x : F, {y : F // y^2=x^2-t}) where
  toFun z := ⟨z.1.1,z.1.2,by linear_combination -z.2⟩
  invFun z := ⟨(z.1,z.2.1),by linear_combination -z.2.2⟩
  left_inv z := by cases z; rfl
  right_inv z := by cases z; rfl

/-- Count all solutions of x²−y²=t, including every ordinate fiber. -/
theorem difference_card (h2 : (2:F)≠0) (t : F) (ht : t≠0) :
    Nat.card (Difference t)=Fintype.card F-1 := by
  rw [Nat.card_congr ((differenceHyperbola h2 t).trans (hyperbolaUnits t ht))]
  simp only [Nat.card_eq_fintype_card,Fintype.card_units]

/-- The quadratic polynomial character sum is derived by counting the
same conic two ways, not imported as an assumed local-density formula. -/
theorem difference_character_sum (hF : ringChar F≠2) (h2 : (2:F)≠0)
    (t : F) (ht : t≠0) : (∑ x : F, quadraticChar F (x^2-t))= -1 := by
  classical
  have hf : (Nat.card (Difference t):ℤ)=(Fintype.card F:ℤ)+
      ∑ x : F, quadraticChar F (x^2-t) := by
    rw [Nat.card_congr (differenceFibers t)]
    simp only [Nat.card_eq_fintype_card,Fintype.card_sigma,Nat.cast_sum]
    have he (x : F) : (Fintype.card {y : F // y^2=x^2-t}:ℤ)=quadraticChar F (x^2-t)+1 := by
      simpa only [Nat.card_eq_fintype_card] using fiber_count hF (x^2-t)
    simp_rw [he]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
    ring
  have hd : (Nat.card (Difference t):ℤ)=(Fintype.card F:ℤ)-1 := by
    rw [difference_card h2 t ht,Nat.cast_sub (Nat.le_of_lt Fintype.one_lt_card),Nat.cast_one]
  omega


@[expose] def NormFiber (t : F) := {z : F×F // z.1^2+z.2^2=t}
@[expose] def normFibers (t : F) : NormFiber t ≃ (Σ x : F, {y : F // y^2=t-x^2}) where
  toFun z := ⟨z.1.1,z.1.2,by linear_combination z.2⟩
  invFun z := ⟨(z.1,z.2.1),by linear_combination z.2.2⟩
  left_inv z := by cases z; rfl
  right_inv z := by cases z; rfl

lemma norm_character_formula (hF : ringChar F≠2) (t : F) :
    (Nat.card (NormFiber t):ℤ)=(Fintype.card F:ℤ)+∑ x : F, quadraticChar F (t-x^2) := by
  classical
  rw [Nat.card_congr (normFibers t)]
  simp only [Nat.card_eq_fintype_card,Fintype.card_sigma,Nat.cast_sum]
  have he (x : F) : (Fintype.card {y : F // y^2=t-x^2}:ℤ)=quadraticChar F (t-x^2)+1 := by
    simpa only [Nat.card_eq_fintype_card] using fiber_count hF (t-x^2)
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  ring

lemma square_character_sum : (∑ x : F, quadraticChar F (x^2))=(Fintype.card F:ℤ)-1 := by
  classical
  have he : (∑ x ∈ (Finset.univ.erase (0:F)),quadraticChar F (x^2))=
      ((Finset.univ.erase (0:F)).card:ℤ) := by
    calc
      _ = ∑ x ∈ (Finset.univ.erase (0:F)),(1:ℤ) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact quadraticChar_sq_one' (Finset.mem_erase.mp hx).1
      _ = _ := by simp
  have hs := Finset.sum_erase_add (Finset.univ:Finset F)
    (fun x : F => quadraticChar F (x^2)) (Finset.mem_univ (0:F))
  rw [he] at hs
  simp only [zero_pow (by decide : (2:ℕ)≠0),quadraticChar_zero,add_zero,
    Finset.card_erase_of_mem (Finset.mem_univ (0:F)),Finset.card_univ] at hs
  rw [←hs,Nat.cast_sub (Nat.le_of_lt Fintype.one_lt_card),Nat.cast_one]

/-- Literal norm representations of zero, valid in both split and inert
odd-characteristic cases, including the origin. -/
theorem norm_zero (hF : ringChar F≠2) :
    (Nat.card (NormFiber (0:F)):ℤ)=(Fintype.card F:ℤ)+
      ((Fintype.card F:ℤ)-1)*quadraticChar F (-1:F) := by
  rw [norm_character_formula hF]
  have hs : (∑ x : F, quadraticChar F (0-x^2))=
      quadraticChar F (-1:F)*(∑ x : F,quadraticChar F (x^2)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [show (0:F)-x^2=(-1:F)*x^2 by ring,map_mul]
  rw [hs,square_character_sum]
  ring

/-- Every nonzero norm has exactly q−chi(−1) literal representations.
This establishes the actual first local-sieve fiber input. -/
theorem norm_nonzero (hF : ringChar F≠2) (h2 : (2:F)≠0)
    (t : F) (ht : t≠0) :
    (Nat.card (NormFiber t):ℤ)=(Fintype.card F:ℤ)-quadraticChar F (-1:F) := by
  rw [norm_character_formula hF]
  have hs : (∑ x : F, quadraticChar F (t-x^2))=
      quadraticChar F (-1:F)*(∑ x : F,quadraticChar F (x^2-t)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [show t-x^2=(-1:F)*(x^2-t) by ring,map_mul]
  rw [hs,difference_character_sum hF h2 t ht]
  ring


@[expose] def NormDifference (s : F) :=
  {z : (F×F)×(F×F) // z.1.1^2+z.1.2^2-(z.2.1^2+z.2.2^2)=s}

@[expose] def normDifferenceFibers (s : F) :
    NormDifference s ≃ (Σ t : F, NormFiber t × NormFiber (t-s)) where
  toFun z := ⟨z.1.1.1^2+z.1.1.2^2,
    ⟨z.1.1,rfl⟩,⟨z.1.2,by linear_combination -z.2⟩⟩
  invFun z := ⟨(z.2.1.1,z.2.2.1),by linear_combination z.2.1.2-z.2.2.2⟩
  left_inv z := by cases z; rfl
  right_inv z := by
    rcases z with ⟨t,⟨a,ha⟩,⟨b,hb⟩⟩
    cases ha
    rfl

lemma norm_indicator (hF : ringChar F≠2) (h2 : (2:F)≠0) (t : F) :
    (Nat.card (NormFiber t):ℤ)=(Fintype.card F:ℤ)-quadraticChar F (-1:F)+
      if t=0 then (Fintype.card F:ℤ)*quadraticChar F (-1:F) else 0 := by
  by_cases ht : t=0
  · subst t
    rw [norm_zero hF,if_pos rfl]
    ring
  · rw [norm_nonzero hF h2 t ht,if_neg ht,add_zero]

lemma sum_two_indicators (A B : ℤ) (s : F) :
    (∑ t : F, (A+if t=0 then B else 0)*(A+if t-s=0 then B else 0))=
      (Fintype.card F:ℤ)*A^2+2*A*B+(if s=0 then B^2 else 0) := by
  classical
  have he (t : F) : (A+if t=0 then B else 0)*(A+if t-s=0 then B else 0)=
      A^2+(if t=0 then A*B else 0)+(if t=s then A*B else 0)+
      (if t=0 ∧ t=s then B^2 else 0) := by
    have hSub : (if t-s=0 then B else 0)=(if t=s then B else 0) := by
      by_cases eq : t=s
      · rw [if_pos (sub_eq_zero.mpr eq),if_pos eq]
      · rw [if_neg (fun e => eq (sub_eq_zero.mp e)),if_neg eq]
    rw [hSub]
    by_cases h0 : t=0
    · by_cases hs : t=s
      · simp only [if_pos h0,if_pos hs,if_pos (And.intro h0 hs)] <;> ring
      · have hn : ¬(t=0 ∧ t=s) := fun h => hs h.2
        simp only [if_pos h0,if_neg hs,if_neg hn] <;> ring
    · have hn : ¬(t=0 ∧ t=s) := fun h => h0 h.1
      by_cases hs : t=s
      · simp only [if_neg h0,if_pos hs,if_neg hn] <;> ring
      · simp only [if_neg h0,if_neg hs,if_neg hn] <;> ring
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,Finset.sum_add_distrib]
  by_cases hs : s=0
  · subst s
    simp only [and_self,if_pos rfl]
    simp
    <;> ring
  · have hz : ∑ t : F, (if t=0 ∧ t=s then B^2 else 0)=0 := by
      apply Finset.sum_eq_zero
      intro t ht
      have he : ¬(t=0 ∧ t=s) := by rintro ⟨h0,h1⟩; exact hs (h1.symm.trans h0)
      rw [if_neg he]
    rw [hz,if_neg hs]
    simp
    <;> ring

/-- Count every literal pair of norm fibers, retaining the zero difference. -/
theorem difference_count (hF : ringChar F≠2) (h2 : (2:F)≠0) (s : F) :
    (Nat.card (NormDifference s):ℤ)=(Fintype.card F:ℤ)^3-(Fintype.card F:ℤ)+
      if s=0 then (Fintype.card F:ℤ)^2 else 0 := by
  classical
  have hc : (Nat.card (NormDifference s):ℤ)=
      ∑ t : F, (Nat.card (NormFiber t):ℤ)*(Nat.card (NormFiber (t-s)):ℤ) := by
    have hFinite (u : F) : Finite (NormFiber u) :=
      Finite.of_injective (fun z : NormFiber u => z.val) (fun z w e => Subtype.ext e)
    letI : ∀ t : F, Finite (NormFiber t × NormFiber (t-s)) := fun t =>
      letI := hFinite t
      letI := hFinite (t-s)
      inferInstance
    rw [Nat.card_congr (normDifferenceFibers s),Nat.card_sigma,Nat.cast_sum] <;>
      simp only [Nat.card_prod,Nat.cast_mul]
  rw [hc]
  simp_rw [norm_indicator hF h2]
  rw [sum_two_indicators]
  have he : (quadraticChar F (-1:F))^2=1 := quadraticChar_sq_one (neg_ne_zero.mpr one_ne_zero)
  have ha : (Fintype.card F:ℤ)*((Fintype.card F:ℤ)-quadraticChar F (-1:F))^2+
      2*((Fintype.card F:ℤ)-quadraticChar F (-1:F))*
        ((Fintype.card F:ℤ)*quadraticChar F (-1:F))=
      (Fintype.card F:ℤ)^3-(Fintype.card F:ℤ) := by
    calc
      _ = (Fintype.card F:ℤ)^3-(Fintype.card F:ℤ)*(quadraticChar F (-1:F))^2 := by ring
      _ = _ := by rw [he,mul_one]
  rw [ha,mul_pow,he,mul_one]


end ActualA4FieldNormCount318
