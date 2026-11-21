module
public import ActualA4FieldNormCount318
public section
noncomputable section
namespace ActualA4LinearNormCard318
open scoped BigOperators
open ActualA4FieldNormCount318
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

abbrev TwoPlanes (F : Type*) := (F×F)×(F×F)
@[expose] def norm (x : F×F) : F := x.1^2+x.2^2
@[expose] def zeroSet (a b : F) : Finset (TwoPlanes F) :=
  Finset.univ.filter (fun z => a*norm z.1+b*norm z.2=0)
@[expose] def core : Finset (TwoPlanes F) :=
  Finset.univ.filter (fun z => norm z.1=0 ∧ norm z.2=0)

theorem core_subset (a b : F) : core ⊆ zeroSet a b := by
  intro z hz
  have h := (Finset.mem_filter.mp hz).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp [h.1,h.2]⟩

/-- Any two different projective coefficient pairs meet in exactly the
common two-norm zero core. This is more precise than Bonferroni: off-core
all the masks are literally disjoint. -/
theorem common_intersection {a b c d : F} (hdet : a*d-c*b ≠ 0) :
    zeroSet a b ∩ zeroSet c d = core := by
  ext z
  simp only [Finset.mem_inter,zeroSet,core,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨h₁,h₂⟩
    have hN : (a*d-c*b)*norm z.1=0 := by linear_combination d*h₁-b*h₂
    have hM : (a*d-c*b)*norm z.2=0 := by linear_combination a*h₂-c*h₁
    exact ⟨(mul_eq_zero.mp hN).resolve_left hdet,(mul_eq_zero.mp hM).resolve_left hdet⟩
  · rintro ⟨h₁,h₂⟩
    simp [h₁,h₂]

private def planeFibre (a b : F) (hb : b ≠ 0) :
    ↥(zeroSet a b) ≃ (Σ t : F, NormFiber t × NormFiber ((-a/b)*t)) where
  toFun z := ⟨norm z.val.1, ⟨z.val.1,rfl⟩,⟨z.val.2,by
    have h := (Finset.mem_filter.mp z.prop).2
    change norm z.val.2=(-a/b)*norm z.val.1
    field_simp [hb]
    linear_combination h⟩⟩
  invFun w := ⟨(w.2.1.val,w.2.2.val),Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,by
      change a*norm w.2.1.val+b*norm w.2.2.val=0
      have h₁ : norm w.2.1.val=w.1 := w.2.1.prop
      have h₂ : norm w.2.2.val=(-a/b)*w.1 := w.2.2.prop
      rw [h₁,h₂]
      field_simp [hb]
      <;> ring⟩⟩
  left_inv z := by cases z; rfl
  right_inv z := by
    rcases z with ⟨t,⟨u,hu⟩,⟨v,hv⟩⟩
    cases hu
    rfl

private def firstFibre (a : F) (ha : a ≠ 0) :
    ↥(zeroSet a 0) ≃ ((NormFiber (0:F)) × (F×F)) where
  toFun z := (⟨z.val.1,by
    have h : a*norm z.val.1+0*norm z.val.2=0 := (Finset.mem_filter.mp z.prop).2
    rw [zero_mul,add_zero] at h
    exact (mul_eq_zero.mp h).resolve_left ha⟩,z.val.2)
  invFun z := ⟨(z.1.val,z.2),Finset.mem_filter.mpr ⟨Finset.mem_univ _,by
    have h : norm z.1.val=0 := z.1.prop
    simp [h]⟩⟩
  left_inv z := by cases z; rfl
  right_inv z := by rcases z with ⟨⟨v,hv⟩,w⟩; rfl

private def flip (a b : F) : ↥(zeroSet a b) ≃ ↥(zeroSet b a) where
  toFun z := ⟨(z.val.2,z.val.1), Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,by simpa only [add_comm] using (Finset.mem_filter.mp z.prop).2⟩⟩
  invFun z := ⟨(z.val.2,z.val.1), Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,by simpa only [add_comm] using (Finset.mem_filter.mp z.prop).2⟩⟩
  left_inv z := by cases z; rfl
  right_inv z := by cases z; rfl

private def coreProd : ↥(core : Finset (TwoPlanes F)) ≃
    NormFiber (0:F) × NormFiber (0:F) where
  toFun z := (⟨z.val.1,(Finset.mem_filter.mp z.prop).2.1⟩,⟨z.val.2,(Finset.mem_filter.mp z.prop).2.2⟩)
  invFun z := ⟨(z.1.val,z.2.val),Finset.mem_filter.mpr ⟨Finset.mem_univ _,z.1.prop,z.2.prop⟩⟩
  left_inv z := by cases z; rfl
  right_inv z := by rcases z with ⟨⟨u,hu⟩,⟨v,hv⟩⟩; rfl

private theorem natCard_finset {α : Type*} (s : Finset α) : Nat.card ↥s=s.card := by
  classical
  rw [Nat.card_eq_fintype_card,Fintype.card_coe]

theorem core_card (hF : ringChar F ≠ 2) :
    ((core : Finset (TwoPlanes F)).card:ℤ)=
      ((Fintype.card F:ℤ)+((Fintype.card F:ℤ)-1)*quadraticChar F (-1:F))^2 := by
  have hN : (core : Finset (TwoPlanes F)).card=Nat.card (NormFiber (0:F) × NormFiber (0:F)) :=
    (natCard_finset _).symm.trans (Nat.card_congr (coreProd (F:=F)))
  rw [hN,Nat.card_prod,Nat.cast_mul,norm_zero hF,pow_two]

theorem first_card (hF : ringChar F ≠ 2) (a : F) (ha : a ≠ 0) :
    ((zeroSet a 0).card:ℤ)=
      ((Fintype.card F:ℤ)+((Fintype.card F:ℤ)-1)*quadraticChar F (-1:F))*(Fintype.card F:ℤ)^2 := by
  have hN : (zeroSet a 0).card=Nat.card (NormFiber (0:F) × F × F) :=
    (natCard_finset _).symm.trans (Nat.card_congr (firstFibre a ha))
  rw [hN,Nat.card_prod,Nat.card_prod,Nat.cast_mul,Nat.cast_mul,norm_zero hF]
  simp only [Nat.card_eq_fintype_card,pow_two]

theorem second_card (hF : ringChar F ≠ 2) (b : F) (hb : b ≠ 0) :
    ((zeroSet 0 b).card:ℤ)=
      ((Fintype.card F:ℤ)+((Fintype.card F:ℤ)-1)*quadraticChar F (-1:F))*(Fintype.card F:ℤ)^2 := by
  have H := Fintype.card_congr (flip 0 b)
  simp only [Fintype.card_coe] at H
  rw [H]
  exact first_card hF b hb

theorem rank_four_card (hF : ringChar F ≠ 2) (h2 : (2:F) ≠ 0)
    (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    ((zeroSet a b).card:ℤ)=(Fintype.card F:ℤ)^3+(Fintype.card F:ℤ)^2-(Fintype.card F:ℤ) := by
  classical
  have hFinite (t : F) : Finite (NormFiber t) :=
    Finite.of_injective (fun z : NormFiber t => z.val) (fun z w e => Subtype.ext e)
  have hSum (f : F → F) :
      Nat.card (Σ t : F, NormFiber t × NormFiber (f t)) =
        ∑ t : F, Nat.card (NormFiber t)*Nat.card (NormFiber (f t)) := by
    letI : ∀ t : F, Finite (NormFiber t × NormFiber (f t)) := fun t =>
      letI := hFinite t
      letI := hFinite (f t)
      inferInstance
    rw [Nat.card_sigma] <;> simp only [Nat.card_prod]
  have hLeft : (zeroSet a b).card=Nat.card (Σ t : F, NormFiber t × NormFiber ((-a/b)*t)) :=
    (natCard_finset _).symm.trans (Nat.card_congr (planeFibre a b hb))
  have hRight := (Nat.card_congr (normDifferenceFibers (0:F))).trans (hSum (fun t => t-0))
  have hC : (zeroSet a b).card=Nat.card (NormDifference (0:F)) := by
    rw [hLeft,hSum (fun t => (-a/b)*t),hRight]
    simp only [sub_zero]
    apply Finset.sum_congr rfl
    intro t _
    congr 1
    by_cases ht : t=0
    · rw [ht,mul_zero]
    · have hAt : (-a/b)*t ≠ 0 := mul_ne_zero (div_ne_zero (neg_ne_zero.mpr ha) hb) ht
      have h : (Nat.card (NormFiber ((-a/b)*t)):ℤ)=(Nat.card (NormFiber t):ℤ) :=
        (norm_nonzero hF h2 ((-a/b)*t) hAt).trans (norm_nonzero hF h2 t ht).symm
      exact_mod_cast h
  rw [hC,difference_count hF h2]
  simp only [if_pos rfl] <;> ring


end ActualA4LinearNormCard318
