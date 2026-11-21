module
public import ActualA4ShortProduct318
public import ActualTZResidueIntervalCount318
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Fin
public section
noncomputable section
namespace ActualA4IntegerBoxFibres318
open scoped BigOperators
open Classical
open ActualTZResidueIntervalCount318 ActualA4ShortProduct318

abbrev Vec (R : Type*) := Fin 4 → R
abbrev Digit (B : ℕ) := Fin (2*B+1)

@[expose] def coordinate (B : ℕ) (i : Digit B) : ℤ := -(B:ℤ)+(i.val:ℤ)

@[expose] def residue (m B : ℕ) (x : Vec (Digit B)) : Vec (ZMod m) :=
  fun i => (coordinate B (x i):ZMod m)

@[expose] def axis (m B : ℕ) (r : ZMod m) : Finset (Digit B) :=
  Finset.univ.filter (fun i => (coordinate B i:ZMod m)=r)

@[expose] def fibre (m B : ℕ) (r : Vec (ZMod m)) : Finset (Vec (Digit B)) :=
  Finset.univ.filter (fun x => residue m B x=r)

@[expose] def accepted (m B : ℕ) (Ω : Finset (Vec (ZMod m))) : Finset (Vec (Digit B)) :=
  Finset.univ.filter (fun x => residue m B x ∈ Ω)

theorem axis_card (m B : ℕ) [NeZero m] (r : ZMod m) :
    (axis m B r).card = intHits m (2*B+1) (-(B:ℤ)) (r.val:ℤ) := by
  classical
  have hR : ((r.val:ℤ):ZMod m)=r := by
    rw [Int.cast_natCast,ZMod.natCast_zmod_val]
  have hc (i : Digit B) : (coordinate B i:ZMod m)=r ↔
      Int.ModEq (m:ℤ) (-(B:ℤ)+(i.val:ℤ)) (r.val:ℤ) := by
    calc
      _ ↔ (coordinate B i:ZMod m)=((r.val:ℤ):ZMod m) := by rw [hR]
      _ ↔ _ := ZMod.intCast_eq_intCast_iff _ _ m
  let F : ℕ → ℕ := fun i =>
    if Int.ModEq (m:ℤ) (-(B:ℤ)+(i:ℤ)) (r.val:ℤ) then 1 else 0
  calc
    _ = ∑ _ ∈ axis m B r, (1:ℕ) := by simp
    _ = ∑ i : Digit B, F i.val := by
      simp only [axis,Finset.sum_filter,hc,F]
    _ = _ := Fin.sum_univ_eq_sum_range F (2*B+1)

private def fibreEquiv (m B : ℕ) (r : Vec (ZMod m)) :
    ↥(fibre m B r) ≃ ((i : Fin 4) → ↥(axis m B (r i))) where
  toFun x i := ⟨x.val i,Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,congrFun (Finset.mem_filter.mp x.prop).2 i⟩⟩
  invFun f := ⟨fun i => (f i).val,Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,funext (fun i => (Finset.mem_filter.mp (f i).prop).2)⟩⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv f := by
    funext i
    apply Subtype.ext
    rfl

theorem fibre_card (m B : ℕ) (r : Vec (ZMod m)) :
    (fibre m B r).card = ∏ i : Fin 4, (axis m B (r i)).card := by
  rw [←Fintype.card_coe,Fintype.card_congr (fibreEquiv m B r),Fintype.card_pi]
  simp only [Fintype.card_coe]

theorem accepted_card (m B : ℕ) (Ω : Finset (Vec (ZMod m))) :
    (accepted m B Ω).card=∑ r ∈ Ω, (fibre m B r).card := by
  let A := accepted m B Ω
  have hmap : ∀ x ∈ A, residue m B x ∈ Ω :=
    fun x hx => (Finset.mem_filter.mp hx).2
  calc
    _ = ∑ _ ∈ A, (1:ℕ) := by simp [A]
    _ = ∑ r ∈ Ω, ∑ _ ∈ A.filter (fun x => residue m B x=r), (1:ℕ) :=
      (Finset.sum_fiberwise_of_maps_to hmap (fun _ => (1:ℕ))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      have h : A.filter (fun x => residue m B x=r)=fibre m B r := by
        ext x
        simp only [A,accepted,fibre,Finset.mem_filter,Finset.mem_univ,true_and]
        exact ⟨And.right,fun hx => ⟨hx.symm ▸ hr,hx⟩⟩
      rw [h]
      simp

theorem fibre_error (m B : ℕ) [NeZero m] (hm : 0 < m) (hL : m ≤ 2*B+1)
    (r : Vec (ZMod m)) :
    |((fibre m B r).card:ℝ)-(((2*B+1:ℕ):ℝ)/(m:ℝ))^4|
      ≤ 15*(((2*B+1:ℕ):ℝ)/(m:ℝ))^3 := by
  let u : ℝ := ((2*B+1:ℕ):ℝ)/(m:ℝ)
  let a (i : Fin 4) := ((axis m B (r i)).card:ℝ)
  have hm' : 0 < (m:ℝ) := by exact_mod_cast hm
  have hu : 1 ≤ u := by
    change 1 ≤ ((2*B+1:ℕ):ℝ)/(m:ℝ)
    apply (le_div_iff₀ hm').2
    rw [one_mul]
    exact_mod_cast hL
  have he (i : Fin 4) : |a i-u| ≤ 1 := by
    dsimp only [a,u]
    rw [axis_card]
    exact int_count_error m (2*B+1) (-(B:ℤ)) ((r i).val:ℤ) hm
  have hnn (i : Fin 4) : 0 ≤ a i := Nat.cast_nonneg _
  rw [fibre_card,Nat.cast_prod,Fin.prod_univ_four]
  exact product_error u (a 0) (a 1) (a 2) (a 3) hu (hnn _) (hnn _) (hnn _) (hnn _)
    (he _) (he _) (he _) (he _)

/-- The weighted box shape used in the sieve: one common exact residue
mask, arbitrary on the four coordinates, and signed floor/carry error. -/
theorem mask_error (m B : ℕ) [NeZero m] (hm : 0 < m) (hL : m ≤ 2*B+1)
    (Ω : Finset (Vec (ZMod m))) :
    |((accepted m B Ω).card:ℝ)-(Ω.card:ℝ)*(((2*B+1:ℕ):ℝ)/(m:ℝ))^4|
      ≤ (Ω.card:ℝ)*(15*(((2*B+1:ℕ):ℝ)/(m:ℝ))^3) := by
  let u : ℝ := ((2*B+1:ℕ):ℝ)/(m:ℝ)
  rw [accepted_card,Nat.cast_sum]
  change |(∑ r ∈ Ω, ((fibre m B r).card:ℝ))-(Ω.card:ℝ)*u^4| ≤ _
  have hs : (∑ _ ∈ Ω, u^4)=(Ω.card:ℝ)*u^4 := by
    simp only [Finset.sum_const,nsmul_eq_mul]
  rw [←hs,←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ r ∈ Ω, |((fibre m B r).card:ℝ)-u^4| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ ∈ Ω, 15*u^3 := Finset.sum_le_sum (fun r _ => fibre_error m B hm hL r)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul] <;> rfl

end ActualA4IntegerBoxFibres318
