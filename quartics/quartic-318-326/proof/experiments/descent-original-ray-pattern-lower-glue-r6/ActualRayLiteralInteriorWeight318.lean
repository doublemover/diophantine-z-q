module
public import OriginalInteriorTelescoping318
public import ActualRayInteriorBox318
public import ActualRayConductorRows318
import all OriginalInteriorTelescoping318
public section
noncomputable section
namespace ActualRayLiteralInteriorWeight318

open scoped BigOperators
open OriginalInteriorTelescoping318 ActualRayConductorRows318

@[expose] def physicalU (r : Row) (x : ℤ) : ℤ := (r.W:ℤ)*x+r.b
@[expose] def physicalV (r : Row) (m : ℤ) : ℤ := (r.W:ℤ)*m+r.c
@[expose] def physicalUOriginal (r : Row) (x m : ℤ) : ℤ :=
  physicalU r x-r.K*(physicalV r m)^2
@[expose] def physicalPrime (r : Row) (i : ℕ) (x m : ℤ) : ℤ :=
  physicalUOriginal r x m+r.ci i*(physicalV r m)^2

theorem folded_original_value (u v q c : ℤ) :
    u+(q^2*c)*v^2=u+c*(q*v)^2 := by ring

theorem physical_shear (r : Row) (i : ℕ) (x m : ℤ) :
    physicalPrime r i x m=physicalU r x+d r i*(physicalV r m)^2 := by
  simp only [physicalPrime,physicalUOriginal,d]
  ring

theorem residue_gap_divides (r : Row) (i : ℕ) :
    (r.W:ℤ)∣r.b+d r i*r.c^2-residue r i := by
  let A := r.b+d r i*r.c^2-1
  refine ⟨A/(r.W:ℤ),?_⟩
  have h := Int.mul_ediv_add_emod A (r.W:ℤ)
  dsimp only [residue,A] at h ⊢
  linear_combination -h

/-- Exact true integer output of the row polynomial. No positive
value, primality, or wrapped representative is assumed here. -/
theorem true_w_lift (r : Row) (i : ℕ) (x m : ℤ) :
    (r.W:ℤ)*(x+shift r i m)+residue r i=physicalPrime r i x m := by
  have hk := Int.mul_ediv_cancel_of_dvd (residue_gap_divides r i)
  rw [physical_shear]
  exact ActualRayInteriorBox318.lift hk

theorem rep_no_wrap (n : ℕ) (x : ℤ) (hx : 1≤x) (hxn : x≤(n:ℤ)) :
    rep n x=x := by
  unfold rep
  rw [Int.emod_eq_of_lt (show 0≤x-1 by omega) (show x-1<(n:ℤ) by omega)]
  omega

@[expose] def baseIndex (r : Row) (z : Dom r) : ℤ := (z.1.val:ℤ)+1
@[expose] def stepIndex (r : Row) (z : Dom r) : ℤ := (z.2.val:ℤ)+1
@[expose] def noWrap (r : Row) (i : ℕ) (z : Dom r) : Prop :=
  1≤baseIndex r z+shift r i (stepIndex r z) ∧
  baseIndex r z+shift r i (stepIndex r z)≤(r.n:ℤ)

theorem residue_bounds (r : Row) (i : ℕ) (hW : 0<r.W) :
    (1:ℤ)≤residue r i ∧ residue r i≤(r.W:ℤ) := by
  have hW' : (0:ℤ)<(r.W:ℤ) := by exact_mod_cast hW
  have h0 := Int.emod_nonneg (r.b+d r i*r.c^2-1) hW'.ne'
  have h1 := Int.emod_lt_of_pos (r.b+d r i*r.c^2-1) hW'
  unfold residue
  omega

/-- A true physical-prime window forces both no wrapping and passage
of the truncation. The nonlinear donor never needs a boundary count. -/
theorem output_window_implies_no_wrap (r : Row) (i : ℕ) (z : Dom r)
    (hW : 0<r.W)
    (hlo : (r.W:ℤ)<physicalPrime r i (baseIndex r z) (stepIndex r z))
    (hhi : physicalPrime r i (baseIndex r z) (stepIndex r z)≤(r.W:ℤ)*((r.n:ℤ)+1))
    (hcut : (r.W:ℤ)*(r.cut:ℤ)<physicalPrime r i (baseIndex r z) (stepIndex r z)) :
    noWrap r i z ∧ (r.cut:ℤ)≤baseIndex r z+shift r i (stepIndex r z) := by
  let y := baseIndex r z+shift r i (stepIndex r z)
  have hW' : (0:ℤ)<(r.W:ℤ) := by exact_mod_cast hW
  have hB := residue_bounds r i hW
  have hL : (r.W:ℤ)*y+residue r i=physicalPrime r i (baseIndex r z) (stepIndex r z) :=
    true_w_lift r i (baseIndex r z) (stepIndex r z)
  constructor
  · change 1≤y ∧ y≤(r.n:ℤ)
    constructor
    · by_contra h
      have hz : y≤0 := by omega
      have hm := mul_nonpos_of_nonneg_of_nonpos hW'.le hz
      omega
    · by_contra h
      have hz : (r.n:ℤ)+1≤y := by omega
      have hm := mul_le_mul_of_nonneg_left hz hW'.le
      omega
  · change (r.cut:ℤ)≤y
    by_contra h
    have hz : y+1≤(r.cut:ℤ) := by omega
    have hm := mul_le_mul_of_nonneg_left hz hW'.le
    rw [mul_add,mul_one] at hm
    omega

theorem arg_exact (r : Row) (i : ℕ) (z : Dom r) (h : noWrap r i z) :
    arg r i z=baseIndex r z+shift r i (stepIndex r z) :=
  rep_no_wrap r.n _ h.1 h.2

theorem output_exact (r : Row) (i : ℕ) (z : Dom r) (h : noWrap r i z) :
    val r i z=physicalPrime r i (baseIndex r z) (stepIndex r z) := by
  unfold val
  rw [arg_exact r i z h]
  exact true_w_lift r i _ _

theorem prime_factor_exact (r : Row) (i : ℕ) (z : Dom r) (h : noWrap r i z)
    (hc : (r.cut:ℤ)≤baseIndex r z+shift r i (stepIndex r z)) :
    f r i z=r.phiRatio*logPrimeRay r.ray
      (physicalPrime r i (baseIndex r z) (stepIndex r z)) := by
  simp only [f,arg_exact r i z h,if_pos hc,output_exact r i z h]

theorem prime_product_exact (r : Row) (z : Dom r)
    (h : ∀ i<r.k, noWrap r i z)
    (hc : ∀ i<r.k, (r.cut:ℤ)≤baseIndex r z+shift r i (stepIndex r z)) :
    (∏ i∈Finset.range r.k, f r i z)=r.phiRatio^r.k*
      ∏ i∈Finset.range r.k, logPrimeRay r.ray
        (physicalPrime r i (baseIndex r z) (stepIndex r z)) := by
  calc
    _ = ∏ i∈Finset.range r.k, r.phiRatio*logPrimeRay r.ray
        (physicalPrime r i (baseIndex r z) (stepIndex r z)) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact prime_factor_exact r i z (h i (Finset.mem_range.mp hi))
        (hc i (Finset.mem_range.mp hi))
    _ = _ := by simp [Finset.prod_mul_distrib]

/-- Same physical residue digit; z0 is b−1 for the positive base
coordinate and c for the zero-based step coordinate. No bound on the
integer block indices is required for uniqueness. -/
theorem unique_digit {W b b' x x' : ℕ} (hW : 0<W) (hb : b<W) (hb' : b'<W)
    (h : b+W*x=b'+W*x') : b=b' ∧ x=x' := by
  have hr := congrArg (fun t : ℕ => t%W) h
  have hq := congrArg (fun t : ℕ => t/W) h
  change (b+W*x)%W=(b'+W*x')%W at hr
  change (b+W*x)/W=(b'+W*x')/W at hq
  exact ⟨by simpa only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hb,Nat.mod_eq_of_lt hb'] using hr,
    by simpa only [Nat.add_mul_div_left _ _ hW,Nat.div_eq_of_lt hb,Nat.div_eq_of_lt hb',zero_add] using hq⟩

/-- Truth on the sheared box projects injectively to the original
u,v keys. Positive b=W is retained, not dropped as a nonunit dummy. -/
theorem unique_original_pair (W : ℕ) (hW : 0<W) (K : ℤ)
    (b c b' c' : Fin W) (x m x' m' : ℕ)
    (h : (((b.val+1+W*x:ℕ):ℤ)-K*((c.val+W*m:ℕ):ℤ)^2,(c.val+W*m:ℕ)) =
         (((b'.val+1+W*x':ℕ):ℤ)-K*((c'.val+W*m':ℕ):ℤ)^2,(c'.val+W*m':ℕ))) :
    b=b' ∧ c=c' ∧ x=x' ∧ m=m' := by
  have hv := congrArg Prod.snd h
  have hu := congrArg Prod.fst h
  change c.val+W*m=c'.val+W*m' at hv
  change (((b.val+1+W*x:ℕ):ℤ)-K*((c.val+W*m:ℕ):ℤ)^2) =
    (((b'.val+1+W*x':ℕ):ℤ)-K*((c'.val+W*m':ℕ):ℤ)^2) at hu
  have hv' : ((c.val+W*m:ℕ):ℤ)=((c'.val+W*m':ℕ):ℤ) := by exact_mod_cast hv
  rw [hv'] at hu
  have hCancel := congrArg (fun t : ℤ => t+K*((c'.val+W*m':ℕ):ℤ)^2) hu
  have hSigned : ((b.val+1+W*x:ℕ):ℤ)=((b'.val+1+W*x':ℕ):ℤ) := by
    simpa only [sub_add_cancel] using hCancel
  have hu' : b.val+1+W*x=b'.val+1+W*x' := by exact_mod_cast hSigned
  have hu'' : b.val+W*x=b'.val+W*x' := by omega
  obtain ⟨hb,hx⟩ := unique_digit hW b.isLt b'.isLt hu''
  obtain ⟨hc,hm⟩ := unique_digit hW c.isLt c'.isLt hv
  exact ⟨Fin.ext hb,Fin.ext hc,hx,hm⟩

/-- Physical all-means table on one complete conductor cell, with
negative quadratic coefficients treated in the integer residue ring. -/
@[expose] def table (F k : ℕ) (d : ℕ→ℤ) (μ : ℤ→ℝ) (U v : ℕ) : ℝ :=
  ∏ i∈Finset.range k, μ (((U:ℤ)+d i*(v:ℤ)^2)%(F:ℤ))

theorem table_bounds (F k : ℕ) (d : ℕ→ℤ) (μ : ℤ→ℝ)
    (hμ : ∀ a, 0≤μ a ∧ μ a≤1) (U v : ℕ) :
    0≤table F k d μ U v ∧ table F k d μ U v≤1 := by
  unfold table
  constructor
  · exact Finset.prod_nonneg fun i _ => (hμ _).1
  · simpa only [Finset.prod_const_one] using
      (Finset.prod_le_prod₀ (fun i (_ : i∈Finset.range k) => (hμ (((U:ℤ)+d i*(v:ℤ)^2)%(F:ℤ))).1)
        (fun i _ => (hμ (((U:ℤ)+d i*(v:ℤ)^2)%(F:ℤ))).2))

theorem table_mod (F k : ℕ) (d : ℕ→ℤ) (μ : ℤ→ℝ) (U v : ℕ) :
    table F k d μ (U%F) (v%F)=table F k d μ U v := by
  have hw (n : ℕ) : (((n%F:ℕ):ℤ)) ≡ (n:ℤ) [ZMOD (F:ℤ)] := by
    change (((n%F:ℕ):ℤ))%(F:ℤ)=(n:ℤ)%(F:ℤ)
    rw [←Int.ofNat_mod_ofNat,Int.emod_emod]
  unfold table
  apply Finset.prod_congr rfl
  intro i _
  have H := (hw U).add (Int.ModEq.mul_left (d i) ((hw v).pow 2))
  exact congrArg μ H

theorem actual_fold (F k : ℕ) (d : ℕ→ℤ) (μ : ℤ→ℝ) (W b c x m : ℕ) :
    fold (table F k d μ) F W b c x m=table F k d μ (b+W*x) (c+W*m) :=
  table_mod F k d μ _ _

end ActualRayLiteralInteriorWeight318
