module
public import GlobalDualSquare318
public import GlobalNormCoset318
public section
namespace UnitSquareclasses318
open ConcreteG8Domain EuclideanSqrtTwo318 FractionSqrtTwo318
set_option maxHeartbeats 0
noncomputable section

@[expose] def epsilon:Oˣ where
  val:=⟨1,1⟩
  inv:=⟨-1,1⟩
  val_inv:=by ext <;> norm_num [Zsqrtd.re_mul,Zsqrtd.im_mul]
  inv_val:=by ext <;> norm_num [Zsqrtd.re_mul,Zsqrtd.im_mul]

theorem epsilon_map : toK (epsilon:O)=pair 1 1 := rfl

theorem norm_one_signed_square (u:O) (hn:u.norm=1) :
    ∃k:K,toK u=k^2 ∨ toK u= -k^2 := by
  have he:u.re^2-2*u.im^2=1 := by simpa [Zsqrtd.norm_def,pow_two,mul_assoc] using hn
  have ha:u.re≠0 := by intro hh; rw [hh] at he; nlinarith [sq_nonneg u.im]
  rcases lt_or_gt_of_ne ha with hneg|hpos
  · have he':(-u.re)^2-2*(-u.im)^2=1 := by simpa only [neg_sq] using he
    obtain ⟨k,hk⟩:=PositiveUnitSquare318.pell_positive_square (Pell.Solution₁.mk (-u.re) (-u.im) he') (by simpa using neg_pos.mpr hneg)
    refine ⟨k,Or.inr ?_⟩
    change k^2=pair ((-u.re:ℤ):ℚ) ((-u.im:ℤ):ℚ) at hk
    rw [hk]
    ext <;> simp [toK_pair,pair]
  · obtain ⟨k,hk⟩:=PositiveUnitSquare318.pell_positive_square (Pell.Solution₁.mk u.re u.im he) hpos
    exact ⟨k,Or.inl hk.symm⟩

/-- All four actual unit squareclasses, with no unit-group input. -/
theorem unit_four_classes (u:Oˣ) :
    ∃k:K,k≠0 ∧ (toK (u:O)=k^2 ∨ toK (u:O)= -k^2 ∨
      toK (u:O)=pair 1 1*k^2 ∨ toK (u:O)= -(pair 1 1)*k^2) := by
  have hn:=Int.isUnit_iff_abs_eq.mp ((Zsqrtd.isUnit_iff_norm_isUnit (u:O)).mp u.isUnit)
  have hnorm:(u:O).norm=1 ∨ (u:O).norm= -1 := (abs_eq (by norm_num)).mp hn
  have hu0:toK (u:O)≠0:=(u.isUnit.map toK).ne_zero
  rcases hnorm with hn|hn
  · obtain ⟨k,hk|hk⟩:=norm_one_signed_square (u:O) hn
    · refine ⟨k,?_,Or.inl hk⟩
      intro hz; rw [hz,zero_pow (by decide)] at hk; exact hu0 hk
    · refine ⟨k,?_,Or.inr (Or.inl hk)⟩
      intro hz; rw [hz,zero_pow (by decide),neg_zero] at hk; exact hu0 hk
  · let v:Oˣ:=u*epsilon⁻¹
    have hv:(v:O).norm=1 := by
      change Zsqrtd.norm ((u:O)*(↑(epsilon⁻¹):O))=1
      rw [Zsqrtd.norm_mul,hn]
      norm_num [epsilon,Zsqrtd.norm_def]
    have hmul:toK (u:O)=pair 1 1*toK (v:O) := by
      rw [←epsilon_map,←map_mul]
      congr 1
      dsimp only [v]
      simp only [Units.val_mul,←mul_assoc]
      rw [mul_comm (epsilon:O) (u:O),mul_assoc,Units.mul_inv,mul_one]
    obtain ⟨k,hk|hk⟩:=norm_one_signed_square (v:O) hv
    · have h:toK (u:O)=pair 1 1*k^2 := by rw [hmul,hk]
      refine ⟨k,?_,Or.inr (Or.inr (Or.inl h))⟩
      intro hz; rw [hz,zero_pow (by decide),mul_zero] at h; exact hu0 h
    · have h:toK (u:O)= -(pair 1 1)*k^2 := by rw [hmul,hk]; ring
      refine ⟨k,?_,Or.inr (Or.inr (Or.inr h))⟩
      intro hz; rw [hz,zero_pow (by decide),mul_zero] at h; exact hu0 h

end
end UnitSquareclasses318
#print axioms UnitSquareclasses318.unit_four_classes
