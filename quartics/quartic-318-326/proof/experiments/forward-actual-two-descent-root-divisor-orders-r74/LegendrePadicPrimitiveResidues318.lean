module
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Tactic
public section
namespace LegendrePadicPrimitiveResidues318

/-- Scaling a nonzero local homogeneous solution by a largest coordinate
makes every coordinate integral and one coordinate exactly one. -/
theorem primitive_integral_solution (p : ℕ) [Fact p.Prime]
    (a b : ℤ) (x z w : ℚ_[p])
    (hne : ¬(x=0 ∧ z=0 ∧ w=0))
    (hsol : z^2-(a:ℚ_[p])*x^2-(b:ℚ_[p])*w^2=0) :
    ∃ X Z W : ℤ_[p], Z^2-(a:ℤ_[p])*X^2-(b:ℤ_[p])*W^2=0 ∧
      ¬((p:ℤ_[p])∣X ∧ (p:ℤ_[p])∣Z ∧ (p:ℤ_[p])∣W) := by
  have hmax : ∃ q : ℚ_[p], (q=x ∨ q=z ∨ q=w) ∧
      ‖x‖≤‖q‖ ∧ ‖z‖≤‖q‖ ∧ ‖w‖≤‖q‖ := by
    by_cases hxz : ‖x‖≤‖z‖
    · by_cases hzw : ‖z‖≤‖w‖
      · exact ⟨w,Or.inr (Or.inr rfl),hxz.trans hzw,hzw,le_rfl⟩
      · exact ⟨z,Or.inr (Or.inl rfl),hxz,le_rfl,(lt_of_not_ge hzw).le⟩
    · have hzx : ‖z‖≤‖x‖ := (lt_of_not_ge hxz).le
      by_cases hxw : ‖x‖≤‖w‖
      · exact ⟨w,Or.inr (Or.inr rfl),hxw,hzx.trans hxw,le_rfl⟩
      · exact ⟨x,Or.inl rfl,le_rfl,hzx,(lt_of_not_ge hxw).le⟩
  obtain ⟨q,hq,hx,hz,hw⟩ := hmax
  have hq0 : q≠0 := by
    intro hzero
    have ht (v : ℚ_[p]) (hv : ‖v‖≤‖q‖) : v=0 := by
      apply norm_eq_zero.mp
      exact le_antisymm (by simpa [hzero] using hv) (norm_nonneg v)
    exact hne ⟨ht x hx,ht z hz,ht w hw⟩
  have hint (v : ℚ_[p]) (hv : ‖v‖≤‖q‖) : ‖v/q‖≤1 := by
    rw [norm_div]
    exact (div_le_one (norm_pos_iff.mpr hq0)).mpr hv
  let X : ℤ_[p] := ⟨x/q,hint x hx⟩
  let Z : ℤ_[p] := ⟨z/q,hint z hz⟩
  let W : ℤ_[p] := ⟨w/q,hint w hw⟩
  refine ⟨X,Z,W,?_,?_⟩
  · apply PadicInt.coe_inj.mp
    change (z/q)^2-(a:ℚ_[p])*(x/q)^2-(b:ℚ_[p])*(w/q)^2=0
    calc
      _ = (z^2-(a:ℚ_[p])*x^2-(b:ℚ_[p])*w^2)/q^2 := by ring
      _ = 0 := by rw [hsol,zero_div]
  · have hone : X=1 ∨ Z=1 ∨ W=1 := by
      rcases hq with rfl | rfl | rfl
      · exact Or.inl (PadicInt.ext (by simp [X,hq0]))
      · exact Or.inr (Or.inl (PadicInt.ext (by simp [Z,hq0])))
      · exact Or.inr (Or.inr (PadicInt.ext (by simp [W,hq0])))
    have hnot : ¬(p:ℤ_[p])∣(1:ℤ_[p]) := by
      intro hd
      have ht := (PadicInt.norm_lt_one_iff_dvd (1:ℤ_[p])).mpr hd
      simpa using ht
    rintro ⟨hX,hZ,hW⟩
    rcases hone with h | h | h
    · exact hnot (h ▸ hX)
    · exact hnot (h ▸ hZ)
    · exact hnot (h ▸ hW)

/-- Reduction of an actual primitive integral p-adic solution supplies the
integer congruence required by the modular-root descent step. -/
theorem primitive_residues (p : ℕ) [Fact p.Prime]
    (a b : ℤ) (x z w : ℤ_[p])
    (hsol : z^2-(a:ℤ_[p])*x^2-(b:ℤ_[p])*w^2=0)
    (hprim : ¬((p:ℤ_[p])∣x ∧ (p:ℤ_[p])∣z ∧ (p:ℤ_[p])∣w)) :
    ∃ X Z W : ℤ, (p:ℤ)^2 ∣ Z^2-a*X^2-b*W^2 ∧
      ¬((p:ℤ)∣X ∧ (p:ℤ)∣Z ∧ (p:ℤ)∣W) := by
  let rep : ℤ_[p] → ℤ := fun q => q.appr 2
  have hmap (q : ℤ_[p]) :
      PadicInt.toZModPow 2 q = ((rep q : ℤ) : ZMod (p^2)) := by
    rfl
  have hdiv (q : ℤ_[p]) (hq : (p:ℤ)∣rep q) : (p:ℤ_[p])∣q := by
    have hd : (p:ℤ_[p])^2 ∣ q-(rep q:ℤ_[p]) := by
      simpa only [rep,Int.cast_natCast,Ideal.mem_span_singleton] using
        PadicInt.appr_spec 2 q
    have hd' : (p:ℤ_[p]) ∣ q-(rep q:ℤ_[p]) :=
      dvd_trans (dvd_pow_self _ (by decide : 2≠0)) hd
    have hc : (p:ℤ_[p]) ∣ (rep q:ℤ_[p]) := by
      obtain ⟨c,hc⟩ := hq
      refine ⟨(c:ℤ_[p]),?_⟩
      simpa only [Int.cast_mul,Int.cast_natCast] using
        congrArg (fun n : ℤ => (n : ℤ_[p])) hc
    simpa only [sub_add_cancel] using dvd_add hd' hc
  refine ⟨rep x,rep z,rep w,?_,?_⟩
  · rw [←Nat.cast_pow]
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p^2)).mp
    have hh := congrArg (PadicInt.toZModPow (p:=p) 2) hsol
    simpa only [map_sub,map_mul,map_pow,map_intCast,map_zero,hmap,
      Int.cast_sub,Int.cast_mul,Int.cast_pow] using hh
  · rintro ⟨hx,hz,hw⟩
    exact hprim ⟨hdiv x hx,hdiv z hz,hdiv w hw⟩

/-- A nonzero homogeneous p-adic solution yields primitive integer
residues modulo p squared, without an extra integrality assumption. -/
theorem residues_of_local_solution (p : ℕ) [Fact p.Prime]
    (a b : ℤ) (x z w : ℚ_[p])
    (hne : ¬(x=0 ∧ z=0 ∧ w=0))
    (hsol : z^2-(a:ℚ_[p])*x^2-(b:ℚ_[p])*w^2=0) :
    ∃ X Z W : ℤ, (p:ℤ)^2 ∣ Z^2-a*X^2-b*W^2 ∧
      ¬((p:ℤ)∣X ∧ (p:ℤ)∣Z ∧ (p:ℤ)∣W) := by
  obtain ⟨X,Z,W,h,hprim⟩ := primitive_integral_solution p a b x z w hne hsol
  exact primitive_residues p a b X Z W h hprim

end LegendrePadicPrimitiveResidues318
