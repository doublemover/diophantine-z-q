module
public import LegendrePadicPrimitiveResidues318
public section
namespace LegendrePadicResidueDepth318

/-- Positive-depth generalization of the checked p-squared residue extraction.
In particular p=2,k=4 supplies the actual primitive mod16 data needed by
the even-valuation local norm tables. No new integrality premise is added. -/
theorem primitive_residues (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 0<k)
    (a b : ℤ) (x z w : ℤ_[p])
    (hsol : z^2-(a:ℤ_[p])*x^2-(b:ℤ_[p])*w^2=0)
    (hprim : ¬((p:ℤ_[p])∣x ∧ (p:ℤ_[p])∣z ∧ (p:ℤ_[p])∣w)) :
    ∃ X Z W : ℤ, (p:ℤ)^k ∣ Z^2-a*X^2-b*W^2 ∧
      ¬((p:ℤ)∣X ∧ (p:ℤ)∣Z ∧ (p:ℤ)∣W) := by
  let rep : ℤ_[p] → ℤ := fun q => q.appr k
  have hmap (q : ℤ_[p]) :
      PadicInt.toZModPow k q = ((rep q : ℤ) : ZMod (p^k)) := by
    simp only [rep,Int.cast_natCast,PadicInt.toZModPow,PadicInt.toZModHom,
      RingHom.coe_mk] <;> rfl
  have hdiv (q : ℤ_[p]) (hq : (p:ℤ)∣rep q) : (p:ℤ_[p])∣q := by
    have hd : (p:ℤ_[p])^k ∣ q-(rep q:ℤ_[p]) := by
      simpa only [rep,Int.cast_natCast,Ideal.mem_span_singleton] using
        PadicInt.appr_spec k q
    have hd' : (p:ℤ_[p]) ∣ q-(rep q:ℤ_[p]) :=
      dvd_trans (dvd_pow_self _ (Nat.ne_of_gt hk)) hd
    have hc : (p:ℤ_[p]) ∣ (rep q:ℤ_[p]) := by
      obtain ⟨c,hc⟩ := hq
      refine ⟨(c:ℤ_[p]),?_⟩
      simpa only [Int.cast_mul,Int.cast_natCast] using
        congrArg (fun n : ℤ => (n : ℤ_[p])) hc
    simpa only [sub_add_cancel] using dvd_add hd' hc
  refine ⟨rep x,rep z,rep w,?_,?_⟩
  · rw [←Nat.cast_pow]
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p^k)).mp
    have hh := congrArg (PadicInt.toZModPow (p:=p) k) hsol
    simp only [map_sub,map_mul,map_pow,map_intCast,map_zero] at hh
    simpa only [hmap,Int.cast_sub,Int.cast_mul,Int.cast_pow] using hh
  · rintro ⟨hx,hz,hw⟩
    exact hprim ⟨hdiv x hx,hdiv z hz,hdiv w hw⟩

/-- A nonzero homogeneous p-adic solution yields primitive integer
residues modulo any positive power of p, without an extra integrality assumption. -/
theorem residues_of_local_solution (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 0<k)
    (a b : ℤ) (x z w : ℚ_[p])
    (hne : ¬(x=0 ∧ z=0 ∧ w=0))
    (hsol : z^2-(a:ℚ_[p])*x^2-(b:ℚ_[p])*w^2=0) :
    ∃ X Z W : ℤ, (p:ℤ)^k ∣ Z^2-a*X^2-b*W^2 ∧
      ¬((p:ℤ)∣X ∧ (p:ℤ)∣Z ∧ (p:ℤ)∣W) := by
  obtain ⟨X,Z,W,h,hprim⟩ := LegendrePadicPrimitiveResidues318.primitive_integral_solution p a b x z w hne hsol
  exact primitive_residues p k hk a b X Z W h hprim


end LegendrePadicResidueDepth318
