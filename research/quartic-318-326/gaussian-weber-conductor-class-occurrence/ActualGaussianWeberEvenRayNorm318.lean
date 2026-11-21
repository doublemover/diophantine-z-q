module
public import ActualGaussianWeberEvenNormLift318
public import ActualGaussianResidueOrbit318
public section

namespace ActualGaussianWeberEvenRayNorm318

open ActualGaussianResidueOrbit318 ActualGaussianWeberEvenNormLift318

/-- The actual Gaussian norm of a full-level class lifts to twice the
even level. These are the same Gaussian ideal and the same residues. -/
theorem reduce_norm_twice {M : ℕ} (hM : Even M) {a b : GaussianInt}
    (h : red M a=red M b) :
    2*(M:ℤ) ∣ a.norm-b.norm := by
  have hE : Even (M:ℤ) := by
    obtain ⟨k,hk⟩ := hM
    exact ⟨(k:ℤ),by exact_mod_cast hk⟩
  have hc := full_coordinate_congruence (M:=M) h
  have hR : (M:ℤ)∣a.re-b.re := Int.dvd_neg.mp (by
    have e : -(a.re-b.re)=b.re-a.re := by ring
    rw [e]
    exact hc.1.dvd)
  have hI : (M:ℤ)∣a.im-b.im := Int.dvd_neg.mp (by
    have e : -(a.im-b.im)=b.im-a.im := by ring
    rw [e]
    exact hc.2.dvd)
  simpa only [norm_coords,coords] using norm_even_congr (M:ℤ) a.re a.im b.re b.im hE hR hI

/-- Exact norm-one congruence forced by the identity Gaussian ray
Frobenius tag. Gaussian representatives can differ by a genuine
global unit, without changing the norm modulo twice the level. -/
theorem prime_norm_one_mod_twice {M p : ℕ} (hM : Even M) {π : GaussianInt}
    (hp : π.norm=(p:ℤ))
    (hClass : ∃ e : GaussianIntˣ, red M π=red M (e:GaussianInt)) :
    2*(M:ℤ) ∣ (p:ℤ)-1 := by
  obtain ⟨e,he⟩ := hClass
  have hn : (e:GaussianInt).norm=1 :=
    (Zsqrtd.norm_eq_one_iff' (by norm_num : (-1:ℤ)≤0) (e:GaussianInt)).mpr e.isUnit
  have h := reduce_norm_twice hM he
  rw [hp,hn] at h
  exact h

/-- The norm residue is unchanged by a global unit or conjugation;
this exercises exactly the equivalence used for a full absolute class. -/
theorem embedded_norm_ratio_invariant {M : ℕ} (hM : Even M) {π γ : GaussianInt}
    (e : GaussianIntˣ) (h : red M π=red M ((e:GaussianInt)*γ)) :
    2*(M:ℤ) ∣ π.norm-γ.norm := by
  have hn : (e:GaussianInt).norm=1 :=
    (Zsqrtd.norm_eq_one_iff' (by norm_num : (-1:ℤ)≤0) (e:GaussianInt)).mpr e.isUnit
  have q := reduce_norm_twice hM h
  simpa only [Zsqrtd.norm_mul,hn,one_mul] using q

end ActualGaussianWeberEvenRayNorm318
