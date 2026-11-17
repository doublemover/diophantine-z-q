module
public import LegendreHomogeneousAffine318
public import LegendreNormDescentStep318
public import LegendreSquarefreeCRT318
public import LegendreCenteredRoot318
public import LegendrePrimitiveModularRoot318
public import LegendrePadicPrimitiveResidues318
public section
namespace LegendreTernaryDescent318

/-- Literal nonzero homogeneous solution, not a local-global premise. -/
def Sol (F : Type*) [Field F] (a b : F) : Prop :=
  ∃ x z w : F, ¬(x=0 ∧ z=0 ∧ w=0) ∧ z^2-a*x^2-b*w^2=0

def Everywhere (a b : ℤ) : Prop :=
  Sol ℝ a b ∧ ∀ (p : ℕ) [Fact p.Prime], Sol ℚ_[p] a b

theorem swap {F : Type*} [Field F] {a b : F}
    (h : Sol F a b) : Sol F b a := by
  obtain ⟨x,z,w,hne,he⟩ := h
  refine ⟨w,z,x,?_,?_⟩
  · rintro ⟨hw,hz,hx⟩
    exact hne ⟨hx,hz,hw⟩
  · linear_combination he

theorem swap_everywhere {a b : ℤ} (h : Everywhere a b) : Everywhere b a :=
  ⟨swap h.1,fun p _ => swap (h.2 p)⟩

theorem of_affine {F : Type*} [Field F] (a b u v : F)
    (h : u^2-a*v^2=b) : Sol F a b := by
  refine ⟨v,u,1,by simp,?_⟩
  simpa only [one_pow,mul_one] using sub_eq_zero.mpr h

theorem to_affine {F : Type*} [Field F] [CharZero F]
    {a b : F} (ha : a≠0) (h : Sol F a b) :
    ∃ u v : F, u^2-a*v^2=b := by
  obtain ⟨x,z,w,hne,he⟩ := h
  exact LegendreHomogeneousAffine318.affine_of_homogeneous a b x z w ha hne he

/-- Descent transfers actual local solutions and removes the square factor
of the new coefficient. This works uniformly at the real and every p-adic place. -/
theorem descend_at {F : Type*} [Field F] [CharZero F]
    (a b c t e d : ℤ) (ha : a≠0) (hb : b≠0) (he0 : e≠0)
    (hstep : t^2-a=b*c) (he : e^2*d=c)
    (h : Sol F (a:F) (b:F)) : Sol F (a:F) (d:F) := by
  have haF : (a:F)≠0 := by exact_mod_cast ha
  have hbF : (b:F)≠0 := by exact_mod_cast hb
  have heF0 : (e:F)≠0 := by exact_mod_cast he0
  have hstepF : (t:F)^2-(a:F)=(b:F)*(c:F) := by exact_mod_cast hstep
  have heF : (e:F)^2*(d:F)=(c:F) := by exact_mod_cast he
  obtain ⟨u,v,hu⟩ := to_affine haF h
  obtain ⟨U,V,hUV⟩ := LegendreNormDescentStep318.affine_transfer
    (a:F) (b:F) (c:F) (t:F) u v hbF hstepF hu
  refine ⟨V,U,(e:F),?_,?_⟩
  · intro hh
    exact heF0 hh.2.2
  · calc
      U^2-(a:F)*V^2-(d:F)*(e:F)^2=(c:F)-(e:F)^2*(d:F) := by rw [hUV]; ring
      _=0 := by rw [heF,sub_self]

/-- The reverse algebraic transfer constructs the global witness after
induction; the nonzero c branch is explicit. -/
theorem ascend_at {F : Type*} [Field F] [CharZero F]
    (a b c t e d : ℤ) (ha : a≠0) (hc : c≠0)
    (hstep : t^2-a=b*c) (he : e^2*d=c)
    (h : Sol F (a:F) (d:F)) : Sol F (a:F) (b:F) := by
  have haF : (a:F)≠0 := by exact_mod_cast ha
  have hcF : (c:F)≠0 := by exact_mod_cast hc
  have hstepF : (t:F)^2-(a:F)=(c:F)*(b:F) := by
    exact_mod_cast (show t^2-a=c*b by rw [hstep]; ring)
  have heF : (e:F)^2*(d:F)=(c:F) := by exact_mod_cast he
  obtain ⟨u,v,hu⟩ := to_affine haF h
  have hnorm : ((e:F)*u)^2-(a:F)*((e:F)*v)^2=(c:F) := by
    calc
      _=(e:F)^2*(u^2-(a:F)*v^2) := by ring
      _=(c:F) := by rw [hu,heF]
  obtain ⟨U,V,hUV⟩ := LegendreNormDescentStep318.affine_transfer
    (a:F) (c:F) (b:F) (t:F) ((e:F)*u) ((e:F)*v) hcF hstepF hnorm
  exact of_affine (a:F) (b:F) U V hUV

/-- All-prime local solutions construct the modular root needed for a
squarefree second coefficient, including shared coefficient primes and p=2. -/
theorem modular_root (a b : ℤ) (hb : Squarefree b) (h : Everywhere a b) :
    IsSquare (a : ZMod b.natAbs) := by
  apply LegendreSquarefreeCRT318.square_mod_squarefree a b.natAbs
    (Int.squarefree_natAbs.mpr hb)
  intro p hp hpb
  letI : Fact p.Prime := ⟨hp⟩
  have hd : (p:ℤ)∣b := by
    have hh : (p:ℤ)∣(b.natAbs:ℤ) := by exact_mod_cast hpb
    simpa only [Int.natCast_natAbs,dvd_abs] using hh
  obtain ⟨B,hB,hBp⟩ := LegendreSquarefreeCRT318.prime_factor_once b hb p hp hd
  obtain ⟨x,z,w,hne,hsol⟩ := h.2 p
  obtain ⟨X,Z,W,hcong,hprim⟩ :=
    LegendrePadicPrimitiveResidues318.residues_of_local_solution p a b x z w hne hsol
  rw [hB] at hcong
  exact LegendrePrimitiveModularRoot318.square_of_primitive_mod_square p a B X Z W
    hBp hcong hprim

/-- Ternary local-global existence for squarefree signed integer coefficients.
The proof is constructive strong descent in the sum of coefficient sizes;
no local-global principle is a premise. -/
theorem rational_of_everywhere_squarefree (a b : ℤ)
    (ha : Squarefree a) (hb : Squarefree b) (hloc : Everywhere a b) :
    Sol ℚ a b := by
  have main : ∀ n : ℕ, ∀ a b : ℤ, a.natAbs+b.natAbs=n →
      Squarefree a → Squarefree b → Everywhere a b → Sol ℚ a b := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      have ordered (a b : ℤ) (hn : a.natAbs+b.natAbs=n)
          (ha : Squarefree a) (hb : Squarefree b) (hloc : Everywhere a b)
          (hab : |a|≤|b|) : Sol ℚ a b := by
        have ha0 : a≠0 := ha.ne_zero
        have hb0 : b≠0 := hb.ne_zero
        by_cases hsmall : |b|≤1
        · have habounds := abs_le.mp (hab.trans hsmall)
          have hbbounds := abs_le.mp hsmall
          have hac : a=1 ∨ a= -1 := by omega
          have hbc : b=1 ∨ b= -1 := by omega
          rcases hac with rfl | rfl
          · exact ⟨1,1,0,by simp,by simp⟩
          · rcases hbc with rfl | rfl
            · exact ⟨0,1,1,by simp,by simp⟩
            · obtain ⟨x,z,w,hne,he⟩ := hloc.1
              norm_num at he
              have hx2 : x^2=0 := by nlinarith [sq_nonneg x,sq_nonneg z,sq_nonneg w]
              have hz2 : z^2=0 := by nlinarith [sq_nonneg x,sq_nonneg z,sq_nonneg w]
              have hw2 : w^2=0 := by nlinarith [sq_nonneg x,sq_nonneg z,sq_nonneg w]
              have hx0 : x=0 :=
                (mul_eq_zero.mp (show x*x=0 by simpa only [pow_two] using hx2)).elim id id
              have hz0 : z=0 :=
                (mul_eq_zero.mp (show z*z=0 by simpa only [pow_two] using hz2)).elim id id
              have hw0 : w=0 :=
                (mul_eq_zero.mp (show w*w=0 by simpa only [pow_two] using hw2)).elim id id
              exact False.elim (hne ⟨hx0,hz0,hw0⟩)
        · have hb2 : 2≤|b| := by omega
          obtain ⟨t,c,hstep,ht⟩ := LegendreCenteredRoot318.centered_root a b hb0
            (modular_root a b hb hloc)
          by_cases hc0 : c=0
          · have hat : a=t^2 := by rw [hc0,mul_zero] at hstep; exact (sub_eq_zero.mp hstep).symm
            have hatQ : (a:ℚ)=(t:ℚ)^2 := by exact_mod_cast hat
            exact ⟨1,(t:ℚ),0,by simp,by simp [hatQ]⟩
          · have hcsmall : |c| < |b| :=
              LegendreNormDescentStep318.coefficient_strictly_smaller a b c t hab hb2 ht hstep
            obtain ⟨e,d,he0,hd0,he,hdsq,hdle⟩ := LegendreSquarefreeCRT318.normalize c hc0
            have hlocald : Everywhere a d := by
              refine ⟨descend_at a b c t e d ha0 hb0 he0 hstep he hloc.1,?_⟩
              intro p hp
              exact descend_at a b c t e d ha0 hb0 he0 hstep he (hloc.2 p)
            have hdn : d.natAbs<b.natAbs := by exact_mod_cast hdle.trans_lt hcsmall
            have hmeasure : a.natAbs+d.natAbs<n := by omega
            have hglobald := ih (a.natAbs+d.natAbs) hmeasure a d rfl ha hdsq hlocald
            exact ascend_at a b c t e d ha0 hc0 hstep he hglobald
      intro a b hn ha hb hloc
      rcases le_total |a| |b| with hab | hba
      · exact ordered a b hn ha hb hloc hab
      · apply swap
        exact ordered b a (by omega) hb ha (swap_everywhere hloc) hba
  exact main (a.natAbs+b.natAbs) a b rfl ha hb hloc

/-- Removing a nonzero square from a coefficient preserves actual solutions. -/
theorem square_factor_left {F : Type*} [Field F] (e d b : F) (he0 : e≠0) :
    Sol F (e^2*d) b ↔ Sol F d b := by
  constructor
  · rintro ⟨x,z,w,hne,hsol⟩
    refine ⟨e*x,z,w,?_,?_⟩
    · rintro ⟨hx,hz,hw⟩
      exact hne ⟨(mul_eq_zero.mp hx).resolve_left he0,hz,hw⟩
    · linear_combination hsol
  · rintro ⟨x,z,w,hne,hsol⟩
    refine ⟨x/e,z,w,?_,?_⟩
    · rintro ⟨hx,hz,hw⟩
      have hx0 : x=0 := by
        have hh := congrArg (fun u : F => u*e) hx
        simpa [he0] using hh
      exact hne ⟨hx0,hz,hw⟩
    · have hc : (e^2*d)*(x/e)^2=d*x^2 := by
        field_simp [he0]
        <;> ring
      rw [hc]
      exact hsol

/-- Exact coefficient normalization, uniformly over all characteristic-zero
fields; square factors cannot disappear under their integer embeddings. -/
theorem normalize_at {F : Type*} [Field F] [CharZero F]
    (a b e d f c : ℤ) (he0 : e≠0) (hf0 : f≠0)
    (he : e^2*d=a) (hf : f^2*c=b) :
    Sol F (a:F) (b:F) ↔ Sol F (d:F) (c:F) := by
  have heF : (e:F)^2*(d:F)=(a:F) := by exact_mod_cast he
  have hfF : (f:F)^2*(c:F)=(b:F) := by exact_mod_cast hf
  have heF0 : (e:F)≠0 := by exact_mod_cast he0
  have hfF0 : (f:F)≠0 := by exact_mod_cast hf0
  rw [←heF,←hfF]
  constructor
  · intro h
    exact swap ((square_factor_left (f:F) (c:F) (d:F) hfF0).mp
      (swap ((square_factor_left (e:F) (d:F) ((f:F)^2*(c:F)) heF0).mp h)))
  · intro h
    exact (square_factor_left (e:F) (d:F) ((f:F)^2*(c:F)) heF0).mpr
      (swap ((square_factor_left (f:F) (c:F) (d:F) hfF0).mpr (swap h)))

/-- Ternary local-global existence for integer coefficients, obtained by
normalization and the explicit descending construction, with no local-global
axiom or point-selection premise. This theorem is still an unchecked source
candidate until every dependency and this proof pass strict hosted Lean. -/
theorem rational_of_everywhere (a b : ℤ) (h : Everywhere a b) : Sol ℚ a b := by
  by_cases ha0 : a=0
  · subst a
    exact ⟨1,0,0,by simp,by simp⟩
  by_cases hb0 : b=0
  · subst b
    exact ⟨0,0,1,by simp,by simp⟩
  obtain ⟨e,d,he0,hd0,he,hdsq,hdle⟩ := LegendreSquarefreeCRT318.normalize a ha0
  obtain ⟨f,c,hf0,hc0,hf,hcsq,hcle⟩ := LegendreSquarefreeCRT318.normalize b hb0
  have hlocal : Everywhere d c := by
    refine ⟨(normalize_at a b e d f c he0 hf0 he hf).mp h.1,?_⟩
    intro p hp
    exact (normalize_at a b e d f c he0 hf0 he hf).mp (h.2 p)
  exact (normalize_at a b e d f c he0 hf0 he hf).mpr
    (rational_of_everywhere_squarefree d c hdsq hcsq hlocal)

end LegendreTernaryDescent318
