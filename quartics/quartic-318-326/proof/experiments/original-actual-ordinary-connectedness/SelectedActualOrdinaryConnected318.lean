module
public import Mathlib.NumberTheory.Modular
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.SetTheory.Cardinal.Basic
public import Mathlib.Tactic
public section
noncomputable section

open scoped MatrixGroups
open UpperHalfPlane

namespace SelectedActualOrdinaryConnected318

@[expose] def rect (x y : ℝ) : ℂ := (x:ℂ)+(y:ℂ)*Complex.I

@[simp] theorem rect_re (x y : ℝ) : (rect x y).re = x := by
  simp [rect,Complex.add_re,Complex.mul_re]

@[simp] theorem rect_im (x y : ℝ) : (rect x y).im = y := by
  simp [rect,Complex.add_im,Complex.mul_im]

theorem continuous_rect {A : Type*} [TopologicalSpace A] {x y : A → ℝ}
    (hx : Continuous x) (hy : Continuous y) : Continuous (fun a => rect (x a) (y a)) :=
  (Complex.continuous_ofReal.comp hx).add
    ((Complex.continuous_ofReal.comp hy).mul continuous_const)

/-- A homeomorphism of the genuine upper half-plane with the complex
plane. This is just topology: it is not a holomorphic modular chart. -/
@[expose] def logHeight : ℍ ≃ₜ ℂ where
  toFun z := rect z.re (Real.log z.im)
  invFun w := UpperHalfPlane.mk (rect w.re (Real.exp w.im)) (by simpa using Real.exp_pos w.im)
  left_inv z := by
    apply UpperHalfPlane.ext_re_im
    · simp
    · simp [Real.exp_log z.im_pos]
  right_inv w := by
    apply Complex.ext
    · simp
    · simp [Real.log_exp]
  continuous_toFun := by
    apply continuous_rect UpperHalfPlane.continuous_re
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (Real.continuousAt_log z.im_pos.ne').comp UpperHalfPlane.continuous_im.continuousAt
  continuous_invFun := by
    apply Continuous.upperHalfPlaneMk
    exact continuous_rect Complex.continuous_re (Real.continuous_exp.comp Complex.continuous_im)

/-- Exactly the two full modular elliptic orbits. All their lifts
are removed, not just the two standard representatives. -/
@[expose] def excluded : Set ℍ :=
  Set.range (fun g : SL(2, ℤ) => g • UpperHalfPlane.I) ∪
  Set.range (fun g : SL(2, ℤ) => g • UpperHalfPlane.ρ)

theorem excluded_countable : excluded.Countable := by
  letI : Countable (SL(2, ℤ)) := by
    change Countable { g : Matrix (Fin 2) (Fin 2) ℤ // Matrix.det g = 1 }
    infer_instance
  exact (Set.countable_range _).union (Set.countable_range _)

theorem excluded_smul (g : SL(2, ℤ)) {z : ℍ} (hz : z ∈ excluded) :
    g • z ∈ excluded := by
  rcases hz with ⟨a,rfl⟩|⟨a,rfl⟩
  · exact Or.inl ⟨g*a,mul_smul g a _⟩
  · exact Or.inr ⟨g*a,mul_smul g a _⟩

theorem upper_ordinary_pathConnected : IsPathConnected (excludedᶜ : Set ℍ) := by
  have hr : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    exact Cardinal.one_lt_two
  have hc : (logHeight '' excluded).Countable := excluded_countable.image logHeight
  have hp := hc.isPathConnected_compl_of_one_lt_rank hr
  have himg := hp.image' logHeight.symm.continuous.continuousOn
  have hset : logHeight.symm '' (logHeight '' excluded)ᶜ = excludedᶜ := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩ hz
      exact hw ⟨logHeight.symm w,hz,logHeight.apply_symm_apply w⟩
    · intro hz
      refine ⟨logHeight z, ?_,logHeight.symm_apply_apply z⟩
      rintro ⟨z',hz',he⟩
      exact hz (logHeight.injective he ▸ hz')
  rwa [hset] at himg

abbrev QuotientAtLevel (N : ℕ) :=
  Quotient (MulAction.orbitRel (CongruenceSubgroup.Gamma1 N) ℍ)

@[expose] def quotientMap (N : ℕ) : ℍ → QuotientAtLevel N := Quotient.mk'

/-- The actual ordinary part of the genuine Γ₁ quotient, with no
independent connected surface chosen for it. -/
@[expose] def ordinaryQuotient (N : ℕ) : Set (QuotientAtLevel N) :=
  quotientMap N '' excludedᶜ

/-- Ordinary membership depends only on the genuine Γ₁ quotient
point, not on choosing a favorable representative. -/
theorem ordinary_iff (N : ℕ) (z : ℍ) :
    quotientMap N z ∈ ordinaryQuotient N ↔ z ∉ excluded := by
  constructor
  · rintro ⟨z',hz',h⟩
    intro hz
    have hrel : MulAction.orbitRel (CongruenceSubgroup.Gamma1 N) ℍ z' z :=
      Quotient.exact h
    obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hrel)
    apply hz'
    have hg' : (g : SL(2, ℤ)) • z = z' := hg
    rw [← hg']
    exact excluded_smul (g : SL(2, ℤ)) hz
  · intro hz
    exact ⟨z,hz,rfl⟩

theorem ordinary_pathConnected (N : ℕ) : IsPathConnected (ordinaryQuotient N) :=
  upper_ordinary_pathConnected.image' continuous_quotient_mk'.continuousOn

theorem ordinary_connected (N : ℕ) : IsConnected (ordinaryQuotient N) :=
  (ordinary_pathConnected N).isConnected

end SelectedActualOrdinaryConnected318

#print axioms SelectedActualOrdinaryConnected318.excluded_countable
#print axioms SelectedActualOrdinaryConnected318.upper_ordinary_pathConnected
#print axioms SelectedActualOrdinaryConnected318.ordinary_connected
