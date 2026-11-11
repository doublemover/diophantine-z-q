module
public import PELOriginalResidualQuotientCover318
public section
noncomputable section
namespace ComplexAffineFreeTranslation318
set_option maxHeartbeats 2000000
variable (L : AddSubgroup ℂ)
abbrev Torus := ℂ ⧸ L
@[expose] def projection : ℂ →+ Torus L := QuotientAddGroup.mk' L

/-- An affine lift with nonidentity linear part has an actual fixed point
in the complex vector space, hence in the SAME period quotient. -/
theorem affine_fixed (f : Torus L → Torus L) (a b : ℂ)
    (hf : ∀ z,f (projection L z)=projection L (a*z+b)) (ha : a≠1) :
    ∃ p,f p=p := by
  have hn : 1-a≠0 := sub_ne_zero.mpr (Ne.symm ha)
  refine ⟨projection L (b/(1-a)),?_⟩
  rw [hf]
  congr 1
  field_simp [hn] <;> ring

/-- Freeness forces a genuine translation, not merely degree preservation.
The affine lift is an explicit remaining analytic input, not inferred from
an arbitrary holomorphic map of arbitrary genus. -/
theorem free_is_translation (f : Torus L → Torus L) (a b : ℂ)
    (hf : ∀ z,f (projection L z)=projection L (a*z+b))
    (hfree : ∀ p,f p≠p) :
    a=1 ∧ ∀ p,f p=p+projection L b := by
  have ha : a=1 := by
    by_contra hn
    obtain ⟨p,hp⟩ := affine_fixed L f a b hf hn
    exact hfree p hp
  refine ⟨ha,?_⟩
  intro p
  obtain ⟨z,rfl⟩ := QuotientAddGroup.mk'_surjective L p
  rw [hf,ha,one_mul,map_add]

/-- An involutive translation has an actual two-torsion displacement. -/
theorem translation_square (f : Torus L → Torus L) (t : Torus L)
    (hf : ∀ p,f p=p+t) (hsq : ∀ p,f (f p)=p) : t+t=0 := by
  have h := hsq 0
  simpa only [hf,zero_add] using h
end ComplexAffineFreeTranslation318
