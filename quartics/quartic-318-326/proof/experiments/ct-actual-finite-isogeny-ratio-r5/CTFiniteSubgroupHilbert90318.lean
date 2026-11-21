module
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public section
noncomputable section

namespace CTFiniteSubgroupHilbert90318

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [FiniteDimensional K E]

/-- Finite Hilbert 90 on the actual image subgroup, which need
not be the full Galois group of E over K. Use its literal fixed field
rather than extending the finite cocycle to the full group. -/
theorem finite_subgroup_hilbert90
    (J : Subgroup (E ≃ₐ[K] E)) (c : J → Eˣ)
    (hc : ∀ g h : J, c (g*h)=(g : E ≃ₐ[K] E) • c h * c g) :
    ∃ a : Eˣ, ∀ g : J, (g : E ≃ₐ[K] E) • a / a = c g := by
  let F := IntermediateField.fixedField J
  letI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite K F E
  let e := IntermediateField.subgroupEquivAlgEquiv J
  let c' : (E ≃ₐ[F] E) → Eˣ := c ∘ e.symm
  have ha (g : J) (x : Eˣ) : (e g) • x=(g : E ≃ₐ[K] E) • x := by
    apply Units.ext
    simp only [AlgEquiv.smul_units_def,Units.coe_map,MonoidHom.coe_ofClass]
    exact congrFun (IntermediateField.coe_subgroupEquivAlgEquiv_apply J g) (x:E)
  have hC : groupCohomology.IsMulCocycle₁ c' := by
    intro s t
    change c (e.symm (s*t))=s • c (e.symm t) * c (e.symm s)
    rw [map_mul,hc]
    exact congrArg (fun x : Eˣ => x*c (e.symm s))
      ((ha (e.symm s) (c (e.symm t))).symm.trans (by rw [e.apply_symm_apply]))
  obtain ⟨a,hh⟩ := groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units c' hC
  refine ⟨a,fun g => ?_⟩
  have h := hh (e g)
  change e g • a / a=c (e.symm (e g)) at h
  rwa [ha,e.symm_apply_apply] at h

end CTFiniteSubgroupHilbert90318
