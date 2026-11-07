module
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.Coset.Card
public section
noncomputable section
namespace FiberCentralizer318
set_option maxHeartbeats 0
variable {G Γ : Type*} [Group G] [Group Γ]

/-- A permutation commuting with the left regular action is a right translation. -/
theorem commuting_perm_eq_right (f:Equiv.Perm G)
    (hc:∀g x:G,f (g*x)=g*f x) (x:G) : f x=x*f 1 := by
  simpa using hc x 1

/-- The centralizer evaluation is an honest homomorphism to the opposite group. -/
@[expose] def evaluationHom (ρ:Γ→*Equiv.Perm G)
    (hc:∀s:Γ,∀g x:G,ρ s (g*x)=g*ρ s x) : Γ→*Gᵐᵒᵖ where
  toFun s:=MulOpposite.op (ρ s 1)
  map_one' := by simp
  map_mul' s t := by
    apply MulOpposite.unop_injective
    change ρ (s*t) 1=ρ t 1*ρ s 1
    rw [map_mul,Equiv.Perm.mul_apply]
    exact commuting_perm_eq_right (ρ s) (hc s) (ρ t 1)

theorem evaluationHom_injective (ρ:Γ→*Equiv.Perm G)
    (hc:∀s:Γ,∀g x:G,ρ s (g*x)=g*ρ s x) (hρ:Function.Injective ρ) :
    Function.Injective (evaluationHom ρ hc) := by
  intro s t h
  apply hρ
  have he:ρ s 1=ρ t 1 := congrArg MulOpposite.unop h
  apply Equiv.ext
  intro x
  rw [commuting_perm_eq_right (ρ s) (hc s),commuting_perm_eq_right (ρ t) (hc t),he]

/-- The faithful commuting image order divides the regular-group order, not merely its factorial. -/
theorem faithful_commuting_card_dvd (ρ:Γ→*Equiv.Perm G)
    (hc:∀s:Γ,∀g x:G,ρ s (g*x)=g*ρ s x) (hρ:Function.Injective ρ) :
    Nat.card Γ∣Nat.card G := by
  have h:=Subgroup.card_dvd_of_injective (evaluationHom ρ hc) (evaluationHom_injective ρ hc hρ)
  rwa [←Nat.card_congr (MulOpposite.opEquiv (α:=G))] at h

theorem faithful_commuting_card_le [Finite G] (ρ:Γ→*Equiv.Perm G)
    (hc:∀s:Γ,∀g x:G,ρ s (g*x)=g*ρ s x) (hρ:Function.Injective ρ) :
    Nat.card Γ≤Nat.card G := Nat.le_of_dvd Nat.card_pos (faithful_commuting_card_dvd ρ hc hρ)

/-- An actual finite Galois field degree, conditional on its faithful regular-fiber action. -/
theorem galois_degree_dvd (F L:Type*) [Field F] [Field L] [Algebra F L]
    [FiniteDimensional F L] [IsGalois F L]
    (ρ:(L≃ₐ[F]L)→*Equiv.Perm G)
    (hc:∀s:L≃ₐ[F]L,∀g x:G,ρ s (g*x)=g*ρ s x) (hρ:Function.Injective ρ) :
    Module.finrank F L∣Nat.card G := by
  rw [←IsGalois.card_aut_eq_finrank F L]
  exact faithful_commuting_card_dvd ρ hc hρ

theorem galois_degree_576 (L:Type*) [Field L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (hG:Nat.card G=576) (ρ:(L≃ₐ[ℚ]L)→*Equiv.Perm G)
    (hc:∀s:L≃ₐ[ℚ]L,∀g x:G,ρ s (g*x)=g*ρ s x) (hρ:Function.Injective ρ) :
    Module.finrank ℚ L∣576 ∧ Module.finrank ℚ L≤576 := by
  have hd:=galois_degree_dvd ℚ L ρ hc hρ
  rw [hG] at hd
  exact ⟨hd,Nat.le_of_dvd (by norm_num) hd⟩


section Torsor
variable {Ω:Type*}

/-- A chosen geometric point identifies a free transitive fiber with its regular group. -/
@[expose] def orbitEquiv (a:G→*Equiv.Perm Ω) (o:Ω)
    (ha:Function.Bijective (fun g:G=>a g o)) : G≃Ω := Equiv.ofBijective _ ha

theorem orbitEquiv_mul (a:G→*Equiv.Perm Ω) (o:Ω)
    (ha:Function.Bijective (fun g:G=>a g o)) (g x:G) :
    orbitEquiv a o ha (g*x)=a g (orbitEquiv a o ha x) := by
  simp only [orbitEquiv,Equiv.ofBijective_apply,map_mul,Equiv.Perm.mul_apply]

@[expose] def transportRepresentation (e:G≃Ω) (ρ:Γ→*Equiv.Perm Ω) : Γ→*Equiv.Perm G :=
  e.symm.permCongrHom.toMonoidHom.comp ρ

theorem transportRepresentation_apply (e:G≃Ω) (ρ:Γ→*Equiv.Perm Ω) (s:Γ) (x:G) :
    transportRepresentation e ρ s x=e.symm (ρ s (e x)) := rfl

theorem transportRepresentation_injective (e:G≃Ω) (ρ:Γ→*Equiv.Perm Ω)
    (hρ:Function.Injective ρ) : Function.Injective (transportRepresentation e ρ) :=
  e.symm.permCongrHom.injective.comp hρ

/-- Q-defined deck transformations commute with Galois permutations before any point is chosen. -/
theorem torsor_commutation (a:G→*Equiv.Perm Ω) (o:Ω)
    (ha:Function.Bijective (fun g:G=>a g o)) (ρ:Γ→*Equiv.Perm Ω)
    (hc:∀s:Γ,∀g:G,∀x:Ω,ρ s (a g x)=a g (ρ s x)) :
    ∀s:Γ,∀g x:G,transportRepresentation (orbitEquiv a o ha) ρ s (g*x)=
      g*transportRepresentation (orbitEquiv a o ha) ρ s x := by
  intro s g x
  simp only [transportRepresentation_apply]
  apply (orbitEquiv a o ha).injective
  simp only [Equiv.apply_symm_apply,orbitEquiv_mul]
  rw [hc]

theorem faithful_torsor_card_dvd (a:G→*Equiv.Perm Ω) (o:Ω)
    (ha:Function.Bijective (fun g:G=>a g o)) (ρ:Γ→*Equiv.Perm Ω)
    (hc:∀s:Γ,∀g:G,∀x:Ω,ρ s (a g x)=a g (ρ s x)) (hρ:Function.Injective ρ) :
    Nat.card Γ∣Nat.card G :=
  faithful_commuting_card_dvd (transportRepresentation (orbitEquiv a o ha) ρ)
    (torsor_commutation a o ha ρ hc)
    (transportRepresentation_injective (orbitEquiv a o ha) ρ hρ)

/-- The source-specific degree conclusion for an actual finite Galois field and its actual torsor fiber. -/
theorem galois_torsor_degree_576 (L:Type*) [Field L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (a:G→*Equiv.Perm Ω) (o:Ω) (ha:Function.Bijective (fun g:G=>a g o))
    (hG:Nat.card G=576) (ρ:(L≃ₐ[ℚ]L)→*Equiv.Perm Ω)
    (hc:∀s:L≃ₐ[ℚ]L,∀g:G,∀x:Ω,ρ s (a g x)=a g (ρ s x))
    (hρ:Function.Injective ρ) :
    Module.finrank ℚ L∣576 ∧ Module.finrank ℚ L≤576 := by
  have hd:=faithful_torsor_card_dvd a o ha ρ hc hρ
  rw [hG,IsGalois.card_aut_eq_finrank ℚ L] at hd
  exact ⟨hd,Nat.le_of_dvd (by norm_num) hd⟩

end Torsor
end FiberCentralizer318
