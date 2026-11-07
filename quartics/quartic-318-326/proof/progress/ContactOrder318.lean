module
public import ContactGenericFiber318
public section
noncomputable section
namespace ContactOrder318
set_option maxHeartbeats 600000
open QuadraticPresentation318 ContactBaseChange318
variable {R:Type*} [CommRing R]

/-- The actual contact order is a monogenic finite algebra, including ramified contacts. -/
theorem finite_order (u:Rˣ) (pi:R) (m:ℕ) :
    Module.Finite R (RootRing ((u:R)*pi^(2*m))) :=
  (Polynomial.monic_X_pow_sub_C ((u:R)*pi^(2*m)) (by decide : 2≠0)).finite_adjoinRoot

theorem free_order (u:Rˣ) (pi:R) (m:ℕ) :
    Module.Free R (RootRing ((u:R)*pi^(2*m))) :=
  (Polynomial.monic_X_pow_sub_C ((u:R)*pi^(2*m)) (by decide : 2≠0)).free_adjoinRoot

@[expose] def unitPresentation (u:Rˣ) :
    QuadraticAlgebra R (u:R) 0 ≃ₐ[R] EvenContactEtale318.RootRing u :=
  presentationEquiv (u:R)

@[simp] theorem unitPresentation_generator (u:Rˣ) :
    unitPresentation u QuadraticAlgebra.omega=EvenContactEtale318.root u :=
  presentationEquiv_generator (u:R)

@[expose] def scaling (u:Rˣ) (pi:R) (m:ℕ) :
    QuadraticAlgebra R ((u:R)*pi^(2*m)) 0 →ₐ[R] QuadraticAlgebra R (u:R) 0 :=
  QuadraticAlgebra.changeGenerator (u:R) 0 (pi^m) 0
    (by simp only [mul_zero,sub_zero,zero_pow (by decide : 2≠0),pow_mul]; ring) (by simp)

@[simp] theorem scaling_generator (u:Rˣ) (pi:R) (m:ℕ) :
    scaling u pi m QuadraticAlgebra.omega=pi^m • QuadraticAlgebra.omega := by
  simp [scaling]

theorem contactMap_presentation (u:Rˣ) (pi:R) (m:ℕ) :
    (contactMap u pi m).comp (presentationEquiv ((u:R)*pi^(2*m))).toAlgHom=
      (unitPresentation u).toAlgHom.comp (scaling u pi m) := by
  apply QuadraticAlgebra.algHom_ext
  simp only [AlgHom.comp_apply,AlgEquiv.coe_toAlgHom,presentationEquiv_generator,
    contactMap_generator,scaling_generator,map_smul,unitPresentation_generator]
  rw [Algebra.smul_def,map_pow]

/-- The actual contact-to-unit-root map is injective for nonzero parameter over a domain. -/
theorem contactMap_injective [IsDomain R] (u:Rˣ) (pi:R) (m:ℕ) (hp:pi≠0) :
    Function.Injective (contactMap u pi m) := by
  have hs:Function.Injective (scaling u pi m) := by
    apply QuadraticAlgebra.changeGenerator_injective
    exact isRegular_iff_ne_zero.mpr (pow_ne_zero m hp)
  intro x y h
  obtain ⟨a,rfl⟩:=(presentationEquiv ((u:R)*pi^(2*m))).surjective x
  obtain ⟨b,rfl⟩:=(presentationEquiv ((u:R)*pi^(2*m))).surjective y
  have he:=contactMap_presentation u pi m
  have ha:=AlgHom.congr_fun he a
  have hb:=AlgHom.congr_fun he b
  simp only [AlgHom.comp_apply,AlgEquiv.coe_toAlgHom] at ha hb
  rw [ha,hb] at h
  exact congrArg (presentationEquiv ((u:R)*pi^(2*m))) (hs ((unitPresentation u).injective h))

end ContactOrder318
