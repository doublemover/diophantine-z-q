module
public import PELInertiaOrderInvolutions318
public section
noncomputable section
namespace PELInertiaQuadraticEmbeddings318
open PELQuaternionAlgebra318 PELInertiaNormalizerData318
set_option maxHeartbeats 1000000
/-- The five genuine imaginary quadratic carriers with the exact label
radicands, embedded in the original rational quaternion algebra. -/
abbrev Quadratic (i : Fin 5) := QuadraticAlgebra ℚ (-(discriminant i:ℚ)) 0

theorem relation (i : Fin 5) : element i*element i=
    (-(discriminant i:ℚ)) • (1:B)+(0:ℚ) • element i := by
  rw [element_square]
  ext <;> simp [QuaternionAlgebra.algebraMap_eq]

@[expose] def realization (i : Fin 5) : Quadratic i →ₐ[ℚ] B :=
  QuadraticAlgebra.lift ⟨element i,relation i⟩
theorem realization_value (i : Fin 5) (z : Quadratic i) :
    realization i z=z.re • (1:B)+z.im • element i := rfl

theorem realization_generator (i : Fin 5) :
    realization i QuadraticAlgebra.omega=element i := by
  rw [realization_value]
  simp [QuadraticAlgebra.omega]

theorem realization_injective (i : Fin 5) : Function.Injective (realization i) := by
  intro z w h
  rw [realization_value,realization_value] at h
  have hr := congrArg QuaternionAlgebra.re h
  have hi := congrArg QuaternionAlgebra.imI h
  change z.re*1+z.im*(element i).re=w.re*1+w.im*(element i).re at hr
  change z.re*0+z.im*(element i).imI=w.re*0+w.im*(element i).imI at hi
  simp only [mul_zero,zero_add] at hi
  have him := mul_right_cancel₀ (element_imI_ne_zero i) hi
  have hre : z.re=w.re := by rw [him] at hr; linarith
  exact QuadraticAlgebra.ext hre him

instance noRoot (i : Fin 5) : Fact (∀ r : ℚ,r^2≠-(discriminant i:ℚ)+0*r) :=
  ⟨by intro r hr; have hd := discriminant_positive i; nlinarith [sq_nonneg r]⟩

/-- Field structure follows from actual negativity, not from a supplied
irreducibility or a label named imaginary quadratic. -/
noncomputable instance quadraticField (i : Fin 5) : Field (Quadratic i) := inferInstance

/-- The same integral normalizer is the image of the literal quadratic
generator, with the unchanged original inertia label. -/
theorem original_label_generator (i : Fin 5) :
    realization i QuadraticAlgebra.omega∈PELPrincipalOrderCoordinates318.order ∧
    reducedNorm (realization i QuadraticAlgebra.omega)=
      InertiaLabels318.divisor (InertiaLabels318.fiveLabels i) := by
  rw [realization_generator,label_identity]
  exact ⟨element_mem i,element_norm i⟩
end PELInertiaQuadraticEmbeddings318
