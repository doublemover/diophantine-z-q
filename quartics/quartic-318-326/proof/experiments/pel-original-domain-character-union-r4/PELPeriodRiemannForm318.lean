module
public import PELOriginalPeriodLattice318
public import PELQuaternionPeriodOrientation318
public import PELPrincipalOrderPerfect318
public section
noncomputable section
namespace PELPeriodRiemannForm318
open QuaternionicRealPeriod318 QuaternionicOrderPeriodQuotient318
open PELQuaternionRealRepresentation318 PELPrincipalOrderCoordinates318
open PELOriginalPeriodLattice318 QuaternionicPeriodAlternating318
set_option maxHeartbeats 1200000
variable (τ : ℂ) (hτ : 0<τ.im)

/-- The form is transported to the ACTUAL complex period carrier, with the
explicit sign needed for positive E(z,iz). -/
@[expose] def riemann (z w : ComplexVectors) : ℝ :=
  oriented ((periodEquiv τ hτ).symm z) ((periodEquiv τ hτ).symm w)

theorem alternating (z : ComplexVectors) : riemann τ hτ z z=0 := by
  unfold riemann oriented pairing
  ring

theorem add_left (z z' w : ComplexVectors) :
    riemann τ hτ (z+z') w=riemann τ hτ z w+riemann τ hτ z' w := by
  simp only [riemann,map_add,oriented,pairing,Matrix.add_apply]
  ring

theorem add_right (z w w' : ComplexVectors) :
    riemann τ hτ z (w+w')=riemann τ hτ z w+riemann τ hτ z w' := by
  simp only [riemann,map_add,oriented,pairing,Matrix.add_apply]
  ring

theorem smul_left (a : ℝ) (z w : ComplexVectors) :
    riemann τ hτ (a • z) w=a*riemann τ hτ z w := by
  simp only [riemann,map_smul,oriented,pairing,Matrix.smul_apply,smul_eq_mul]
  ring

theorem smul_right (a : ℝ) (z w : ComplexVectors) :
    riemann τ hτ z (a • w)=a*riemann τ hτ z w := by
  simp only [riemann,map_smul,oriented,pairing,Matrix.smul_apply,smul_eq_mul]
  ring

theorem inverse_I (z : ComplexVectors) :
    (periodEquiv τ hτ).symm (Complex.I • z)=
      complexStructure τ hτ ((periodEquiv τ hτ).symm z) := by
  unfold complexStructure
  rw [show period τ ((periodEquiv τ hτ).symm z)=z from
    (periodEquiv τ hτ).apply_symm_apply z]

theorem positive (z : ComplexVectors) (hz : z≠0) : 0<riemann τ hτ z (Complex.I • z) := by
  rw [riemann,inverse_I]
  apply oriented_positive τ hτ
  intro h
  apply hz
  have hh := congrArg (periodEquiv τ hτ) h
  simpa only [LinearEquiv.apply_symm_apply,map_zero] using hh

theorem I_invariant (z w : ComplexVectors) :
    riemann τ hτ (Complex.I • z) (Complex.I • w)=riemann τ hτ z w := by
  simp only [riemann,inverse_I,complexStructure_invariant]

theorem original_integral (x y : PELPrincipalOrderCoordinates318.Coordinates) :
    riemann τ hτ (periodHom representation τ (embed x)) (periodHom representation τ (embed y))=
      (-(integralForm x y):ℤ) := by
  change oriented ((periodEquiv τ hτ).symm (periodEquiv τ hτ (representation (embed x))))
    ((periodEquiv τ hτ).symm (periodEquiv τ hτ (representation (embed y))))=_
  rw [LinearEquiv.symm_apply_apply,LinearEquiv.symm_apply_apply,oriented,
    PELQuaternionPeriodOrientation318.original_pairing,pairing_value]
  push_cast
  all_goals rfl

@[expose] def latticeMap : PELPrincipalOrderCoordinates318.Coordinates →ₗ[ℤ] lattice τ hτ where
  toFun x := ⟨periodHom representation τ (embed x),original_mem_lattice τ hτ x⟩
  map_add' x y := by
    apply Subtype.ext
    change periodHom representation τ (embed (x+y))=
      periodHom representation τ (embed x)+periodHom representation τ (embed y)
    rw [embed_add,map_add]
  map_smul' n x := by
    apply Subtype.ext
    have he : embed (n • x)=n • embed x := by
      exact congrArg (fun z : order => (z:PELQuaternionAlgebra318.B))
        (map_zsmul coordinatesEquiv.toAddMonoidHom x n)
    change periodHom representation τ (embed (n • x))=n • periodHom representation τ (embed x)
    rw [he,map_zsmul]

theorem latticeMap_bijective : Function.Bijective (latticeMap τ hτ) := by
  constructor
  · intro x y h
    apply embed_injective
    apply representation_injective
    apply (periodEquiv τ hτ).injective
    exact congrArg Subtype.val h
  · intro z
    have hz : z.val∈periodSubgroup representation order τ := by
      rw [exact_period_subgroup τ hτ]
      exact z.property
    obtain ⟨x,hx,hxz⟩ := hz
    obtain ⟨a,rfl⟩ := hx
    exact ⟨a,Subtype.ext hxz⟩

@[expose] def latticeEquiv : PELPrincipalOrderCoordinates318.Coordinates ≃ₗ[ℤ] lattice τ hτ :=
  LinearEquiv.ofBijective (latticeMap τ hτ) (latticeMap_bijective τ hτ)
@[expose] def integralRiemann (x y : lattice τ hτ) : ℤ :=
  -integralForm ((latticeEquiv τ hτ).symm x) ((latticeEquiv τ hτ).symm y)

theorem integralRiemann_value (x y : lattice τ hτ) :
    riemann τ hτ x.val y.val=(integralRiemann τ hτ x y:ℝ) := by
  obtain ⟨a,rfl⟩ := (latticeEquiv τ hτ).surjective x
  obtain ⟨b,rfl⟩ := (latticeEquiv τ hτ).surjective y
  simp only [integralRiemann,LinearEquiv.symm_apply_apply]
  exact original_integral τ hτ a b

/-- Perfectness now holds on the SAME discrete full period lattice that
occurs in the original compact quotient, not only on an abstract Z^4 copy. -/
theorem perfect (f : lattice τ hτ →ₗ[ℤ] ℤ) :
    ∃! x : lattice τ hτ,∀ y : lattice τ hτ,integralRiemann τ hτ x y=f y := by
  let g : PELPrincipalOrderCoordinates318.Coordinates →ₗ[ℤ] ℤ :=
    -(f.comp (latticeEquiv τ hτ).toLinearMap)
  obtain ⟨a,ha,hunique⟩ := PELPrincipalOrderPerfect318.perfect g
  refine ⟨latticeEquiv τ hτ a,?_,?_⟩
  · intro y
    obtain ⟨b,rfl⟩ := (latticeEquiv τ hτ).surjective y
    simp only [integralRiemann,LinearEquiv.symm_apply_apply,ha]
    change -(-f (latticeEquiv τ hτ b))=f (latticeEquiv τ hτ b)
    exact neg_neg _
  · intro x hx
    obtain ⟨b,rfl⟩ := (latticeEquiv τ hτ).surjective x
    apply congrArg (latticeEquiv τ hτ)
    apply hunique
    intro y
    have hh := hx (latticeEquiv τ hτ y)
    simp only [integralRiemann,LinearEquiv.symm_apply_apply] at hh
    change integralForm b y= -f (latticeEquiv τ hτ y)
    linarith
end PELPeriodRiemannForm318
