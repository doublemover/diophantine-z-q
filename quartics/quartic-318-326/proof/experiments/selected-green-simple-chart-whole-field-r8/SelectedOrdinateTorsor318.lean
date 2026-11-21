module
public import SelectedPrimitiveTwistPoint318
public import EvenContactCover318
public import QuadraticPresentation318
public section
noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial
open SelectedPrimitiveAffineSign318 SelectedPrimitiveFixedX318 SelectedPrimitiveTwistPoint318
open EvenContactEtale318

namespace SelectedOrdinateTorsor318
variable (n : ℕ) (I : Ideal (D n))
local notation "R" => SelectedPrimitiveAffineSign318.R n
local notation "Q" => D n ⧸ I
variable (τ : Q →ₐ[R] Q) (hτ : τ.comp (q n I) = (q n I).comp (sign n))
local notation "F" => fixed n I τ
variable (hY : IsUnit (ybar n I))
local notation "Y" => ybar n I
local notation "d" => twistUnit n I τ hτ hY
local notation "P" => QuadraticAlgebra F (d:F) (0:F)

/-- The readout of the actual two-coordinate algebra sends its generator
to the actual primitive ordinate, with no separate square root. -/
@[expose] def evaluate : P →ₐ[F] Q :=
  QuadraticAlgebra.lift ⟨Y,by
    simp only [Algebra.smul_def,mul_one,map_zero,zero_mul,add_zero]
    rw [←pow_two]
    exact (twistUnit_value n I τ hτ hY).symm⟩

theorem evaluate_formula (z : P) :
    evaluate n I τ hτ hY z = (z.re:Q)+(z.im:Q)*Y := by
  simp only [evaluate,QuadraticAlgebra.lift_apply_apply,Algebra.smul_def,mul_one] <;> rfl

theorem evaluate_injective : Function.Injective (evaluate n I τ hτ hY) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  rw [evaluate_formula] at hz
  have hneg := congrArg τ hz
  have hre : τ (z.re:Q) = (z.re:Q) := z.re.property
  have him : τ (z.im:Q) = (z.im:Q) := z.im.property
  simp only [map_add,map_mul,map_zero,hre,him,y_anti n I τ hτ] at hneg
  have hz₂ : (2:Q)*((z.im:Q)*Y) = 0 := by linear_combination hz-hneg
  have h2 : IsUnit (2:Q) := by
    simpa only [map_ofNat] using (OpenJModel318.base_units n).1.map (algebraMap R Q)
  have hzY : (z.im:Q)*Y=0 := h2.mul_left_cancel (hz₂.trans (mul_zero _).symm)
  have hz0 : (z.im:Q)=0 := hY.mul_right_cancel (hzY.trans (zero_mul _).symm)
  have hz1 : (z.re:Q)=0 := by rwa [hzY,add_zero] at hz
  apply QuadraticAlgebra.ext
  · exact Subtype.ext hz1
  · exact Subtype.ext hz0

theorem evaluate_surjective : Function.Surjective (evaluate n I τ hτ hY) := by
  intro z
  obtain ⟨p,r,hr⟩ := even_odd n I z
  let a : F := ⟨aeval (xbar n I) p,(fixed_iff_polynomial n I τ hτ _).mpr ⟨p,rfl⟩⟩
  let b : F := ⟨aeval (xbar n I) r,(fixed_iff_polynomial n I τ hτ _).mpr ⟨r,rfl⟩⟩
  refine ⟨⟨a,b⟩,?_⟩
  rw [evaluate_formula]
  change aeval (xbar n I) p+aeval (xbar n I) r*Y=z
  rw [mul_comm (aeval (xbar n I) r) Y]
  exact hr.symm

/-- The actual primitive coordinate algebra IS the quadratic root algebra
over its actual fixed algebra. No flatness or torsor premise. -/
@[expose] def rootIso : RootRing d ≃ₐ[F] Q :=
  (QuadraticPresentation318.presentationEquiv (d:F)).symm.trans
    (AlgEquiv.ofBijective (evaluate n I τ hτ hY)
      ⟨evaluate_injective n I τ hτ hY,evaluate_surjective n I τ hτ hY⟩)

@[simp] theorem rootIso_root : rootIso n I τ hτ hY (root d) = Y := by
  have hr : QuadraticPresentation318.presentationEquiv (d:F) QuadraticAlgebra.omega =
      root d := QuadraticPresentation318.presentationEquiv_generator (d:F)
  rw [←hr]
  change evaluate n I τ hτ hY
    ((QuadraticPresentation318.presentationEquiv (d:F)).symm
      (QuadraticPresentation318.presentationEquiv (d:F) QuadraticAlgebra.omega)) = _
  rw [AlgEquiv.symm_apply_apply,evaluate_formula]
  simp only [QuadraticAlgebra.re_omega,QuadraticAlgebra.im_omega,ZeroMemClass.coe_zero,
    OneMemClass.coe_one,one_mul,zero_add]

/-- Sign over the ACTUAL fixed algebra. -/
@[expose] def signOverFixed : Q →ₐ[F] Q :=
  { toRingHom := τ.toRingHom
    commutes' := fun a => a.property }

theorem sign_root :
    signOverFixed n I τ (rootIso n I τ hτ hY (root d)) = -Y := by
  rw [rootIso_root]
  exact y_anti n I τ hτ

theorem finite_etale : Module.Finite F Q ∧ Algebra.Etale F Q := by
  have h2 : IsUnit (2:F) := by
    simpa only [map_ofNat] using (OpenJModel318.base_units n).1.map (algebraMap R F)
  letI : Module.Finite F (RootRing d) := rootRing_finite d
  letI : Algebra.Etale F (RootRing d) := rootRing_etale d h2
  exact ⟨Module.Finite.equiv (rootIso n I τ hτ hY).toLinearEquiv,
    Algebra.Etale.of_equiv (rootIso n I τ hτ hY)⟩

theorem faithfully_flat [Nontrivial F] : Module.FaithfullyFlat F Q := by
  letI : Module.FaithfullyFlat F (RootRing d) := rootRing_faithfullyFlat d
  exact Module.FaithfullyFlat.of_linearEquiv F (RootRing d) (rootIso n I τ hτ hY).symm.toLinearEquiv

end SelectedOrdinateTorsor318

#print axioms SelectedOrdinateTorsor318.rootIso_root
#print axioms SelectedOrdinateTorsor318.finite_etale
#print axioms SelectedOrdinateTorsor318.faithfully_flat
