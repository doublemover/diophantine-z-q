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
variable (τ : (D n ⧸ I) →ₐ[SelectedPrimitiveAffineSign318.R n] (D n ⧸ I))
variable (hτ : τ.comp (q n I) = (q n I).comp (sign n)) (hY : IsUnit (ybar n I))

/-- The readout of the actual two-coordinate algebra sends its generator
to the actual primitive ordinate, with no separate square root. -/
@[expose] def evaluate : (QuadraticAlgebra ↥(fixed n I τ) ((twistUnit n I τ hτ hY):↥(fixed n I τ)) (0:↥(fixed n I τ))) →ₐ[↥(fixed n I τ)] (D n ⧸ I) :=
  QuadraticAlgebra.lift ⟨(ybar n I),by
    simp only [Algebra.smul_def,mul_one,map_zero,zero_mul,add_zero]
    rw [←pow_two]
    exact (twistUnit_value n I τ hτ hY).symm⟩

theorem evaluate_formula (z : (QuadraticAlgebra ↥(fixed n I τ) ((twistUnit n I τ hτ hY):↥(fixed n I τ)) (0:↥(fixed n I τ)))) :
    evaluate n I τ hτ hY z = (z.re:(D n ⧸ I))+(z.im:(D n ⧸ I))*(ybar n I) := by
  simp only [evaluate,QuadraticAlgebra.lift_apply_apply,Algebra.smul_def,mul_one] <;> rfl

theorem evaluate_injective : Function.Injective (evaluate n I τ hτ hY) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  rw [evaluate_formula] at hz
  have hneg := congrArg τ hz
  have hre : τ (z.re:(D n ⧸ I)) = (z.re:(D n ⧸ I)) := z.re.property
  have him : τ (z.im:(D n ⧸ I)) = (z.im:(D n ⧸ I)) := z.im.property
  simp only [map_add,map_mul,map_zero,hre,him,y_anti n I τ hτ] at hneg
  have hz₂ : (2:(D n ⧸ I))*((z.im:(D n ⧸ I))*(ybar n I)) = 0 := by linear_combination hz-hneg
  have h2 : IsUnit (2:(D n ⧸ I)) := by
    simpa only [map_ofNat] using (OpenJModel318.base_units n).1.map (algebraMap (SelectedPrimitiveAffineSign318.R n) (D n ⧸ I))
  have hzY : (z.im:(D n ⧸ I))*(ybar n I)=0 := h2.mul_left_cancel (hz₂.trans (mul_zero _).symm)
  have hz0 : (z.im:(D n ⧸ I))=0 := hY.mul_right_cancel (hzY.trans (zero_mul _).symm)
  have hz1 : (z.re:(D n ⧸ I))=0 := by rwa [hzY,add_zero] at hz
  apply QuadraticAlgebra.ext
  · exact Subtype.ext hz1
  · exact Subtype.ext hz0

theorem evaluate_surjective : Function.Surjective (evaluate n I τ hτ hY) := by
  intro z
  obtain ⟨p,r,hr⟩ := even_odd n I z
  let a : ↥(fixed n I τ) := ⟨aeval (xbar n I) p,(fixed_iff_polynomial n I τ hτ _).mpr ⟨p,rfl⟩⟩
  let b : ↥(fixed n I τ) := ⟨aeval (xbar n I) r,(fixed_iff_polynomial n I τ hτ _).mpr ⟨r,rfl⟩⟩
  refine ⟨⟨a,b⟩,?_⟩
  rw [evaluate_formula]
  change aeval (xbar n I) p+aeval (xbar n I) r*(ybar n I)=z
  rw [mul_comm (aeval (xbar n I) r) (ybar n I)]
  exact hr.symm

/-- The actual primitive coordinate algebra IS the quadratic root algebra
over its actual fixed algebra. No flatness or torsor premise. -/
@[expose] def rootIso : RootRing (twistUnit n I τ hτ hY) ≃ₐ[↥(fixed n I τ)] (D n ⧸ I) :=
  (QuadraticPresentation318.presentationEquiv ((twistUnit n I τ hτ hY):↥(fixed n I τ))).symm.trans
    (AlgEquiv.ofBijective (evaluate n I τ hτ hY)
      ⟨evaluate_injective n I τ hτ hY,evaluate_surjective n I τ hτ hY⟩)

@[simp] theorem rootIso_root : rootIso n I τ hτ hY (root (twistUnit n I τ hτ hY)) = (ybar n I) := by
  have hr : QuadraticPresentation318.presentationEquiv ((twistUnit n I τ hτ hY):↥(fixed n I τ)) QuadraticAlgebra.omega =
      root (twistUnit n I τ hτ hY) := QuadraticPresentation318.presentationEquiv_generator ((twistUnit n I τ hτ hY):↥(fixed n I τ))
  rw [←hr]
  change evaluate n I τ hτ hY
    ((QuadraticPresentation318.presentationEquiv ((twistUnit n I τ hτ hY):↥(fixed n I τ))).symm
      (QuadraticPresentation318.presentationEquiv ((twistUnit n I τ hτ hY):↥(fixed n I τ)) QuadraticAlgebra.omega)) = _
  rw [AlgEquiv.symm_apply_apply,evaluate_formula]
  simp only [QuadraticAlgebra.re_omega,QuadraticAlgebra.im_omega,ZeroMemClass.coe_zero,
    OneMemClass.coe_one,one_mul,zero_add]

/-- Sign over the ACTUAL fixed algebra. -/
@[expose] def signOverFixed : (D n ⧸ I) →ₐ[↥(fixed n I τ)] (D n ⧸ I) :=
  { toRingHom := τ.toRingHom
    commutes' := fun a => a.property }

theorem sign_root :
    signOverFixed n I τ (rootIso n I τ hτ hY (root (twistUnit n I τ hτ hY))) = -(ybar n I) := by
  rw [rootIso_root]
  exact y_anti n I τ hτ

include hτ hY in
theorem finite_etale : Module.Finite ↥(fixed n I τ) (D n ⧸ I) ∧ Algebra.Etale ↥(fixed n I τ) (D n ⧸ I) := by
  have h2 : IsUnit (2:↥(fixed n I τ)) := by
    simpa only [map_ofNat] using (OpenJModel318.base_units n).1.map (algebraMap (SelectedPrimitiveAffineSign318.R n) ↥(fixed n I τ))
  letI : Module.Finite ↥(fixed n I τ) (RootRing (twistUnit n I τ hτ hY)) := rootRing_finite (twistUnit n I τ hτ hY)
  letI : Algebra.Etale ↥(fixed n I τ) (RootRing (twistUnit n I τ hτ hY)) := rootRing_etale (twistUnit n I τ hτ hY) h2
  exact ⟨Module.Finite.equiv (rootIso n I τ hτ hY).toLinearEquiv,
    Algebra.Etale.of_equiv (rootIso n I τ hτ hY)⟩

include hτ hY in
theorem faithfully_flat [Nontrivial ↥(fixed n I τ)] : Module.FaithfullyFlat ↥(fixed n I τ) (D n ⧸ I) := by
  letI : Module.FaithfullyFlat ↥(fixed n I τ) (RootRing (twistUnit n I τ hτ hY)) := rootRing_faithfullyFlat (twistUnit n I τ hτ hY)
  exact Module.FaithfullyFlat.of_linearEquiv ↥(fixed n I τ) (RootRing (twistUnit n I τ hτ hY)) (rootIso n I τ hτ hY).symm.toLinearEquiv

end SelectedOrdinateTorsor318

#print axioms SelectedOrdinateTorsor318.rootIso_root
#print axioms SelectedOrdinateTorsor318.finite_etale
#print axioms SelectedOrdinateTorsor318.faithfully_flat
