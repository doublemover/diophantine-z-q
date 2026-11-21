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
/-- Canonical subalgebra operations, presented explicitly to avoid typeclass
search through the expanded actual quotient. -/
abbrev fixedRing (n : ℕ) (I : Ideal (D n))
    (τ : (D n ⧸ I) →ₐ[SelectedPrimitiveAffineSign318.R n] (D n ⧸ I)) :
    CommRing ↥(fixed n I τ) :=
  @Subalgebra.toCommRing (SelectedPrimitiveAffineSign318.R n) (D n ⧸ I)
    inferInstance inferInstance inferInstance (fixed n I τ)

abbrev fixedAlgebra (n : ℕ) (I : Ideal (D n))
    (τ : (D n ⧸ I) →ₐ[SelectedPrimitiveAffineSign318.R n] (D n ⧸ I)) :
    letI := fixedRing n I τ
    Algebra ↥(fixed n I τ) (D n ⧸ I) :=
  Subalgebra.toAlgebra (R := SelectedPrimitiveAffineSign318.R n)
    (A := D n ⧸ I) (α := D n ⧸ I) (fixed n I τ)

attribute [local instance 2000] fixedRing fixedAlgebra

private theorem transfer_finite_etale {S T : Type*} [CommRing S] [CommRing T]
    [Algebra S T] (d : Sˣ) (h2 : IsUnit (2:S)) (e : RootRing d ≃ₐ[S] T) :
    Module.Finite S T ∧ Algebra.Etale S T := by
  letI : Module.Finite S (RootRing d) := rootRing_finite d
  letI : Algebra.Etale S (RootRing d) := rootRing_etale d h2
  exact ⟨Module.Finite.equiv e.toLinearEquiv, Algebra.Etale.of_equiv e⟩

private theorem transfer_faithfully_flat {S T : Type*} [CommRing S] [CommRing T]
    [Algebra S T] [Nontrivial S] (d : Sˣ) (e : RootRing d ≃ₐ[S] T) :
    Module.FaithfullyFlat S T := by
  letI : Module.FaithfullyFlat S (RootRing d) := rootRing_faithfullyFlat d
  exact Module.FaithfullyFlat.of_linearEquiv S (RootRing d) e.symm.toLinearEquiv

/-- The readout of the actual two-coordinate algebra sends its generator
to the actual primitive ordinate, with no separate square root. -/
@[expose] def evaluate (n : ℕ) (I : Ideal (D n))
    (τ : (D n ⧸ I) →ₐ[SelectedPrimitiveAffineSign318.R n] (D n ⧸ I))
    (hτ : τ.comp (q n I) = (q n I).comp (sign n)) (hY : IsUnit (ybar n I)) : (QuadraticAlgebra ↥(fixed n I τ) ((twistUnit n I τ hτ hY):↥(fixed n I τ)) (0:↥(fixed n I τ))) →ₐ[↥(fixed n I τ)] (D n ⧸ I) :=
  QuadraticAlgebra.lift ⟨(ybar n I),by
    simp only [Algebra.smul_def,mul_one,map_zero,zero_mul,add_zero]
    rw [←pow_two]
    exact (twistUnit_value n I τ hτ hY).symm⟩

theorem evaluate_formula (n : ℕ) (I : Ideal (D n))
    (τ : (D n ⧸ I) →ₐ[SelectedPrimitiveAffineSign318.R n] (D n ⧸ I))
    (hτ : τ.comp (q n I) = (q n I).comp (sign n)) (hY : IsUnit (ybar n I)) (z : (QuadraticAlgebra ↥(fixed n I τ) ((twistUnit n I τ hτ hY):↥(fixed n I τ)) (0:↥(fixed n I τ)))) :
    evaluate n I τ hτ hY z = (z.re:(D n ⧸ I))+(z.im:(D n ⧸ I))*(ybar n I) := by
  simp only [evaluate,QuadraticAlgebra.lift_apply_apply,Algebra.smul_def,mul_one] <;> rfl

theorem evaluate_injective (n : ℕ) (I : Ideal (D n))
    (τ : (D n ⧸ I) →ₐ[SelectedPrimitiveAffineSign318.R n] (D n ⧸ I))
    (hτ : τ.comp (q n I) = (q n I).comp (sign n)) (hY : IsUnit (ybar n I)) : Function.Injective (evaluate n I τ hτ hY) := by
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

theorem evaluate_surjective (n : ℕ) (I : Ideal (D n))
    (τ : (D n ⧸ I) →ₐ[SelectedPrimitiveAffineSign318.R n] (D n ⧸ I))
    (hτ : τ.comp (q n I) = (q n I).comp (sign n)) (hY : IsUnit (ybar n I)) : Function.Surjective (evaluate n I τ hτ hY) := by
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
@[expose] def rootIso (n : ℕ) (I : Ideal (D n))
    (τ : (D n ⧸ I) →ₐ[SelectedPrimitiveAffineSign318.R n] (D n ⧸ I))
    (hτ : τ.comp (q n I) = (q n I).comp (sign n)) (hY : IsUnit (ybar n I)) : RootRing (twistUnit n I τ hτ hY) ≃ₐ[↥(fixed n I τ)] (D n ⧸ I) :=
  (QuadraticPresentation318.presentationEquiv ((twistUnit n I τ hτ hY):↥(fixed n I τ))).symm.trans
    (AlgEquiv.ofBijective (evaluate n I τ hτ hY)
      ⟨evaluate_injective n I τ hτ hY,evaluate_surjective n I τ hτ hY⟩)

@[simp] theorem rootIso_root (n : ℕ) (I : Ideal (D n))
    (τ : (D n ⧸ I) →ₐ[SelectedPrimitiveAffineSign318.R n] (D n ⧸ I))
    (hτ : τ.comp (q n I) = (q n I).comp (sign n)) (hY : IsUnit (ybar n I)) : rootIso n I τ hτ hY (root (twistUnit n I τ hτ hY)) = (ybar n I) := by
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
@[expose] def signOverFixed (n : ℕ) (I : Ideal (D n))
    (τ : (D n ⧸ I) →ₐ[SelectedPrimitiveAffineSign318.R n] (D n ⧸ I)) : (D n ⧸ I) →ₐ[↥(fixed n I τ)] (D n ⧸ I) :=
  { toRingHom := τ.toRingHom
    commutes' := fun a => a.property }

theorem sign_root (n : ℕ) (I : Ideal (D n))
    (τ : (D n ⧸ I) →ₐ[SelectedPrimitiveAffineSign318.R n] (D n ⧸ I))
    (hτ : τ.comp (q n I) = (q n I).comp (sign n)) (hY : IsUnit (ybar n I)) :
    signOverFixed n I τ (rootIso n I τ hτ hY (root (twistUnit n I τ hτ hY))) = -(ybar n I) := by
  rw [rootIso_root]
  exact y_anti n I τ hτ

theorem finite_etale (n : ℕ) (I : Ideal (D n))
    (τ : (D n ⧸ I) →ₐ[SelectedPrimitiveAffineSign318.R n] (D n ⧸ I))
    (hτ : τ.comp (q n I) = (q n I).comp (sign n)) (hY : IsUnit (ybar n I)) : Module.Finite ↥(fixed n I τ) (D n ⧸ I) ∧ Algebra.Etale ↥(fixed n I τ) (D n ⧸ I) := by
  have h2 : IsUnit (2:↥(fixed n I τ)) := by
    simpa only [map_ofNat] using (OpenJModel318.base_units n).1.map (algebraMap (SelectedPrimitiveAffineSign318.R n) ↥(fixed n I τ))
  exact transfer_finite_etale (S := ↥(fixed n I τ)) (T := D n ⧸ I)
    (twistUnit n I τ hτ hY) h2 (rootIso n I τ hτ hY)

theorem faithfully_flat (n : ℕ) (I : Ideal (D n))
    (τ : (D n ⧸ I) →ₐ[SelectedPrimitiveAffineSign318.R n] (D n ⧸ I))
    (hτ : τ.comp (q n I) = (q n I).comp (sign n)) (hY : IsUnit (ybar n I)) [Nontrivial ↥(fixed n I τ)] : Module.FaithfullyFlat ↥(fixed n I τ) (D n ⧸ I) := by
  exact transfer_faithfully_flat (S := ↥(fixed n I τ)) (T := D n ⧸ I)
    (twistUnit n I τ hτ hY) (rootIso n I τ hτ hY)

end SelectedOrdinateTorsor318

#print axioms SelectedOrdinateTorsor318.rootIso_root
#print axioms SelectedOrdinateTorsor318.finite_etale
#print axioms SelectedOrdinateTorsor318.faithfully_flat
