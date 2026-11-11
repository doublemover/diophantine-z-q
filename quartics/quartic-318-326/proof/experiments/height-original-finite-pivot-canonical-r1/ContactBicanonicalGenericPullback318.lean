module
public import ContactFiniteCoefficientIdentity318
public import FieldContactZoomTensor318
public section
noncomputable section
namespace ContactBicanonicalGenericPullback318
open scoped TensorProduct
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {K A : Type*} [Field K] [CharZero K] [CommRing A]
  [Algebra K A] [Algebra ℚ A] [IsScalarTower ℚ K A]
  (c : Fin 4 → ℚˣ) (i : Fin 4)
  (f : ContactBicanonicalCoefficients318.BranchRing c i →ₐ[ℚ] A)
@[expose] def branchImage : KaehlerDifferential K A ⊗[A] KaehlerDifferential K A :=
  f (ContactBicanonicalCoefficients318.branchQ0 c i) •
    (KaehlerDifferential.D K A (f (ContactFrameNormalization318.sourceCoordinate c i)) ⊗ₜ[A]
      KaehlerDifferential.D K A (f (ContactFrameNormalization318.sourceCoordinate c i)))

theorem branch_differential : KaehlerDifferential.D K A (f (ContactBicanonicalCoefficients318.branchT c i))=
    (2*algebraMap ℚ A (↑(c i)⁻¹ : ℚ)*f (ContactFrameNormalization318.sourceCoordinate c i)) •
      KaehlerDifferential.D K A (f (ContactFrameNormalization318.sourceCoordinate c i)) := by
  have hs := congrArg f (ContactBranchCoordinate318.coordinate_square c i)
  simp only [map_sub,map_mul,map_pow,AlgHom.commutes] at hs
  have hs' : f (ContactBicanonicalCoefficients318.branchT c i)-
      algebraMap K A (algebraMap ℚ K (LinearContactSquareclass318.contacts i))=
      algebraMap K A (algebraMap ℚ K (↑(c i)⁻¹ : ℚ))*
        f (ContactFrameNormalization318.sourceCoordinate c i)^2 := by
    simpa only [←IsScalarTower.algebraMap_apply] using hs
  simpa only [←IsScalarTower.algebraMap_apply] using
    SquareCoordinateDifferential318.D_of_square (R:=K)
      (f (ContactBicanonicalCoefficients318.branchT c i))
      (f (ContactFrameNormalization318.sourceCoordinate c i))
      (algebraMap ℚ K (LinearContactSquareclass318.contacts i))
      (algebraMap ℚ K (↑(c i)⁻¹ : ℚ)) hs'

theorem branchImage_cleared : f (ContactFiniteCoefficientIdentity318.branchP c i) • branchImage c i f=
    KaehlerDifferential.D K A (f (ContactBicanonicalCoefficients318.branchT c i)) ⊗ₜ[A]
      KaehlerDifferential.D K A (f (ContactBicanonicalCoefficients318.branchT c i)) := by
  have hc := congrArg f (ContactFiniteCoefficientIdentity318.finite_cleared c i)
  simp only [map_mul,map_pow,map_ofNat,AlgHom.commutes] at hc
  rw [branchImage,←mul_smul,hc]
  simp only [branch_differential,TensorProduct.smul_tmul_smul,←pow_two]

open IntegralContactZoomCoefficients318
variable (d a : Fin 4 → K) (t : K) (y : Fin 4 → K)
  (hy : ∀ j,(y j)^2=IntegralQuadraticPointZoom318.value (alpha d a .finite) d (gamma d a .finite) t j)
  (hn : ∀ j,y j≠0)
  (g : ContactBicanonicalCoefficients318.BranchRing c i →ₐ[ℚ] Chart d a t .finite)
  (hT : g (ContactBicanonicalCoefficients318.branchT c i)=oldCoordinate d a t .finite)
  (hP : g (ContactFiniteCoefficientIdentity318.branchP c i)=contactProduct d a t .finite)

/-- Exact identification with the literal original q0 coefficient and
original branch differential, after the actual source map preserves T
and the original contact quartic. This is equality in the true tensor
square, not merely a claimed agreement of rational functions. -/
include hy hn hT hP in
theorem finite_original_q0 : section0 d a t .finite=branchImage c i g := by
  apply FieldContactZoomTensor318.q0_unique d a t .finite y hy hn
  have h := branchImage_cleared c i g
  rw [hT,hP] at h
  exact h

@[expose] def branchImage1 : KaehlerDifferential K (Chart d a t .finite) ⊗[Chart d a t .finite]
    KaehlerDifferential K (Chart d a t .finite) :=
  g (ContactBicanonicalCoefficients318.branchQ1 c i) •
    (KaehlerDifferential.D K _ (g (ContactFrameNormalization318.sourceCoordinate c i)) ⊗ₜ[Chart d a t .finite]
      KaehlerDifferential.D K _ (g (ContactFrameNormalization318.sourceCoordinate c i)))

include hy hn hT hP in
theorem finite_original_q1 : section1 d a t .finite=branchImage1 c i d a t g := by
  rw [finite_section_ratio,finite_original_q0 c i d a t y hy hn g hT hP]
  unfold branchImage1 branchImage
  rw [ContactBicanonicalCoefficients318.branchQ1,map_mul,←mul_smul,hT]
end ContactBicanonicalGenericPullback318
