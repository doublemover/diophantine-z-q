module
public import OriginalMarkedBranchMap318
public import ContactBicanonicalGenericPullback318
public import UnitReciprocalDifferential318
public section
noncomputable section
namespace OriginalReciprocalZoomBranchMap318
open Polynomial IntegralContactZoomCoefficients318
open scoped TensorProduct
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K] [CharZero K]
  (c : Fin 4 → ℚˣ) (d : Fin 4 → K) (t : K) (y s : Fin 4 → K)
  (hs : ∀ i,s i≠0)
  (hc : ∀ i,algebraMap ℚ K (c i : ℚ)=d i*(s i)^2)
abbrev contacts : Fin 4 → K := fun i => algebraMap ℚ K (LinearContactSquareclass318.contacts i)
abbrev Target := Chart d (contacts (K:=K)) t .reciprocal
variable (hy : ∀ i,(y i)^2=IntegralQuadraticPointZoom318.value
  (alpha d (contacts (K:=K)) .reciprocal) d (gamma d (contacts (K:=K)) .reciprocal) t i)
  (hn : ∀ i,y i≠0)

include hy hn in
theorem coordinate_unit : IsUnit (oldCoordinate d (contacts (K:=K)) t .reciprocal) := by
  have h := (FieldContactZoomTensor318.original_root_unit d (contacts (K:=K)) t .reciprocal y hn 0).pow 2
  rw [IntegralContactZoomCoefficients318.original_root_square d (contacts (K:=K)) t .reciprocal y hy 0] at h
  exact isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left h)
@[expose] def coordinateUnit : (Target d t)ˣ := (coordinate_unit d t y hy hn).unit

theorem coordinateUnit_val : (coordinateUnit d t y hy hn : Target d t)=
    oldCoordinate d (contacts (K:=K)) t .reciprocal := (coordinate_unit d t y hy hn).unit_spec
@[expose] def originalRoot (i : Fin 4) : Target d t :=
  algebraMap K (Target d t) (s i)*(↑(coordinateUnit d t y hy hn)⁻¹ : Target d t)*
    IntegralZoomNeighborhood318.oldRoot K (alpha d (contacts (K:=K)) .reciprocal)
      d (gamma d (contacts (K:=K)) .reciprocal) t y i

include hc in
theorem originalRoot_equation (i : Fin 4) : (originalRoot d t y s hy hn i)^2=
    algebraMap ℚ (Target d t) (c i : ℚ)*
      ((↑(coordinateUnit d t y hy hn)⁻¹ : Target d t)-
        algebraMap ℚ (Target d t) (LinearContactSquareclass318.contacts i)) := by
  have hr := IntegralContactZoomCoefficients318.original_root_square d (contacts (K:=K)) t .reciprocal y hy i
  have hcoef : algebraMap ℚ (Target d t) (c i : ℚ)=
      algebraMap K (Target d t) (d i)*(algebraMap K (Target d t) (s i))^2 := by
    rw [IsScalarTower.algebraMap_apply ℚ K (Target d t),hc i,map_mul,map_pow]
  have hu : (↑(coordinateUnit d t y hy hn)⁻¹ : Target d t)*
      oldCoordinate d (contacts (K:=K)) t .reciprocal=1 := by
    rw [←coordinateUnit_val]
    exact Units.inv_mul _
  rw [originalRoot,mul_pow,mul_pow,hr,hcoef]
  simp only [contactFactor,contacts,←IsScalarTower.algebraMap_apply]
  linear_combination
    (algebraMap K (Target d t) (d i)*(algebraMap K (Target d t) (s i))^2*
      (↑(coordinateUnit d t y hy hn)⁻¹ : Target d t)*
        (1-algebraMap ℚ (Target d t) (LinearContactSquareclass318.contacts i)*
          oldCoordinate d (contacts (K:=K)) t .reciprocal))*hu -
    (algebraMap K (Target d t) (d i)*(algebraMap K (Target d t) (s i))^2*
      algebraMap ℚ (Target d t) (LinearContactSquareclass318.contacts i))*hu

include hs in
theorem originalRoot_unit (i : Fin 4) : IsUnit (originalRoot d t y s hy hn i) :=
  (((IsUnit.mk0 (s i) (hs i)).map (algebraMap K (Target d t))).mul
    (coordinateUnit d t y hy hn)⁻¹.isUnit).mul
      (FieldContactZoomTensor318.original_root_unit d (contacts (K:=K)) t .reciprocal y hn i)

@[expose] def branchMap (i : Fin 4) : ContactBicanonicalCoefficients318.BranchRing c i →ₐ[ℚ] Target d t :=
  OriginalMarkedBranchMap318.branchMap c (↑(coordinateUnit d t y hy hn)⁻¹ : Target d t)
    (originalRoot d t y s hy hn) (originalRoot_equation c d t y s hc hy hn)
    (originalRoot_unit d t y s hs hy hn) i

theorem branchMap_T (i : Fin 4) : branchMap c d t y s hs hc hy hn i
    (ContactBicanonicalCoefficients318.branchT c i)=(↑(coordinateUnit d t y hy hn)⁻¹ : Target d t) :=
  OriginalMarkedBranchMap318.branchMap_T _ _ _ _ _ i

theorem branchMap_P (i : Fin 4) : branchMap c d t y s hs hc hy hn i
    (ContactFiniteCoefficientIdentity318.branchP c i)=
      (↑(coordinateUnit d t y hy hn)⁻¹ : Target d t)^4*
        contactProduct d (contacts (K:=K)) t .reciprocal := by
  rw [branchMap,OriginalMarkedBranchMap318.branchMap_P]
  rw [UnitReciprocalDifferential318.contact_product]
  simp only [contactProduct,contactFactor,contacts,←coordinateUnit_val,
    ←IsScalarTower.algebraMap_apply]

theorem original_q0 (i : Fin 4) : section0 d (contacts (K:=K)) t .reciprocal=
    ContactBicanonicalGenericPullback318.branchImage c i (branchMap c d t y s hs hc hy hn i) := by
  apply FieldContactZoomTensor318.q0_unique d (contacts (K:=K)) t .reciprocal y hy hn
  have h := ContactBicanonicalGenericPullback318.branchImage_cleared c i
    (branchMap c d t y s hs hc hy hn i)
  rw [branchMap_T,branchMap_P,UnitReciprocalDifferential318.tensor_square] at h
  rw [mul_smul] at h
  have hh := ((coordinateUnit d t y hy hn)⁻¹.isUnit.pow 4).smul_left_cancel.mp h
  simpa only [coordinateUnit_val] using hh

@[expose] def branchImage1 (i : Fin 4) :
    KaehlerDifferential K (Target d t) ⊗[Target d t] KaehlerDifferential K (Target d t) :=
  branchMap c d t y s hs hc hy hn i (ContactBicanonicalCoefficients318.branchQ1 c i) •
    (KaehlerDifferential.D K _ (branchMap c d t y s hs hc hy hn i
      (ContactFrameNormalization318.sourceCoordinate c i)) ⊗ₜ[Target d t]
    KaehlerDifferential.D K _ (branchMap c d t y s hs hc hy hn i
      (ContactFrameNormalization318.sourceCoordinate c i)))

theorem original_q1 (i : Fin 4) : section1 d (contacts (K:=K)) t .reciprocal=
    branchImage1 c d t y s hs hc hy hn i := by
  apply (coordinate_unit d t y hy hn).smul_left_cancel.mp
  rw [reciprocal_section_ratio,original_q0 c d t y s hs hc hy hn i]
  unfold branchImage1
  rw [ContactBicanonicalCoefficients318.branchQ1,map_mul,branchMap_T,mul_smul,←smul_smul]
  have hu : oldCoordinate d (contacts (K:=K)) t .reciprocal*
      (↑(coordinateUnit d t y hy hn)⁻¹ : Target d t)=1 := by
    rw [←coordinateUnit_val]
    exact Units.mul_inv _
  rw [hu,one_smul]
  rfl
end OriginalReciprocalZoomBranchMap318
