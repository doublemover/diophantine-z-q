module
public import OriginalBranchResidueLocal318
public import Mathlib.RingTheory.Localization.Away.Basic
public section
noncomputable section
namespace OriginalBranchCechOverlap318
open OriginalBranchPlaneLocal318 OriginalBranchResidueLocal318 OriginalBranchCechCalculus318 Polynomial
variable {k : Type*} [Field k] {I : Ideal (Plane (k:=k))}
section Common
variable (φ : A I→ₐ[k]k) (y : A I)
variable (B : Type*) [CommRing B] [Algebra (stalk φ) B] [IsLocalization.Away (2*toLocal φ y) B]

@[expose] def restrict : stalk φ→+*B := algebraMap _ _
@[expose] def iy : B :=
  ↑(IsLocalization.Away.algebraMap_isUnit (S:=B) (2*toLocal φ y)).unit⁻¹
theorem iy_spec :
    (2*(restrict φ B (toLocal φ y)))*iy φ y B=1 := by
  have h:=(IsLocalization.Away.algebraMap_isUnit (S:=B) (2*toLocal φ y)).mul_val_inv
  change restrict φ B (2*toLocal φ y)*iy φ y B=1 at h
  rw [map_mul,map_ofNat] at h
  exact h
end Common
/-- The complete overlap computation is in the genuine localization inverting
the ordinary y-Jacobian on the branch stalk. Both lift equations and the
identification of the local logarithmic numerator with the contraction hold. -/
theorem actual_contraction (φ : A I→ₐ[k]k) (x y : A I) (B : Type*) [CommRing B] [Algebra (stalk φ) B]
    [IsLocalization.Away (2*toLocal φ y) B] (F G : k[X]) (i j : ℕ)
    (hu : φ (aeval x F.derivative)≠0) :
    let ψ:=restrict φ B
    let X₀:=ψ (toLocal φ x)
    let y₀:=ψ (toLocal φ y)
    let fp:=ψ (toLocal φ (aeval x F.derivative))
    let g:=ψ (toLocal φ (aeval x G))
    let u:=iy φ y B
    let v:=ψ (invAt φ (aeval x F.derivative) hu)
    (2*y₀)*(u*g)-fp*0=g ∧ (2*y₀)*0-fp*(-v*g)=g ∧
    (2*y₀)*(-(u*g))=fp*(-v*g) ∧
    y₀*((2*X₀^i*v)*(2*X₀^j*v)*(-(u*g)))=ψ (principalNumerator φ x F G i j hu) := by
  dsimp only
  let ψ:=restrict φ B
  have hp : ψ (toLocal φ (aeval x F.derivative))*ψ (invAt φ (aeval x F.derivative) hu)=1 := by
    rw [←map_mul,inverse_spec,map_one]
  obtain ⟨a,b,c⟩:=two_splittings _ _ _ _ _ (iy_spec φ y B) hp
  refine ⟨a,b,c,?_⟩
  rw [simple_pole _ _ _ _ _ (iy_spec φ y B) i j]
  simp only [principalNumerator,map_mul,map_pow]
  have h2 : restrict φ B (-2) = -2 := by
    have h:=map_neg (restrict φ B) (2:stalk φ)
    rw [map_ofNat] at h
    exact h
  rw [h2]
end OriginalBranchCechOverlap318
#print axioms OriginalBranchCechOverlap318.actual_contraction
