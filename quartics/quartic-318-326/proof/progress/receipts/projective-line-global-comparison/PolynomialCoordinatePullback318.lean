module
public import ProjectiveLineCoordinates318
public section
noncomputable section
namespace PolynomialCoordinatePullback318
open AlgebraicGeometry CategoryTheory Polynomial
set_option maxHeartbeats 150000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {S : Type} [CommRing S] [Algebra ℚ S]
/-- Evaluation of the actual global affine coordinate under its literal Spec map. -/
theorem coordinate (a : S) :
    (Spec.map (CommRingCat.ofHom (Polynomial.aeval (R:=ℚ) a).toRingHom)).appTop
      ProjectiveLineCoordinates318.coordinate=(Scheme.ΓSpecIso (CommRingCat.of S)).inv a := by
  have h := congrArg (fun f => f X) (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (Polynomial.aeval (R:=ℚ) a).toRingHom))
  have hh := h.symm
  change (Spec.map (CommRingCat.ofHom (Polynomial.aeval (R:=ℚ) a).toRingHom)).appTop
    ProjectiveLineCoordinates318.coordinate=
    (Scheme.ΓSpecIso (CommRingCat.of S)).inv ((Polynomial.aeval (R:=ℚ) a) X) at hh
  rw [Polynomial.aeval_X] at hh
  exact hh
end PolynomialCoordinatePullback318
