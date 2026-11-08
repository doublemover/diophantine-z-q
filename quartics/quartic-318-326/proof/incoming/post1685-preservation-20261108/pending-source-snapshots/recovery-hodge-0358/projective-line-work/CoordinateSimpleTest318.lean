module
public import ProjectiveLineOOne318
public section
noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial
open ProjectiveLineOverlap318
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
@[expose] def coord : Γ(Spec (CommRingCat.of ℚ[X]),⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of ℚ[X])).inv X
example : finiteInclusion.appTop coord=ProjectiveLineOOne318.transition := by
  have h := congrArg (fun f => f X) (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (algebraMap ℚ[X] A)))
  exact h.symm
example : infinityInclusion.appTop coord=(Scheme.ΓSpecIso (CommRingCat.of A)).inv s := by
  have h := congrArg (fun f => f X) (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (Polynomial.aeval (R:=ℚ) s).toRingHom))
  have hh := h.symm
  change infinityInclusion.appTop coord=
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv ((Polynomial.aeval (R:=ℚ) s) X) at hh
  rw [Polynomial.aeval_X] at hh
  exact hh
