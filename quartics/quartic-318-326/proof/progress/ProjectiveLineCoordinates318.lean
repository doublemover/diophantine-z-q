module
public import ProjectiveLineOOne318
public import ClutchedModuleTop318
public section
noncomputable section
namespace ProjectiveLineCoordinates318
open AlgebraicGeometry CategoryTheory Polynomial
open ProjectiveLineOverlap318 ClutchedModule318 ProjectiveLineOOne318
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
@[expose] def coordinate : Γ(Spec (CommRingCat.of ℚ[X]),⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of ℚ[X])).inv X

theorem finite_coordinate : finiteInclusion.appTop coordinate=transition := by
  have h := congrArg (fun f => f X) (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (algebraMap ℚ[X] A)))
  exact h.symm

theorem infinity_coordinate : infinityInclusion.appTop coordinate=
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv s := by
  have h := congrArg (fun f => f X) (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (Polynomial.aeval (R:=ℚ) s).toRingHom))
  have hh := h.symm
  change infinityInclusion.appTop coordinate=
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv ((Polynomial.aeval (R:=ℚ) s) X) at hh
  rw [Polynomial.aeval_X] at hh
  exact hh

/-- Exact compatibility of the X1 local coefficients (1,s). -/
theorem zero_compatible : finiteInclusion.appTop (1:Γ(Spec (CommRingCat.of ℚ[X]),⊤))=
    infinityInclusion.appTop coordinate*transition := by
  rw [map_one,infinity_coordinate]
  change 1=(Scheme.ΓSpecIso (CommRingCat.of A)).inv s*(Scheme.ΓSpecIso (CommRingCat.of A)).inv t
  rw [←map_mul,mul_comm s t,ts,map_one]

/-- Exact compatibility of the X0 local coefficients (t,1). -/
theorem one_compatible : finiteInclusion.appTop coordinate=
    infinityInclusion.appTop (1:Γ(Spec (CommRingCat.of ℚ[X]),⊤))*transition := by
  rw [map_one,one_mul]
  exact finite_coordinate

/-- Actual coordinate sheaf maps, using the generic checked gluing constructor. -/
@[expose] def zeroMap := ClutchedModuleTop318.map
  (JLineAtlas318.chart ℚ 1) (JLineAtlas318.chart ℚ 0)
  finiteInclusion infinityInclusion maps_agree.symm transition
  (1:Γ(Spec (CommRingCat.of ℚ[X]),⊤)) coordinate zero_compatible
@[expose] def oneMap := ClutchedModuleTop318.map
  (JLineAtlas318.chart ℚ 1) (JLineAtlas318.chart ℚ 0)
  finiteInclusion infinityInclusion maps_agree.symm transition
  coordinate (1:Γ(Spec (CommRingCat.of ℚ[X]),⊤)) one_compatible
@[expose] def q0 := ClutchedModuleTop318.sectionTop
  (JLineAtlas318.chart ℚ 1) (JLineAtlas318.chart ℚ 0)
  finiteInclusion infinityInclusion maps_agree.symm transition
  (1:Γ(Spec (CommRingCat.of ℚ[X]),⊤)) coordinate zero_compatible
@[expose] def q1 := ClutchedModuleTop318.sectionTop
  (JLineAtlas318.chart ℚ 1) (JLineAtlas318.chart ℚ 0)
  finiteInclusion infinityInclusion maps_agree.symm transition
  coordinate (1:Γ(Spec (CommRingCat.of ℚ[X]),⊤)) one_compatible

/-- Inferred proof-valued specializations preserve the exact chosen limit
object while certifying all four actual coordinate projections. -/
@[expose] def q0_finite := ClutchedModuleTop318.first_value
  (JLineAtlas318.chart ℚ 1) (JLineAtlas318.chart ℚ 0)
  finiteInclusion infinityInclusion maps_agree.symm transition
  (1:Γ(Spec (CommRingCat.of ℚ[X]),⊤)) coordinate zero_compatible
@[expose] def q0_infinity := ClutchedModuleTop318.second_value
  (JLineAtlas318.chart ℚ 1) (JLineAtlas318.chart ℚ 0)
  finiteInclusion infinityInclusion maps_agree.symm transition
  (1:Γ(Spec (CommRingCat.of ℚ[X]),⊤)) coordinate zero_compatible
@[expose] def q1_finite := ClutchedModuleTop318.first_value
  (JLineAtlas318.chart ℚ 1) (JLineAtlas318.chart ℚ 0)
  finiteInclusion infinityInclusion maps_agree.symm transition
  coordinate (1:Γ(Spec (CommRingCat.of ℚ[X]),⊤)) one_compatible
@[expose] def q1_infinity := ClutchedModuleTop318.second_value
  (JLineAtlas318.chart ℚ 1) (JLineAtlas318.chart ℚ 0)
  finiteInclusion infinityInclusion maps_agree.symm transition
  coordinate (1:Γ(Spec (CommRingCat.of ℚ[X]),⊤)) one_compatible
end ProjectiveLineCoordinates318
