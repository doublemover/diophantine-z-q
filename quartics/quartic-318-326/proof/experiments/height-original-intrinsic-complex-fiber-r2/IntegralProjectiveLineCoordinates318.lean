module
public import IntegralProjectiveLineOOne318
public import ClutchedModuleTop318
public section
noncomputable section
namespace IntegralProjectiveLineCoordinates318
open AlgebraicGeometry CategoryTheory Polynomial
open IntegralProjectiveLineOverlap318 ClutchedModule318 IntegralProjectiveLineOOne318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (R : Type*) [CommRing R]
@[expose] def coordinate : Γ(Spec (CommRingCat.of R[X]),⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of R[X])).inv X

theorem finite_coordinate : (finiteInclusion R).appTop (coordinate R)=(transition R) := by
  have h := congrArg (fun f => f X) (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (algebraMap R[X] (A R))))
  exact h.symm

theorem infinity_coordinate : (infinityInclusion R).appTop (coordinate R)=
    (Scheme.ΓSpecIso (CommRingCat.of (A R))).inv (s R) := by
  have h := congrArg (fun f => f X) (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (Polynomial.aeval (R:=R) (s R)).toRingHom))
  have hh := h.symm
  change (infinityInclusion R).appTop (coordinate R)=
    (Scheme.ΓSpecIso (CommRingCat.of (A R))).inv ((Polynomial.aeval (R:=R) (s R)) X) at hh
  rw [Polynomial.aeval_X] at hh
  exact hh

/-- Exact compatibility of the X1 local coefficients (1,s). -/
theorem zero_compatible : (finiteInclusion R).appTop (1:Γ(Spec (CommRingCat.of R[X]),⊤))=
    (infinityInclusion R).appTop (coordinate R)*(transition R) := by
  rw [map_one,(infinity_coordinate R)]
  change 1=(Scheme.ΓSpecIso (CommRingCat.of (A R))).inv (s R)*(Scheme.ΓSpecIso (CommRingCat.of (A R))).inv (t R)
  rw [←map_mul,mul_comm (s R) (t R),(ts R),map_one]

/-- Exact compatibility of the X0 local coefficients (t,1). -/
theorem one_compatible : (finiteInclusion R).appTop (coordinate R)=
    (infinityInclusion R).appTop (1:Γ(Spec (CommRingCat.of R[X]),⊤))*(transition R) := by
  rw [map_one,one_mul]
  exact (finite_coordinate R)

/-- Actual coordinate sheaf maps, using the generic checked gluing constructor. -/
@[expose] def zeroMap := ClutchedModuleTop318.map
  (JLineAtlas318.chart R 1) (JLineAtlas318.chart R 0)
  (finiteInclusion R) (infinityInclusion R) (maps_agree R).symm (transition R)
  (1:Γ(Spec (CommRingCat.of R[X]),⊤)) (coordinate R) (zero_compatible R)
@[expose] def oneMap := ClutchedModuleTop318.map
  (JLineAtlas318.chart R 1) (JLineAtlas318.chart R 0)
  (finiteInclusion R) (infinityInclusion R) (maps_agree R).symm (transition R)
  (coordinate R) (1:Γ(Spec (CommRingCat.of R[X]),⊤)) (one_compatible R)
@[expose] def q0 := ClutchedModuleTop318.sectionTop
  (JLineAtlas318.chart R 1) (JLineAtlas318.chart R 0)
  (finiteInclusion R) (infinityInclusion R) (maps_agree R).symm (transition R)
  (1:Γ(Spec (CommRingCat.of R[X]),⊤)) (coordinate R) (zero_compatible R)
@[expose] def q1 := ClutchedModuleTop318.sectionTop
  (JLineAtlas318.chart R 1) (JLineAtlas318.chart R 0)
  (finiteInclusion R) (infinityInclusion R) (maps_agree R).symm (transition R)
  (coordinate R) (1:Γ(Spec (CommRingCat.of R[X]),⊤)) (one_compatible R)

/-- Inferred proof-valued specializations preserve the exact chosen limit
object while certifying all four actual coordinate projections. -/
@[expose] def q0_finite := ClutchedModuleTop318.first_value
  (JLineAtlas318.chart R 1) (JLineAtlas318.chart R 0)
  (finiteInclusion R) (infinityInclusion R) (maps_agree R).symm (transition R)
  (1:Γ(Spec (CommRingCat.of R[X]),⊤)) (coordinate R) (zero_compatible R)
@[expose] def finite_coordinate0 := ClutchedModuleTop318.second_value
  (JLineAtlas318.chart R 1) (JLineAtlas318.chart R 0)
  (finiteInclusion R) (infinityInclusion R) (maps_agree R).symm (transition R)
  (1:Γ(Spec (CommRingCat.of R[X]),⊤)) (coordinate R) (zero_compatible R)
@[expose] def finite_coordinate1 := ClutchedModuleTop318.first_value
  (JLineAtlas318.chart R 1) (JLineAtlas318.chart R 0)
  (finiteInclusion R) (infinityInclusion R) (maps_agree R).symm (transition R)
  (coordinate R) (1:Γ(Spec (CommRingCat.of R[X]),⊤)) (one_compatible R)
@[expose] def finite_coordinate2 := ClutchedModuleTop318.second_value
  (JLineAtlas318.chart R 1) (JLineAtlas318.chart R 0)
  (finiteInclusion R) (infinityInclusion R) (maps_agree R).symm (transition R)
  (coordinate R) (1:Γ(Spec (CommRingCat.of R[X]),⊤)) (one_compatible R)
end IntegralProjectiveLineCoordinates318
