module
public import CompletedIntegral318
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public section
noncomputable section
namespace GeometricFibers318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R]

/-- Any field-valued base point has the actual integral completed cubic as fiber. -/
theorem pullback_integral (A B:R) (K:Type u) [Field K]
    (y:Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) :
    IsIntegral (pullback (WeierstrassGluing318.structureMap A B) y) := by
  let φ : R →+* K := (Scheme.Spec.preimage y).unop.hom
  letI : Algebra R K := φ.toAlgebra
  have hy : Spec.map (CommRingCat.ofHom (algebraMap R K))=y := by
    exact Scheme.Spec.map_preimage y
  have := CompletedIntegral318.completed_integral (algebraMap R K A) (algebraMap R K B)
  have h := IsIntegral.of_isIso (WeierstrassBaseChange318.coefficient_base_pullback (S:=K) A B).isoPullback.hom
  simpa only [hy] using h

/-- Geometric integrality of the actual completed family, over the original arbitrary base. -/
theorem geometrically_integral (A B:R) :
    GeometricallyIntegral (WeierstrassGluing318.structureMap A B) := by
  constructor
  intro K _ y Z fst snd h
  have := pullback_integral A B K y
  exact IsIntegral.of_isIso h.isoPullback.inv

/-- In particular every field fiber is connected, without an assumed connectedness hypothesis. -/
theorem geometrically_connected (A B:R) :
    GeometricallyConnected (WeierstrassGluing318.structureMap A B) := by
  constructor
  rw [geometrically_iff_of_isClosedUnderIsomorphisms]
  intro K _ y
  have := pullback_integral A B K y
  infer_instance

/-- The literal integral OpenJ family has geometrically integral fibers. -/
theorem literal_geometrically_integral (N:ℕ) :
    GeometricallyIntegral (WeierstrassGluing318.literalStructureMap N) :=
  geometrically_integral _ _

/-- The exact scheme-theoretic fiber over each prime of the literal base is integral. -/
theorem literal_fiber_integral (N:ℕ) (s:Spec (CommRingCat.of (OpenJModel318.Base N))) :
    IsIntegral ((WeierstrassGluing318.literalStructureMap N).fiber s) := by
  have := literal_geometrically_integral N
  infer_instance

end GeometricFibers318
