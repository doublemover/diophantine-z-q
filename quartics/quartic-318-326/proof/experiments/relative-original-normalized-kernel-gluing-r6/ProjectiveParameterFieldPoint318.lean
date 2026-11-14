module
public import ProjectiveParameterSliceSchemes318
public section
noncomputable section
namespace ProjectiveParameterFieldPoint318
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
variable (R : CommRingCat.{0}) (P : Type) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
variable (K : CommRingCat.{0}) [Field K] [Algebra R K]
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P

/-- A nonzero ACTUAL tensor section over a field chooses a genuine
coordinate-one slice, using a nonzero coordinate only where it is a unit. -/
lemma exists_slice (v : K ⊗[R] P) (hv : v≠0) :
    ∃ i : Fin F.size, Nonempty (ProjectiveParameterSliceAlgebra318.algebra R P i →ₐ[R] K) := by
  let a := (ProjectiveSectionParameter318.points R P K).symm v
  have ha : ProjectiveSectionParameter318.points R P K a≠0 := by
    simpa only [a,Equiv.apply_symm_apply] using hv
  obtain ⟨i,hi⟩ := (ProjectiveParameterZeroCoordinates318.nonzero_iff R P K a).mp ha
  let u : Kˣ := Units.mk0 (a (ProjectiveParameterZeroCoordinates318.coordinate R P i)) hi
  let cp : ProjectiveParameterUnitSlice318.ChartPoint R P K i := ⟨a,u,rfl⟩
  exact ⟨i,⟨ProjectiveParameterSliceAlgebra318.backward R P i K
    (ProjectiveParameterUnitSlice318.normalize R P K i cp)⟩⟩

/-- The normalized slice point is a morphism over the ORIGINAL field
coefficient map, not merely a set-theoretic nonempty fiber. -/
lemma exists_chart_map (v : K ⊗[R] P) (hv : v≠0) :
    ∃ (i : Fin F.size) (g : Spec K ⟶ ProjectiveParameterSliceSchemes318.chart R P i),
      g ≫ ProjectiveParameterSliceSchemes318.projection R P i=
        Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
  obtain ⟨i,⟨a⟩⟩ := exists_slice R P K v hv
  refine ⟨i,Spec.map (CommRingCat.ofHom a.toRingHom),?_⟩
  rw [ProjectiveParameterSliceSchemes318.projection,← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact a.commutes r
end ProjectiveParameterFieldPoint318
