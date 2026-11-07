module
public import ReciprocalCover318
public import OpenJProjectiveMap318
public section
noncomputable section
namespace ReciprocalProjective318
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
variable (N:ℕ) (B:Type) [CommRing B] [Algebra (OpenJModel318.Base N) B]

/-- Exact actual second-chart factorization of the already constructed
source map, using precisely the polynomial scalar map whose finite normal
model was proved in ReciprocalCover318. -/
theorem coverMap_infinity : OpenJProjectiveMap318.coverMap N B=
    Spec.map (CommRingCat.ofHom (ReciprocalCover318.polynomialMap N B)) ≫
      JLineAtlas318.chart ℤ 0 := by
  rw [OpenJProjectiveMap318.coverMap_at_infinity,←Category.assoc,←Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro z
    simp [ReciprocalCover318.polynomialMap,ReciprocalCover318.coverHom]
  · simpa [ReciprocalJ318.zeroUnit] using (ReciprocalCover318.polynomial_coordinate N B).symm

/-- This exact reciprocal factor is genuinely finite type and quasi-finite. -/
theorem infinity_local_properties [Module.Finite (OpenJModel318.Base N) B] :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (ReciprocalCover318.polynomialMap N B))) ∧
    LocallyQuasiFinite (Spec.map (CommRingCat.ofHom (ReciprocalCover318.polynomialMap N B))) := by
  letI : IsFinite (Spec.map (CommRingCat.ofHom (ReciprocalCover318.coverHom N B))) :=
    (IsFinite.SpecMap_iff _).mpr (ReciprocalCover318.finite N B)
  unfold ReciprocalCover318.polynomialMap
  rw [CommRingCat.ofHom_comp,Spec.map_comp]
  exact ⟨inferInstance,inferInstance⟩

end ReciprocalProjective318
