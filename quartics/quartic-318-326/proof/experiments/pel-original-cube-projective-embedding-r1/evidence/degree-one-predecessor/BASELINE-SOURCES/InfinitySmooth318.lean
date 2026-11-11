module
public import WeierstrassOverlap318
public import ShortAffineScheme318
public section
noncomputable section
namespace InfinitySmooth318
open InfinityChart318 Algebra
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type*} [CommRing R]

/-- The finite-chart overlap and the explicit infinity Jacobian open cover the whole Y=1 chart. -/
theorem cover_span (A B : R) :
    Ideal.span ({z A B,(presentation A B).jacobian} : Set (Ring A B))=⊤ := by
  let I := Ideal.span ({z A B,(presentation A B).jacobian} : Set (Ring A B))
  apply I.eq_top_iff_one.mpr
  have hz : z A B ∈ I := Ideal.subset_span (by simp)
  have hj : (presentation A B).jacobian ∈ I := Ideal.subset_span (by simp)
  have h := I.add_mem hj (I.mul_mem_left
    (2*algebraMap R (Ring A B) A*x A B+3*algebraMap R (Ring A B) B*z A B) hz)
  rw [jacobian_formula] at h
  convert h using 1; ring

/-- The entire actual infinity coordinate ring is smooth, not just its Jacobian open. -/
theorem smooth (A B : R) (hD : IsUnit (-16*(4*A^3+27*B^2))) : Algebra.Smooth R (Ring A B) := by
  have hAff := ShortAffineJacobian318.smooth A B hD
  have hAO : Algebra.Smooth R (WeierstrassOverlap318.AffineOverlap A B) :=
    Algebra.Smooth.comp R (ShortAffineJacobian318.Ring A B) _
  have hIO : Algebra.Smooth R (WeierstrassOverlap318.InfinityOverlap A B) :=
    Algebra.Smooth.of_equiv (WeierstrassOverlap318.overlapEquiv A B).symm
  rw [←RingHom.smooth_algebraMap]
  apply RingHom.Smooth.ofLocalizationSpanTarget _ {z A B,(presentation A B).jacobian} (cover_span A B)
  rintro ⟨r,hr⟩
  rcases Set.mem_insert_iff.mp hr with rfl|hr
  · rw [←IsScalarTower.algebraMap_eq,RingHom.smooth_algebraMap]
    exact hIO
  · have he : r=(presentation A B).jacobian := Set.mem_singleton_iff.mp hr
    subst r
    rw [←IsScalarTower.algebraMap_eq,RingHom.smooth_algebraMap]
    exact InfinityChart318.smooth A B

open CategoryTheory AlgebraicGeometry
abbrev scheme (A B : R) : Scheme := Spec (CommRingCat.of (Ring A B))
@[expose] def structureMap (A B : R) : scheme A B ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (Ring A B)))
@[expose] def infinity (A B : R) : Spec (CommRingCat.of R) ⟶ scheme A B :=
  Spec.map (CommRingCat.ofHom (origin A B).toRingHom)

theorem structure_smooth (A B : R) (hD : IsUnit (-16*(4*A^3+27*B^2))) :
    AlgebraicGeometry.Smooth (structureMap A B) := by
  apply HasRingHomProperty.Spec_iff.mpr
  exact RingHom.smooth_algebraMap.mpr (smooth A B hD)

theorem infinity_section (A B : R) : infinity A B ≫ structureMap A B=𝟙 _ := by
  unfold infinity structureMap
  rw [←Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((origin A B).toRingHom.comp
    (algebraMap R (Ring A B))))=𝟙 _
  have h : (origin A B).toRingHom.comp (algebraMap R (Ring A B))=RingHom.id R := by
    ext r
    exact (origin A B).commutes r
  rw [h]
  exact Spec.map_id _

theorem infinity_closed (A B : R) : IsClosedImmersion (infinity A B) := by
  apply IsClosedImmersion.spec_of_surjective
  intro r
  exact ⟨algebraMap R (Ring A B) r,(origin A B).commutes r⟩

end InfinitySmooth318
