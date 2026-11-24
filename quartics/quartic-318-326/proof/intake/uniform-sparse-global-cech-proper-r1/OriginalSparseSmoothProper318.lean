module
public import OriginalSparseProperModel318
public import OriginalSparseReciprocalSmooth318
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! The genuine smooth proper double cover for every eligible
literal sparse specialization. No Picard scheme is inferred here. -/
public section
noncomputable section
namespace OriginalSparseSmoothProper318

open AlgebraicGeometry CategoryTheory
open OriginalSparseGluedScheme318 OriginalSparseQuadraticCharts318
open OriginalUniformSparseSmoothChart318 (delta collision unit_of_igusa)
universe u
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R : Type u} [CommRing R] (s t : R)

@[expose] def coverObject : Bool → Scheme
  | false => finiteScheme s t
  | true => infinityScheme s t
@[expose] def embedding : (b : Bool) → coverObject s t b ⟶ scheme s t
  | false => finiteChart s t
  | true => infinityChart s t

@[expose] def cover : (scheme s t).OpenCover where
  I₀:=Bool
  X:=coverObject s t
  f:=embedding s t
  mem₀:=by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    constructor
    · intro p
      rcases charts_cover s t p with ⟨x,hx⟩|⟨x,hx⟩
      · exact ⟨false,x,hx⟩
      · exact ⟨true,x,hx⟩
    · intro b
      cases b
      · exact finiteChart_open s t
      · exact infinityChart_open s t

theorem structure_smooth (h2 : IsUnit (2:R)) (hw : IsUnit (5-s*t))
    (hδ : IsUnit (delta s t)) (hδ' : IsUnit (delta t s)) :
    Smooth (structureMap s t) := by
  apply IsZariskiLocalAtSource.of_openCover (P:=@Smooth) (cover s t)
  intro b
  cases b
  · change Smooth (finiteChart s t ≫ structureMap s t)
    rw [finite_structure]
    exact (HasRingHomProperty.Spec_iff (P:=@Smooth)).mpr
      (RingHom.smooth_algebraMap.mpr (OriginalSparseReciprocalSmooth318.finite_smooth s t h2 hδ))
  · change Smooth (infinityChart s t ≫ structureMap s t)
    rw [infinity_structure]
    exact (HasRingHomProperty.Spec_iff (P:=@Smooth)).mpr
      (RingHom.smooth_algebraMap.mpr (OriginalSparseReciprocalSmooth318.infinity_smooth s t h2 hw hδ'))

section Field
variable {K : Type u} [Field K] [CharZero K]

theorem swapped_nonzero (s t : K)
    (h : OriginalUniformSparseIgusa318.i10 s t ≠ 0) :
    OriginalUniformSparseIgusa318.i10 t s ≠ 0 := by
  have hst : OriginalUniformSparseIgusa318.i10 t s = OriginalUniformSparseIgusa318.i10 s t := by
    rw [(OriginalUniformSparseIgusa318.reads_factored t s).2.2.2,
      (OriginalUniformSparseIgusa318.reads_factored s t).2.2.2]
    ring
  exact hst.symm ▸ h

theorem weight_unit (s t : K) (h : OriginalUniformSparseIgusa318.i10 s t ≠ 0) :
    IsUnit (5-s*t) := by
  apply isUnit_iff_ne_zero.mpr
  intro hz
  have hz' : s*t-5=0 := by linear_combination -hz
  have hx := (OriginalUniformSparseIgusa318.reads_factored s t).2.2.2
  change OriginalUniformSparseIgusa318.i10 s t =
    200000*(collision s t)^2*(s*t)^10*(s*t-5)^10 at hx
  rw [hx,hz',zero_pow (by decide : 10≠0),mul_zero] at h
  exact h rfl

/-- Every actual nonexception characteristic-zero sparse fibre is smooth
and proper on the very glued scheme used by its differential frames. -/
theorem smooth_proper_of_igusa (s t : K) (h : OriginalUniformSparseIgusa318.i10 s t ≠ 0) :
    Smooth (structureMap s t) ∧ IsProper (structureMap s t) :=
  ⟨structure_smooth s t (isUnit_iff_ne_zero.mpr (by norm_num)) (weight_unit s t h)
    (unit_of_igusa s t h) (unit_of_igusa t s (swapped_nonzero s t h)),
    OriginalSparseProperModel318.structure_proper s t⟩

end Field
end OriginalSparseSmoothProper318

#print axioms OriginalSparseSmoothProper318.smooth_proper_of_igusa
