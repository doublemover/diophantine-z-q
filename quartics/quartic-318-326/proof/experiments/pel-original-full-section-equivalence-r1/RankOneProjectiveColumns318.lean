module
public import ComplexProjectivePointEquality318
public section
noncomputable section
namespace RankOneProjectiveColumns318
open AlgebraicGeometry CategoryTheory
variable {ι κ : Type*}

/-- Every pair of nonzero columns of a rank-at-most-one matrix gives
the same projective class. Zero columns are not silently selected. -/
theorem projective_columns (m : ι → κ → ℂ)
    (hm : ∀ i j s t, m i s*m j t=m i t*m j s)
    (s t : κ) (hs : ∃ i,m i s≠0) (ht : ∃ i,m i t≠0) :
    Projectivization.mk ℂ (fun i => m i s)
      (ComplexProjectivePointEquality318.vector_nonzero _ hs)=
    Projectivization.mk ℂ (fun i => m i t)
      (ComplexProjectivePointEquality318.vector_nonzero _ ht) := by
  obtain ⟨j,hj⟩ := ht
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨m j s/m j t,?_⟩
  funext i
  change (m j s/m j t)*m i t=m i s
  rw [div_mul_eq_mul_div]
  apply (div_eq_iff hj).mpr
  exact (mul_comm _ _).trans (hm i j t s)

theorem scheme_columns [Finite ι] (m : ι → κ → ℂ)
    (hm : ∀ i j s t, m i s*m j t=m i t*m j s)
    (s t : κ) (hs : ∃ i,m i s≠0) (ht : ∃ i,m i t≠0) :
    ComplexProjectiveSchemePoint318.point (fun i => m i s) hs=
      ComplexProjectiveSchemePoint318.point (fun i => m i t) ht :=
  ComplexProjectivePointEquality318.scheme_point_eq _ _ hs ht (projective_columns m hm s t hs ht)

/-- A nonzero Segre column recovers the first factor. This is the exact
sum/difference tensor specialization needed by the algebraic addition
map, with every nonzero scalar retained. -/
theorem scheme_segre_column [Finite ι] (a : ι → ℂ) (b : κ → ℂ)
    (ha : ∃ i,a i≠0) (s : κ) (hs : ∃ i,a i*b s≠0) :
    ComplexProjectiveSchemePoint318.point (fun i => a i*b s) hs=
      ComplexProjectiveSchemePoint318.point a ha := by
  apply ComplexProjectivePointEquality318.scheme_point_eq
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨b s,?_⟩
  funext i
  exact mul_comm _ _
end RankOneProjectiveColumns318
