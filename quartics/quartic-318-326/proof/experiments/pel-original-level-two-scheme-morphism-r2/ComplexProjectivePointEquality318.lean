module
public import ComplexProjectiveBase318
public import HomogeneousEvaluationScaling318
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public section
noncomputable section
namespace ComplexProjectivePointEquality318
open AlgebraicGeometry CategoryTheory ComplexProjectiveMarkerPoint318
variable {ι : Type*}

lemma vector_nonzero (v : ι → ℂ) (hv : ∃ i,v i≠0) : v≠0 := by
  obtain ⟨i,hi⟩ := hv
  intro h
  exact hi (congrFun h i)

/-- The genuine homogeneous prime remembers the FULL projective class.
Linear homogeneous tests already recover a common nonzero scaling. -/
theorem projective_of_marker (v w : ι → ℂ) (hv : ∃ i,v i≠0) (hw : ∃ i,w i≠0)
    (h : point v hv=point w hw) :
    Projectivization.mk ℂ v (vector_nonzero v hv)=
      Projectivization.mk ℂ w (vector_nonzero w hw) := by
  obtain ⟨j,hj⟩ := hv
  have hmem (p : MvPolynomial ι ℂ) (hp : p.IsHomogeneous 1) :
      MvPolynomial.eval v p=0 ↔ MvPolynomial.eval w p=0 := by
    rw [←homogeneous_mem_iff v hv p 1 hp,←homogeneous_mem_iff w hw p 1 hp,h]
  have hwj : w j≠0 := by
    intro hz
    apply hj
    have ht := (hmem (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X ℂ j)).mpr
      (by simpa using hz)
    simpa using ht
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨v j/w j,?_⟩
  funext i
  let p : MvPolynomial ι ℂ :=
    MvPolynomial.C (w j)*MvPolynomial.X i-MvPolynomial.C (w i)*MvPolynomial.X j
  have hp : p.IsHomogeneous 1 := by
    exact ((MvPolynomial.isHomogeneous_C ι (w j)).mul
      (MvPolynomial.isHomogeneous_X ℂ i)).sub
      ((MvPolynomial.isHomogeneous_C ι (w i)).mul (MvPolynomial.isHomogeneous_X ℂ j))
  have hz : MvPolynomial.eval w p=0 := by simp [p]; ring
  have he := (hmem p hp).mpr hz
  simp only [p,map_sub,map_mul,MvPolynomial.eval_C,MvPolynomial.eval_X] at he
  change (v j/w j)*w i=v i
  rw [div_mul_eq_mul_div]
  apply (div_eq_iff hwj).mpr
  calc
    v j*w i = w i*v j := mul_comm _ _
    _ = w j*v i := (sub_eq_zero.mp he).symm
    _ = v i*w j := mul_comm _ _

lemma marker_of_projective (v w : ι → ℂ) (hv : ∃ i,v i≠0) (hw : ∃ i,w i≠0)
    (h : Projectivization.mk ℂ v (vector_nonzero v hv)=
      Projectivization.mk ℂ w (vector_nonzero w hw)) : point v hv=point w hw := by
  obtain ⟨c,hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp h
  have hc0 : c≠0 := by
    intro hz
    have he : v=0 := by rw [←hc,hz,zero_smul]
    exact vector_nonzero v hv he
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro n p hp
  rw [homogeneous_mem_iff,homogeneous_mem_iff]
  have he : v=fun i => c*w i := hc.symm
  rw [he,HomogeneousEvaluationScaling318.evaluate_scale p n hp]
  exact mul_eq_zero.trans (or_iff_right (pow_ne_zero n hc0))

/-- Equality of ordinary projective classes yields equality of the
actual over-C Spec(C) morphisms, with no choice of affine chart. -/
theorem scheme_point_eq [Finite ι] (v w : ι → ℂ) (hv : ∃ i,v i≠0) (hw : ∃ i,w i≠0)
    (h : Projectivization.mk ℂ v (vector_nonzero v hv)=
      Projectivization.mk ℂ w (vector_nonzero w hw)) :
    ComplexProjectiveSchemePoint318.point v hv=ComplexProjectiveSchemePoint318.point w hw := by
  apply ext_of_apply_closedPoint_eq ComplexProjectiveBase318.structureMap
    (ComplexProjectiveBase318.point_over _ _) (ComplexProjectiveBase318.point_over _ _)
  rw [ComplexProjectiveSchemePoint318.underlying_point,
    ComplexProjectiveSchemePoint318.underlying_point]
  exact marker_of_projective v w hv hw h
end ComplexProjectivePointEquality318
