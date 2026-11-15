module
public import PELOriginalCandidateComplexPoints318
public import PELOriginalLevelThreePointSeparation318
public section
noncomputable section
namespace PELOriginalCandidatePointFaithfulness318
open AlgebraicGeometry CategoryTheory
open PELOriginalAllLevelProjectiveMap318 PELOriginalPolarizationTransitions318
open PELOriginalProjectiveCandidatePoints318 PELOriginalCandidateComplexPoints318
open ComplexProjectiveMarkerPoint318

/-- Equal genuine Proj marker points recover the same projective line:
linear homogeneous equations recover every ratio in a single actual
nonvanishing coordinate. No Nullstellensatz or Chow theorem is used. -/
lemma marker_equal_scalar {ι:Type*}(v w:ι→ℂ)(hv:∃j,v j≠0)(hw:∃j,w j≠0)
    (h:point v hv=point w hw):∃c:ℂ,c≠0∧c•v=w:=by
  obtain ⟨j,hj⟩:=hv
  have hwj:w j≠0:=by
    intro hz
    have hm:MvPolynomial.X j∈(point w hw).asHomogeneousIdeal:=
      (variable_mem_iff w j).mpr hz
    rw [←h] at hm
    exact hj ((variable_mem_iff v j).mp hm)
  refine ⟨w j/v j,div_ne_zero hwj hj,?_⟩
  ext i
  let p:MvPolynomial ι ℂ:=MvPolynomial.C (v j)*MvPolynomial.X i-
    MvPolynomial.C (v i)*MvPolynomial.X j
  have hp:p.IsHomogeneous 1:=by
    simpa only [zero_add] using
      ((MvPolynomial.isHomogeneous_C ι (v j)).mul (MvPolynomial.isHomogeneous_X ℂ i)).sub
        ((MvPolynomial.isHomogeneous_C ι (v i)).mul (MvPolynomial.isHomogeneous_X ℂ j))
  have hpv:p∈(point v hv).asHomogeneousIdeal:=by
    apply (homogeneous_mem_iff v hv p 1 hp).mpr
    simp only [p,map_sub,map_mul,MvPolynomial.eval_C,MvPolynomial.eval_X]
    ring
  rw [h] at hpv
  have he: v j*w i-v i*w j=0:=by
    simpa only [p,map_sub,map_mul,MvPolynomial.eval_C,MvPolynomial.eval_X] using
      (homogeneous_mem_iff w hw p 1 hp).mp hpv
  change w j/v j*v i=w i
  calc
    w j/v j*v i=(v i*w j)/v j:=by ring
    _=(v j*w i)/v j:=by rw [←sub_eq_zero.mp he]
    _=w i:=by field_simp [hj]

variable (τ:ℂ)(hτ:0<τ.im)
lemma originalPoint_injective:Function.Injective (originalPoint τ hτ):=by
  intro q r h
  have hs:=marker_equal_scalar (baseVector τ hτ 1 r) (baseVector τ hτ 1 q)
    (actual_coordinate_nonzero τ hτ r) (actual_coordinate_nonzero τ hτ q) h.symm
  obtain ⟨c,hc,he⟩:=hs
  apply PELOriginalLevelThreePointSeparation318.injective τ hτ
  exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨c,he⟩

/-- Pointwise algebraic realization retains all original points, not just
a choice of image set: equality of actual Spec(C)-valued candidate maps
forces equality in the original analytic quotient. No surjectivity onto
the candidate or algebraic structure on that source is inferred. -/
theorem candidateComplexPoint_injective:
    Function.Injective (candidateComplexPoint τ hτ):=by
  intro q r h
  apply originalPoint_injective τ hτ
  let x:ComplexProjectiveSchemePoint318.ComplexPoint:=Classical.choice inferInstance
  rw [←candidateComplexPoint_underlying τ hτ q x,
    ←candidateComplexPoint_underlying τ hτ r x,h]
end PELOriginalCandidatePointFaithfulness318
