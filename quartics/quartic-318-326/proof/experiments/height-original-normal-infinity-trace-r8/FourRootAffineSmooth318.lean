module
public import FourRootActualGenericField318
public import JacobianLocalSmooth318
public import SmoothDomainNormal318
public section
noncomputable section
namespace FourRootAffineSmooth318
open Algebra MvPolynomial FourRootAffineCoordinateRing318
variable (b:Fin 4→ℂ) (hb:Function.Injective b)

/-- At the j-th branch one solves the j-th equation for t and the other
three equations for their actual nonzero roots. -/
@[expose] def chosen (j k:Fin 4):Option (Fin 4):=if k=j then none else some k
lemma chosen_injective (j:Fin 4):Function.Injective (chosen j):=by
  intro k l h
  by_cases hk:k=j <;> by_cases hl:l=j <;> simp_all [chosen]

@[expose] def presentation (j:Fin 4):PreSubmersivePresentation ℂ (Ring b) (Option (Fin 4)) (Fin 4):=
  PreSubmersivePresentation.naive (v:=equation b) (chosen j) (chosen_injective j)

/-- The branch minors are the true four-by-four Jacobian determinants,
including their factor -8. They omit exactly the potentially zero root. -/
theorem jacobian_formula (j:Fin 4):(presentation b j).jacobian=
    -8*∏k:Fin 3,coordinate b (some (j.succAbove k)):=by
  have hmatrix : (presentation b j).jacobiMatrix =
      fun k l : Fin 4 => pderiv (chosen j k) (equation b l) := by
    ext k l
    simp only [presentation,PreSubmersivePresentation.jacobiMatrix_naive]
  have hsucc : ∀ (r : Fin 4) (k : Fin 3), r.succAbove k =
      (![![(1:Fin 4),2,3],![0,2,3],![0,1,3],![0,1,2]] : Fin 4 → Fin 3 → Fin 4) r k := by
    decide
  rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,hmatrix]
  change Ideal.Quotient.mk (Ideal.span (Set.range (equation b)))
    (Matrix.det (fun k l : Fin 4 => pderiv (chosen j k) (equation b l))) = _
  rw [Matrix.det_succ_row_zero]
  fin_cases j <;>
    simp [chosen,equation,hsucc,Matrix.det_fin_three,Matrix.submatrix_apply,
      coordinate,Fin.prod_univ_succ,Fin.sum_univ_succ] <;> ring

lemma scalar_not_mem (p:PrimeSpectrum (Ring b)) (c:ℂ) (hc:c≠0):
    algebraMap ℂ (Ring b) c∉p.asIdeal:=by
  intro h
  exact p.isPrime.ne_top (p.asIdeal.eq_top_of_isUnit_mem h
    ((IsUnit.mk0 c hc).map (algebraMap ℂ (Ring b))))

lemma distinct_roots_not_both (hb:Function.Injective b) (p:PrimeSpectrum (Ring b)) {i j:Fin 4} (hij:i≠j)
    (hi:coordinate b (some i)∈p.asIdeal):coordinate b (some j)∉p.asIdeal:=by
  intro hj
  have hi2:=p.asIdeal.mul_mem_left (coordinate b (some i)) hi
  have hj2:=p.asIdeal.mul_mem_left (coordinate b (some j)) hj
  have hd:=p.asIdeal.sub_mem hi2 hj2
  have he:coordinate b (some i)*coordinate b (some i)-
      coordinate b (some j)*coordinate b (some j)=algebraMap ℂ (Ring b) (b j-b i):=by
    rw [←pow_two,←pow_two,relation,relation,map_sub]
    ring
  rw [he] at hd
  exact scalar_not_mem b p (b j-b i) (sub_ne_zero.mpr (hb.ne hij.symm)) hd

lemma branch_minor_not_mem (p:PrimeSpectrum (Ring b)) (j:Fin 4)
    (h:∀k,k≠j→coordinate b (some k)∉p.asIdeal):
    (presentation b j).jacobian∉p.asIdeal:=by
  rw [jacobian_formula]
  have hc:(-8:Ring b)∉p.asIdeal:=by
    simpa only [map_neg,map_ofNat] using scalar_not_mem b p (-8:ℂ) (by norm_num)
  have hp:∏k:Fin 3,coordinate b (some (j.succAbove k))∉p.asIdeal:=by
    have aux:∀s:Finset (Fin 3),(∀k∈s,coordinate b (some (j.succAbove k))∉p.asIdeal)→
        ∏k∈s,coordinate b (some (j.succAbove k))∉p.asIdeal:=by
      intro s
      induction s using Finset.induction_on with
      | empty=>
        intro _
        simpa only [Finset.prod_empty,map_one] using scalar_not_mem b p (1:ℂ) one_ne_zero
      | @insert k s hks ih=>
        intro hh
        rw [Finset.prod_insert hks,p.isPrime.mul_mem_iff_mem_or_mem,not_or]
        exact ⟨hh k (Finset.mem_insert_self _ _),ih (fun l hl=>hh l (Finset.mem_insert_of_mem hl))⟩
    exact aux _ (fun k _=>h (j.succAbove k) (Fin.succAbove_ne j k))
  simpa only [p.isPrime.mul_mem_iff_mem_or_mem,not_or] using And.intro hc hp

theorem jacobian_span (hb:Function.Injective b):Ideal.span (Set.range (fun j:Fin 4=>(presentation b j).jacobian))=⊤:=by
  by_contra htop
  obtain ⟨m,hm,hle⟩:=Ideal.exists_le_maximal _ htop
  let p:PrimeSpectrum (Ring b):=⟨m,hm.isPrime⟩
  have exists_minor:∃j,(presentation b j).jacobian∉p.asIdeal:=by
    by_cases h:∃j,coordinate b (some j)∈p.asIdeal
    · obtain ⟨j,hj⟩:=h
      exact ⟨j,branch_minor_not_mem b p j (fun k hkj=>distinct_roots_not_both b hb p hkj.symm hj)⟩
    · push_neg at h
      exact ⟨0,branch_minor_not_mem b p 0 (fun k _=>h k)⟩
  obtain ⟨j,hj⟩:=exists_minor
  exact hj (hle (Ideal.subset_span ⟨j,rfl⟩))

/-- Smoothness of the WHOLE independent affine chart follows from the
actual branch-minor cover, not just its unramified locus. -/
theorem smooth (hb:Function.Injective b):Algebra.Smooth ℂ (Ring b):=by
  rw [←RingHom.smooth_algebraMap,RingHom.smooth_iff_locally_isStandardSmooth]
  refine ⟨Set.range (fun j:Fin 4=>(presentation b j).jacobian),jacobian_span b hb,?_⟩
  rintro r ⟨j,rfl⟩
  rw [←IsScalarTower.algebraMap_eq,RingHom.isStandardSmooth_algebraMap]
  exact JacobianLocalSmooth318.localization_jacobian (presentation b j)

theorem integrallyClosed (hb:Function.Injective b):IsIntegrallyClosed (Ring b):=by
  letI:=FourRootActualGenericField318.affine_domain b hb
  letI:=smooth b hb
  exact SmoothDomainNormal318.integrallyClosed ℂ (Ring b)
end FourRootAffineSmooth318
