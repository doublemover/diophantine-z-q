module
public import ActualTZLiteralProbeSpecialization318
import all ActualTZLiteralProbeSpecialization318
import all ActualTZJointPolynomialForms318
public section
noncomputable section
namespace ActualTZLiteralPairSeparation318
open ActualTZLiteralTerminalLift318 ActualTZJointPolynomialForms318
open ActualTZFixedWrapMarkers318 ActualTZLiteralProbeSpecialization318
open ActualTZMomentCoefficientMarkers318
open scoped BigOperators

variable {m a b j W : ℕ} {S : Terminal m a b}

private theorem coord_diff {D : Type*} {u v : D→Bool} (h : u≠v) :
    ∃ i,u i≠v i := by
  classical
  by_contra hn
  apply h
  funext i
  by_contra hh
  exact hn ⟨i,hh⟩

theorem flip (u v : Site a b j) (H : Varies (siteP S u-siteP S v)) :
    Varies (siteP S v-siteP S u) := by
  obtain ⟨x,y,h⟩ := H
  refine ⟨x,y,?_⟩
  simp only [map_sub] at *
  intro e
  apply h
  linarith

/-- Case 1: marked/marked; the true selected k-bit coordinate
occurs in exactly one of the pair at the differing corner. -/
theorem marked_marked (G : GoodTerminal S W) (ω ω' : Bits a) (hw : ω≠ω') :
    Varies (siteP (j:=j) S (.marked ω)-siteP S (.marked ω')) := by
  obtain ⟨i,hi⟩ := coord_diff hw
  obtain ⟨l,hl⟩ := G.slopeNonzero i
  refine of_mixed S (.marked ω) (.marked ω')
    (fun x _=>basis l x) (fun _ y=>digitBasis (ω i) i y) (fun _ _ _=>0)
    (-(S.slopeCoeff i l)) (neg_ne_zero.mpr hl) ?_
  simp only [mixedProbe,eOffset,sum_digitBasis,slope_basis,if_pos rfl,
    if_neg (Ne.symm hi)] <;> ring

/-- Case 2, linear over marked: slope on the actual copied coarse
variable; the original own-axis face is untouched. -/
theorem linear_marked (G : GoodTerminal S W) (c : Fin j) (i : Fin a)
    (ω : Face a i) (ω' : Bits a) :
    Varies (siteP S (.linear c i ω)-siteP S (.marked ω')) := by
  obtain ⟨l,hl⟩ := G.slopeNonzero i
  refine of_mixed S (.linear c i ω) (.marked ω')
    (fun x _=>basis l x) (fun _ _ _ _=>0) (fun _ y=>basis c y)
    (S.slopeCoeff i l) hl ?_
  simp only [mixedProbe,eOffset,slope_basis,basis_self,mul_zero,
    Finset.sum_const_zero,neg_zero,add_zero,sub_zero] <;> ring

/-- Case 2, nonlinear over marked: exact quadratic coefficient in
the independent true coarse copy. -/
theorem nonlinear_marked (G : GoodTerminal S W) (c : Fin j) (i : Fin b)
    (ω ω' : Bits a) :
    Varies (siteP S (.nonlinear c i ω)-siteP S (.marked ω')) := by
  refine of_coarse_quadratic S (.nonlinear c i ω) (.marked ω') c (S.quadratic i)
    (G.quadNonzero i) ?_
  simp only [quadraticProbe,eOffset,basis_self,nonlinearSlope_zero,mul_zero,
    Finset.sum_const_zero,add_zero,sub_zero,neg_zero] <;> ring

/-- Case 3 for a linear cofactor on a different actual coarse copy. -/
theorem linear_different_copy (G : GoodTerminal S W) (c d : Fin j) (hc : c≠d)
    (i i' : Fin a) (ω : Face a i) (ω' : Face a i') :
    Varies (siteP S (.linear c i ω)-siteP S (.linear d i' ω')) := by
  obtain ⟨l,hl⟩ := G.slopeNonzero i
  refine of_mixed S (.linear c i ω) (.linear d i' ω')
    (fun x _=>basis l x) (fun _ _ _ _=>0) (fun _ y=>basis c y)
    (S.slopeCoeff i l) hl ?_
  simp only [mixedProbe,eOffset,slope_basis,basis_self,basis_other (Ne.symm hc),mul_zero,
    Finset.sum_const_zero,add_zero,sub_zero,zero_add] <;> ring

theorem nonlinear_different_copy (G : GoodTerminal S W) (c d : Fin j) (hc : c≠d)
    (i i' : Fin b) (ω ω' : Bits a) :
    Varies (siteP S (.nonlinear c i ω)-siteP S (.nonlinear d i' ω')) := by
  refine of_coarse_quadratic S (.nonlinear c i ω) (.nonlinear d i' ω') c (S.quadratic i)
    (G.quadNonzero i) ?_
  simp only [quadraticProbe,eOffset,basis_self,basis_other (Ne.symm hc),nonlinearSlope_zero,
    mul_zero,Finset.sum_const_zero,add_zero,sub_zero,zero_pow (by decide : (2:ℕ)≠0),zero_add] <;> ring

/-- Mixed linear/nonlinear is separated even if the coarse copy
is shared; same-copy and two-copy cases use the same exact probe. -/
theorem nonlinear_linear (G : GoodTerminal S W) (c d : Fin j) (i : Fin b) (i' : Fin a)
    (ω : Bits a) (ω' : Face a i') :
    Varies (siteP S (.nonlinear c i ω)-siteP S (.linear d i' ω')) := by
  refine of_coarse_quadratic S (.nonlinear c i ω) (.linear d i' ω') c (S.quadratic i)
    (G.quadNonzero i) ?_
  simp only [quadraticProbe,eOffset,basis_self,nonlinearSlope_zero,slope_zero,
    mul_zero,zero_mul,Finset.sum_const_zero,add_zero,sub_zero,zero_add] <;> ring

/-- Case 4, distinct linear nodes on a shared coarse copy. -/
theorem linear_same_copy_distinct (G : GoodTerminal S W) (c : Fin j)
    (i i' : Fin a) (hi : i≠i') (ω : Face a i) (ω' : Face a i') :
    Varies (siteP S (.linear c i ω)-siteP S (.linear c i' ω')) := by
  obtain ⟨l,hl⟩ := G.slopeDistinct i i' hi
  refine of_mixed S (.linear c i ω) (.linear c i' ω')
    (fun x _=>basis l x) (fun _ _ _ _=>0) (fun _ y=>basis c y)
    (S.slopeCoeff i l-S.slopeCoeff i' l) (sub_ne_zero.mpr hl) ?_
  simp only [mixedProbe,eOffset,slope_basis,basis_self,mul_zero,
    Finset.sum_const_zero,add_zero,sub_zero] <;> ring

/-- Case 5, same nonlinear node at different full corners: the
exact actual coarse/selected-k mixed probe yields 2Q. -/
theorem nonlinear_corner (G : GoodTerminal S W) (c : Fin j) (i : Fin b)
    (ω ω' : Bits a) (hw : ω≠ω') :
    Varies (siteP S (.nonlinear c i ω)-siteP S (.nonlinear c i ω')) := by
  obtain ⟨l,hl⟩ := coord_diff hw
  refine of_mixed S (.nonlinear c i ω) (.nonlinear c i ω')
    (fun _ _ _=>0) (fun _ y=>digitBasis (ω l) l y) (fun x _=>basis c x)
    (2*S.quadratic i) (mul_ne_zero (by norm_num) (G.quadNonzero i)) ?_
  have hs (u : Bits a) (y : ℤ) :
      (∑ t : Fin a,digitBasis (ω l) l y (u t) t)=if u l=ω l then y else 0 := by
    simpa only [one_mul] using sum_digitBasis u (ω l) l y (fun _=>1)
  simp only [mixedProbe,eOffset,hs,basis_self,nonlinearSlope_zero,slope_zero,zero_mul,
    Finset.sum_const_zero,if_pos rfl,if_neg (Ne.symm hl),add_zero,sub_zero] <;> ring

/-- Case 6, same active linear face at different *face* corners.
The pivot p is a subtype axis and cannot be the deleted own axis. -/
theorem linear_corner (G : GoodTerminal S W) (c : Fin j) (i : Fin a)
    (ω ω' : Face a i) (hw : ω≠ω') :
    Varies (siteP S (.linear c i ω)-siteP S (.linear c i ω')) := by
  obtain ⟨p,hp⟩ := coord_diff hw
  obtain ⟨l,hl⟩ := G.slopeDistinct i p.val (Ne.symm p.property)
  refine of_mixed S (.linear c i ω) (.linear c i ω')
    (fun x _=>basis l x) (fun _ y=>digitBasis (ω p) p.val y) (fun _ _ _=>0)
    (S.slopeCoeff i l-S.slopeCoeff p.val l) (sub_ne_zero.mpr hl) ?_
  simp only [mixedProbe,eOffset,sum_faceBasis,slope_basis,if_pos rfl,
    if_neg (Ne.symm hp),mul_zero,zero_add,add_zero] <;> ring

end ActualTZLiteralPairSeparation318
