module
public import CompressedGlobal318
public section
namespace CompressedTranslation318
open ConcreteG8Domain (K pair)
open CircuitReplay Raw318FinalReplay CompressedOrientation318 RawLucasOrientation318
open CompressedPoint318 CompressedGlobal318 WeierstrassCurve.Affine
open scoped QuadraticAlgebra
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
noncomputable section

theorem m_ne : m≠0 := by
  intro h
  have hh := congrArg QuadraticAlgebra.re h
  norm_num [m,pair] at hh

theorem generator_nonsingular : E.Nonsingular (k^2) (k*m) := by
  rw [nonsingular_iff']
  constructor
  · rw [equation_iff]
    simp only [E,zero_mul,mul_zero,add_zero]
    linear_combination k^2*constant_equation
  · right
    simpa [E] using mul_ne_zero (show (2:K)≠0 by norm_num) (mul_ne_zero k_ne m_ne)

@[expose] def P : E.Point := .some (k^2) (k*m) generator_nonsingular
@[expose] def H (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) : E.Point :=
  .some (xH w) (yH w) (source_global_H S w source).2.2.1
@[expose] def V (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) : E.Point :=
  if hs : shift w=0 then 0 else
    .some (xV w) (yV w) (source_global_V S w source hs).2.1
@[expose] def ell (w : Assignment) : K :=
  (k^2+m*shift w+(D*fH w+k^2)*(shift w)^2)/(k*shift w)

theorem source_polynomial (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    1-k^2*fH w*(1+(shift w)^2)-2*m*fH w*shift w-D*(fH w)^2*(shift w)^2=0 := by
  obtain ⟨ht,hg⟩ := source_products S w source
  have he := (source_relations S w source).2
  rw [ht,hg] at he
  linear_combination he

theorem secant_identity (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (hs : shift w≠0) : ell w*(xH w-xV w)=yH w+yV w := by
  have hf := source_fH_ne S w source
  obtain ⟨ht,hg⟩ := source_products S w source
  dsimp [ell,xH,xV,yH,yV,anchorA,anchorB]
  rw [ht,hg]
  field_simp [hf,k_ne,hs]
  ring

theorem added_x (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (hs : shift w≠0) : (ell w)^2-xH w-xV w=k^2 := by
  have hf := source_fH_ne S w source
  have hF := source_polynomial S w source
  have hP := constant_equation
  dsimp [ell,xH,xV]
  field_simp [hf,k_ne,hs]
  linear_combination fH w*(shift w)^2*hP-
    (D*fH w*(shift w)^2+k^2*(shift w)^2+k^2)*hF

theorem added_y (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (hs : shift w≠0) : -yH w+ell w*(xH w-k^2)=k*m := by
  have hf := source_fH_ne S w source
  have hF := source_polynomial S w source
  obtain ⟨ht,hg⟩ := source_products S w source
  dsimp [ell,xH,yH,anchorA]
  rw [ht]
  field_simp [hf,k_ne,hs]
  linear_combination k^2*hF

theorem unequal_translation (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (hs : shift w≠0) (hx : xH w≠xV w) : H S w source-V S w source=P := by
  let hH := (source_global_H S w source).2.2.1
  let hV := (source_global_V S w source hs).2.1
  have hneg := (nonsingular_neg (xV w) (yV w)).mpr hV
  have hslope : E.slope (xH w) (xV w) (yH w) (E.negY (xV w) (yV w))=ell w := by
    rw [slope_of_X_ne hx]
    simp only [negY,E,zero_mul,sub_zero,sub_neg_eq_add]
    apply (div_eq_iff (sub_ne_zero.mpr hx)).mpr
    exact (secant_identity S w source hs).symm
  have hxx : E.addX (xH w) (xV w) (ell w)=k^2 := by
    simpa [addX,E] using added_x S w source hs
  have hyy : E.addY (xH w) (xV w) (yH w) (ell w)=k*m := by
    rw [addY,negAddY,negY,hxx]
    simp only [E,zero_mul,sub_zero]
    linear_combination added_y S w source hs
  rw [H,V,dite_eq_right hs,sub_eq_add_neg,Point.neg_some,Point.add_of_X_ne hx]
  simp only [hslope,hxx,hyy,P]

theorem equal_square_shift (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (hs : shift w≠0) (hx : xH w=xV w) : (shift w)^2=1 := by
  have hf := source_fH_ne S w source
  dsimp [xH,xV] at hx
  field_simp [hf,hs] at hx
  exact hx

theorem equal_negative_y (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (hs : shift w≠0) (he : (shift w)^2=1) : yV w= -yH w := by
  have hf := source_fH_ne S w source
  obtain ⟨ht,hg⟩ := source_products S w source
  dsimp [yV,yH,anchorB,anchorA]
  rw [ht,hg]
  field_simp [hf,k_ne,hs]
  linear_combination (k^2*((shift w)^2+1)+m*shift w+D*fH w*(shift w)^2)*he

theorem tangent_identity (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (hs : shift w≠0) (he : (shift w)^2=1) : ell w*(2*yH w)=3*(xH w)^2-D := by
  have hf := source_fH_ne S w source
  have hF := source_polynomial S w source
  have hP := constant_equation
  have ht := (source_products S w source).1
  dsimp [ell,xH,yH,anchorA]
  rw [ht]
  field_simp [hf,k_ne,hs]
  linear_combination 2*fH w*shift w*hP-
    (2*D*fH w*shift w+3*k^2*shift w)*hF-
    fH w*k^2*(D*fH w*shift w+k^2*shift w+2*m)*he

/-- The equal-abscissa branch uses actual doubling and its nonzero ordinate;
no secant denominator is inserted into the source. -/
theorem equal_translation (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (hs : shift w≠0) (hx : xH w=xV w) : H S w source-V S w source=P := by
  have he := equal_square_shift S w source hs hx
  have hyV := equal_negative_y S w source hs he
  have hyH := (source_global_H S w source).2.1
  have hy : yH w≠E.negY (xH w) (yH w) := by
    simp only [negY,E,zero_mul,sub_zero]
    intro hh
    exact (mul_ne_zero (show (2:K)≠0 by norm_num) hyH) (by linear_combination hh)
  have hV : V S w source= -H S w source := by
    simp only [V,dite_eq_right hs,H,Point.neg_some,hyV,←hx]
    simp only [negY,E,zero_mul,sub_zero]
  have hslope : E.slope (xH w) (xH w) (yH w) (yH w)=ell w := by
    rw [slope_of_Y_ne' hy]
    simp only [E,zero_mul,mul_zero,add_zero,sub_zero,sub_neg_eq_add]
    apply (div_eq_iff (show yH w+yH w≠0 by
      simpa [two_mul] using mul_ne_zero (show (2:K)≠0 by norm_num) hyH)).mpr
    simpa [two_mul,sub_eq_add_neg] using (tangent_identity S w source hs he).symm
  have hxx : E.addX (xH w) (xH w) (ell w)=k^2 := by
    simpa [addX,E,←hx] using added_x S w source hs
  have hyy : E.addY (xH w) (xH w) (yH w) (ell w)=k*m := by
    rw [addY,negAddY,negY,hxx]
    simp only [E,zero_mul,sub_zero]
    linear_combination added_y S w source hs
  rw [hV,sub_neg_eq_add,H,Point.add_self_of_Y_ne hy]
  simp only [hslope,hxx,hyy,P]

/-- The shift-zero boundary is exactly H=P,V=O. -/
theorem zero_translation (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (hs : shift w=0) : H S w source=P ∧ V S w source=0 := by
  have hf := source_fH_ne S w source
  have hF := source_polynomial S w source
  simp only [hs,zero_pow (by decide : 2≠0),add_zero,mul_zero,sub_zero] at hF
  have hf' : k^2*fH w=1 := by linear_combination -hF
  have hA : anchorA w=m := by
    rw [anchorA,(source_products S w source).1,hs]
    ring
  have hx : xH w=k^2 := by
    dsimp [xH]
    exact (div_eq_iff hf).mpr (by simpa [mul_comm] using hf'.symm)
  have hy : yH w=k*m := by
    dsimp [yH]
    rw [hA]
    apply (div_eq_iff (mul_ne_zero k_ne hf)).mpr
    linear_combination -m*hf'
  constructor
  · simp only [H,hx,hy,P]
  · simp [V,hs]

/-- Exact oriented actual-group translation from the raw compression, covering
shift zero and both tangent charts as well as the ordinary secant case. -/
theorem source_translation (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    H S w source-V S w source=P := by
  by_cases hs : shift w=0
  · obtain ⟨hH,hV⟩ := zero_translation S w source hs
    simp [hH,hV]
  · by_cases hx : xH w=xV w
    · exact equal_translation S w source hs hx
    · exact unequal_translation S w source hs hx

end
end CompressedTranslation318
