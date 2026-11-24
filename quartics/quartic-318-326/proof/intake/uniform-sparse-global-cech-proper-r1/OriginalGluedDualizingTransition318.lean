module
public import OriginalActualQuadraticLaurent318
public import OriginalMarkedGlobalCech318
public section
noncomputable section
namespace OriginalGluedDualizingTransition318
open Polynomial OriginalSparseQuadraticCharts318 OriginalActualQuadraticLaurent318
open OriginalQuadraticDualizing318 OriginalGlobalP1Residue318 OriginalGlobalCechOverlap318
open OriginalUniversalSparsePolynomial318 OriginalUniformSparseSmoothChart318
variable {E:Type*} [Field E]

theorem ordinary_eq (s t:E) : F s t=sextic s t := by
  simp only [F,ordinary,eqVal,sextic,cvec,pol,map_mul,map_pow,map_sub,map_neg,map_ofNat,map_zero]
  ring
theorem reciprocal_eq (s t:E) : G s t = reflect 6 (F s t) := by
  apply Polynomial.toLaurent_injective
  rw [←aeval_xl,←aeval_xl]
  let u: (L E)ˣ := uL
  have h : (↑((u⁻¹)⁻¹):L E)=(Xl:L E) := by rw [inv_inv]; rfl
  rw [←h,rev_at_unit (F s t) 6 (by rw [ordinary_eq]; exact pol_bound _ _ (by simp [cvec]))]
  rw [aeval_ordinary,aeval_reciprocal]
  exact (OriginalUniformSparseReciprocalChart318.reverse_laurent _ _ _ _ (u⁻¹).mul_inv).symm

theorem up_xi (f:E[X]) : up f (xi f) = inc f (LaurentPolynomial.T (-1)) := by
  have hh:=congrArg (up f) (xx_xi f)
  rw [map_mul,map_one,up_x] at hh
  calc
    _ = (↑(U f)⁻¹:D f)*((↑(U f):D f)*up f (xi f)) := by rw [←mul_assoc,Units.inv_mul,one_mul]
    _ = _ := by rw [hh,mul_one]; change (↑((Units.map (inc f).toMonoidHom uL)⁻¹):D f)=_; rw [←map_inv]; rfl

@[expose] def move (s t:E) : D (G s t)→ₐ[E]D (F s t) :=
  (up (F s t)).comp ((infToFin s t).comp (down (G s t)))
theorem base_move (s t:E) (h:L E) :
    move s t (inc (G s t) h) = inc (F s t) (LaurentPolynomial.invert h) := by
  have he : (move s t).comp (inc (G s t)) =
      (inc (F s t)).comp LaurentPolynomial.invert.toAlgHom := by
    let inst : IsScalarTower E E[X] (L E) := IsScalarTower.of_algebraMap_eq (fun a => by
      rw [LaurentPolynomial.algebraMap_eq_toLaurent,algebraMap_eq,toLaurent_C,LaurentPolynomial.algebraMap_apply,Algebra.algebraMap_self_apply])
    apply IsLocalization.algHom_ext (Submonoid.powers (X:E[X]))
    apply Polynomial.algHom_ext
    change up _ (infToFin s t (down _ (inc _ (toLaurent X))))=
        inc _ (LaurentPolynomial.invert (toLaurent X))
    rw [toLaurent_X,down_base,leval_T,infToFin_xx,up_xi,LaurentPolynomial.invert_T]
  exact AlgHom.congr_fun he h

theorem y_move (s t:E) : move s t (Y (G s t))=
    Y (F s t)*inc (F s t) (LaurentPolynomial.T (-3)) := by
  change up _ (infToFin s t (down _ (Y (G s t))))=_
  rw [down_y,infToFin_yy,map_mul,map_pow,up_y,up_xi,←map_pow,LaurentPolynomial.T_pow]
  norm_num

/-- The actual overlap transitions send w to y/x³. Thus the monogenic
codifferent functionals satisfy λ_y(move a)=x⁻³ move(λ_w(a)), before
multiplication by the relative base differential dv=-x⁻²dx. -/
theorem lambda_move (s t:E) (a:D (G s t)) :
    lambda (toLaurent (F s t)) (move s t a) =
      LaurentPolynomial.T (-3)*LaurentPolynomial.invert (lambda (toLaurent (G s t)) a) := by
  let f:=F s t
  let g:=G s t
  let α: L E := (basis (toLaurent g)).repr a 0
  let β: L E := lambda (toLaurent g) a
  have e : inc g α+inc g β*Y g=a := by
    change algebraMap _ _ ((basis (toLaurent g)).repr a 0)+
      algebraMap _ _ (lambda (toLaurent g) a)*OriginalQuadraticDualizing318.y (toLaurent g)=a
    simpa only [Algebra.smul_def,mul_one] using decompose (toLaurent g) a
  change lambda (toLaurent f) (move s t a)=LaurentPolynomial.T (-3)*LaurentPolynomial.invert β
  conv_lhs => arg 2; rw [←e]
  rw [map_add,map_mul,base_move,base_move,y_move]
  change lambda (toLaurent f) (inc f (LaurentPolynomial.invert α)+
    inc f (LaurentPolynomial.invert β)*(Y f*inc f (LaurentPolynomial.T (-3))))=_
  have hh : inc f (LaurentPolynomial.invert β)*(Y f*inc f (LaurentPolynomial.T (-3)))=
      (LaurentPolynomial.T (-3)*LaurentPolynomial.invert β) • Y f := by
    rw [Algebra.smul_def]
    change _=inc f (_*_)*Y f
    rw [map_mul]; ring
  rw [hh,map_add,map_smul,lambda_y]
  change lambda (toLaurent f) (algebraMap _ _ _)+_ =_
  rw [lambda_base,zero_add,smul_eq_mul,mul_one]

end OriginalGluedDualizingTransition318
#print axioms OriginalGluedDualizingTransition318.reciprocal_eq
#print axioms OriginalGluedDualizingTransition318.lambda_move
