module
public import ActualGaussianWeberGenericChartDomain318
public import ActualGaussianWeberGaussLocalization318
public import ActualGaussianWeberTranslationFunctionField318
public section
noncomputable section

namespace ActualGaussianWeberArcFunctionEmbedding318

open Polynomial
open ActualGaussianWeberQuadraticGenericChart318 ActualGaussianWeberGenericChartDomain318
open ActualGaussianWeberGaussLocalization318 ActualGaussianWeberTranslationChart318
open ActualGaussianWeberTranslationFunctionField318

variable {k R F : Type*} [Field k] [CommRing R] [IsDomain R] [Field F]

/-- An integral arc with a split constant field and genuinely
nonconstant affine abscissa is transcendental over that field.
The proof repeatedly removes the same linear residual-root factor:
each removal lowers the degree, with no perfection/char hypothesis. -/
theorem eval_integral_arc_injective (c : k→+*R) (reduce : R→+*k)
    (hConst : reduce.comp c=RingHom.id k) (x : R) (hx : x≠c (reduce x)) :
    Function.Injective (eval₂RingHom c x) := by
  have aux : ∀ (n : ℕ) (P : k[X]), P.natDegree=n → P.eval₂ c x=0 → P=0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro P hdeg hP
      by_contra hPn
      have hroot : P.IsRoot (reduce x) := by
        have e := congrArg reduce hP
        rw [hom_eval₂,hConst,map_zero,eval₂_id] at e
        exact e
      obtain ⟨Q,hq⟩ := (dvd_iff_isRoot.mpr hroot)
      have hQ : Q≠0 := fun h => hPn (by rw [hq,h,mul_zero])
      have hQd : Q.natDegree<n := by
        have e := congrArg natDegree hq
        rw [hdeg,natDegree_mul (X_sub_C_ne_zero _) hQ,natDegree_X_sub_C] at e
        omega
      have hQz : Q.eval₂ c x=0 := by
        rw [hq,eval₂_mul,eval₂_sub,eval₂_X,eval₂_C] at hP
        exact (mul_eq_zero.mp hP).resolve_left (sub_ne_zero.mpr hx)
      exact hQ (ih _ hQd Q rfl hQz)
  intro P Q h
  apply sub_eq_zero.mp
  apply aux (P-Q).natDegree _ rfl
  change (eval₂RingHom c x) (P-Q)=0
  rw [map_sub,h,sub_self]

@[expose] def chartEval (c : k→+*F) (x y : F) (he : y^2=x^3-x) : Chart k→+*F :=
  AdjoinRoot.lift (eval₂RingHom c x) y (by
    change (((X : (k[X])[X])^2 - C ((X : k[X])^3-X))).eval₂ (eval₂RingHom c x) y=0
    rw [eval₂_sub,eval₂_pow,eval₂_X,eval₂_C,map_sub,map_pow]
    rw [show (eval₂RingHom c x) X=x from eval₂_X _ _]
    exact sub_eq_zero.mpr he)

theorem chartEval_element (c : k→+*F) (x y : F) (he : y^2=x^3-x) (A B : k[X]) :
    chartEval c x y he (element A B)=A.eval₂ c x+B.eval₂ c x*y := by
  simp only [element,chartEval,map_add,map_mul,AdjoinRoot.lift_of,AdjoinRoot.lift_root,
    coe_eval₂RingHom]

theorem chartEval_injective (c : k→+*F) (x y : F) (he : y^2=x^3-x)
    (hx : Function.Injective (eval₂RingHom c x)) :
    Function.Injective (chartEval c x y he) := by
  let f := eval₂RingHom c x
  let φ : RatFunc k→+*F := IsFractionRing.lift hx
  have zero_test (z : Chart k) (hz : chartEval c x y he z=0) : z=0 := by
    obtain ⟨A,B,hAB⟩ := element_surjective z
    rw [←hAB,chartEval_element] at hz
    change f A+f B*y=0 at hz
    by_cases hb : B=0
    · have hA : A=0 := hx (by
        rw [hb,map_zero,zero_mul,add_zero] at hz
        exact hz.trans (map_zero f).symm)
      rw [←hAB,hA,hb]
      simp [element]
    · have hBV : f B≠0 := fun h => hb (hx (h.trans (map_zero f).symm))
      let r := RatFunc.mk (-A) B
      have hr : φ r=y := by
        change IsFractionRing.lift hx (RatFunc.mk (-A) B)=y
        rw [RatFunc.mk_eq_div,map_div₀,IsFractionRing.lift_algebraMap,IsFractionRing.lift_algebraMap]
        change f (-A)/f B=y
        apply (div_eq_iff hBV).2
        rw [map_neg]
        linear_combination -hz
      exfalso
      apply cubic_not_square k r
      apply φ.injective
      rw [map_pow,hr]
      change y^2=IsFractionRing.lift hx (algebraMap k[X] (RatFunc k) ((X:k[X])^3-X))
      rw [IsFractionRing.lift_algebraMap]
      simpa only [f,map_sub,map_pow,coe_eval₂RingHom,eval₂_X] using he
  intro A B h
  apply sub_eq_zero.mp
  exact zero_test _ (by rw [map_sub,h,sub_self])

/-- The actual original generic function field maps into the formal
arc field at the two prescribed nonconstant coordinates. -/
@[expose] def arcEmbedding (c : k→+*F) (x y : F) (he : y^2=x^3-x)
    (hx : Function.Injective (eval₂RingHom c x)) : FunctionField k→+*F :=
  IsFractionRing.lift (chartEval_injective c x y he hx)

theorem arcEmbedding_x (c : k→+*F) (x y : F) (he : y^2=x^3-x)
    (hx : Function.Injective (eval₂RingHom c x)) :
    arcEmbedding c x y he hx (xGeneric k)=x := by
  change IsFractionRing.lift (chartEval_injective c x y he hx)
    (algebraMap (Chart k) (FunctionField k) (xChart k))=x
  rw [IsFractionRing.lift_algebraMap]
  simp only [chartEval,xChart,AdjoinRoot.lift_of,coe_eval₂RingHom,eval₂_X]

theorem arcEmbedding_y (c : k→+*F) (x y : F) (he : y^2=x^3-x)
    (hx : Function.Injective (eval₂RingHom c x)) :
    arcEmbedding c x y he hx (yGeneric k)=y := by
  change IsFractionRing.lift (chartEval_injective c x y he hx)
    (algebraMap (Chart k) (FunctionField k) (yChart k))=y
  rw [IsFractionRing.lift_algebraMap]
  simp only [chartEval,yChart,AdjoinRoot.lift_root]

theorem arcEmbedding_polynomial (c : k→+*F) (x y : F) (he : y^2=x^3-x)
    (hx : Function.Injective (eval₂RingHom c x)) (P : k[X]) :
    arcEmbedding c x y he hx (fractionMap k (AdjoinRoot.of (relation k) P))=P.eval₂ c x := by
  change IsFractionRing.lift (chartEval_injective c x y he hx)
    (algebraMap (Chart k) (FunctionField k) (AdjoinRoot.of (relation k) P))=P.eval₂ c x
  rw [IsFractionRing.lift_algebraMap]
  simp only [chartEval,AdjoinRoot.lift_of,coe_eval₂RingHom]

theorem arcEmbedding_const (c : k→+*F) (x y : F) (he : y^2=x^3-x)
    (hx : Function.Injective (eval₂RingHom c x)) (v : k) :
    arcEmbedding c x y he hx (constGeneric k v)=c v := by
  change arcEmbedding c x y he hx (fractionMap k (AdjoinRoot.of (relation k) (C v)))=c v
  rw [arcEmbedding_polynomial,eval₂_C]

end ActualGaussianWeberArcFunctionEmbedding318
