module
public import ActualGaussianWeberHenselianPointMap318
public section
noncomputable section

namespace ActualGaussianWeberShortScale318

open WeierstrassCurve WeierstrassCurve.Affine
open ActualGaussianWeberHenselianPointMap318

variable {K : Type*} [Field K] [DecidableEq K]

@[expose] def short (c : K) : WeierstrassCurve K := ⟨0,0,0,-c,0⟩
abbrev src (u : K) := (short (u^4)).toAffine
abbrev tgt := (curve K).toAffine

private theorem source_eq (u x y : K) : (src u).Equation x y ↔ y^2=x^3-u^4*x := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [short,toAffine,sub_eq_add_neg]

private theorem source_nonsing (h2 : (2:K)≠0) {u x y : K} (hu : u≠0)
    (h : y^2=x^3-u^4*x) : (src u).Nonsingular x y := by
  have hD : (short (u^4)).Δ=(2:K)^6*(u^4)^3 := by
    norm_num [short,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,
      WeierstrassCurve.b₆,WeierstrassCurve.b₈] <;> ring
  have hn : (src u).Δ≠0 := by
    change (short (u^4)).Δ≠0
    rw [hD]
    exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ (pow_ne_zero _ hu))
  exact ((src u).equation_iff_nonsingular_of_Δ_ne_zero hn).mp ((source_eq u x y).mpr h)

theorem normalized_nonsing (h2 : (2:K)≠0) {u x y : K} (hu : u≠0)
    (h : (src u).Nonsingular x y) :
    (tgt (K:=K)).Nonsingular (x/u^2) (y/u^3) := by
  have he := (source_eq u x y).mp h.1
  apply nonsing_of_equation h2
  calc
    _ = y^2/u^6 := by rw [div_pow] <;> ring
    _ = _ := by rw [he]; field_simp [hu] <;> ring

@[expose] def normalize (h2 : (2:K)≠0) {u : K} (hu : u≠0) : (src u).Point→WP K
  | Point.zero => Point.zero
  | Point.some x y h => Point.some (x/u^2) (y/u^3) (normalized_nonsing h2 hu h)

theorem normalize_some (h2 : (2:K)≠0) {u x y : K} (hu : u≠0)
    (h : (src u).Nonsingular x y) :
    normalize h2 hu (Point.some x y h)=Point.some (x/u^2) (y/u^3) (normalized_nonsing h2 hu h) :=
  rfl

private theorem transport_some {W : WeierstrassCurve.Affine K} {x y x' y' : K}
    {h : W.Nonsingular x y} {h' : W.Nonsingular x' y'}
    (hx : x=x') (hy : y=y') : Point.some x y h=Point.some x' y' h' := by
  subst x'
  subst y'
  rfl

private theorem negY_src (u x y : K) : (src u).negY x y= -y := by simp [negY,short,toAffine]
private theorem negY_tgt (x y : K) : (tgt (K:=K)).negY x y= -y := by simp [negY,curve,toAffine]

private theorem divide_injective {d : K} (hd : d≠0) : Function.Injective (fun x : K => x/d) := by
  intro x y h
  apply (div_mul_cancel₀ x hd).symm.trans
  exact (congrArg (fun z : K => z*d) h).trans (div_mul_cancel₀ y hd)

private theorem ratio (u N D : K) (hu : u≠0) (n : ℕ) :
    (N/u^(n+1))/(D/u^n)=(N/D)/u := by
  by_cases hd : D=0
  · simp [hd]
  · rw [pow_succ]
    field_simp [hu,hd,pow_ne_zero n hu] <;> ring

private theorem tangent_numerator (u x : K) (hu : u≠0) :
    3*(x/u^2)^2-1=(3*x^2-u^4)/u^4 := by field_simp [hu] <;> ring

private theorem slope_scaled {u x y z w : K} (hu : u≠0)
    (h : ¬(x=z ∧ y=(src u).negY z w))
    (h' : ¬(x/u^2=z/u^2 ∧ y/u^3=(tgt (K:=K)).negY (z/u^2) (w/u^3))) :
    (tgt (K:=K)).slope (x/u^2) (z/u^2) (y/u^3) (w/u^3) =
      (src u).slope x z y w/u := by
  by_cases hx : x=z
  · have hx' : x/u^2=z/u^2 := congrArg (fun a : K => a/u^2) hx
    rw [slope_of_Y_ne hx' (fun e => h' ⟨hx',e⟩),slope_of_Y_ne hx (fun e => h ⟨hx,e⟩)]
    simp only [negY_src,negY_tgt,short,curve,toAffine,mul_zero,zero_mul,add_zero,sub_zero]
    rw [←sub_eq_add_neg (3*(x/u^2)^2) (1:K),
        ←sub_eq_add_neg (3*x^2) (u^4),tangent_numerator u x hu,
        show y/u^3 - -(y/u^3)=(y - -y)/u^3 by rw [sub_div,neg_div]]
    exact ratio u (3*x^2-u^4) (y - -y) hu 3
  · have hx' : x/u^2≠z/u^2 := fun e => hx (divide_injective (pow_ne_zero 2 hu) e)
    rw [slope_of_X_ne hx',slope_of_X_ne hx,←sub_div,←sub_div]
    exact ratio u (y-w) (x-z) hu 2

private theorem x_scaled (u x z s : K) (hu : u≠0) :
    (tgt (K:=K)).addX (x/u^2) (z/u^2) (s/u)=(src u).addX x z s/u^2 := by
  simp only [addX,curve,short,toAffine,mul_zero,zero_mul,add_zero,sub_zero]
  field_simp [hu] <;> ring

private theorem y_src (u x z y s : K) :
    (src u).addY x z y s= -(s*((src u).addX x z s-x)+y) := by
  rw [addY,negY_src,negAddY]

private theorem y_tgt (x z y s : K) :
    (tgt (K:=K)).addY x z y s= -(s*((tgt (K:=K)).addX x z s-x)+y) := by
  rw [addY,negY_tgt,negAddY]

private theorem y_scaled (u x z y s : K) (hu : u≠0) :
    (tgt (K:=K)).addY (x/u^2) (z/u^2) (y/u^3) (s/u)=(src u).addY x z y s/u^3 := by
  rw [y_tgt,y_src,x_scaled u x z s hu]
  field_simp [hu] <;> ring

/-- Actual stock point addition commutes with scaling weights 2,3.
Both tangent and secant slopes acquire the same factor 1/u. -/
theorem normalize_add (h2 : (2:K)≠0) {u : K} (hu : u≠0)
    (P Q : (src u).Point) : normalize h2 hu (P+Q)=normalize h2 hu P+normalize h2 hu Q := by
  cases P with
  | zero =>
    change normalize h2 hu (0+Q)=0+normalize h2 hu Q
    simp only [zero_add]
  | some x y hP =>
    cases Q with
    | zero =>
      change normalize h2 hu (Point.some x y hP+0)=normalize h2 hu (Point.some x y hP)+0
      simp only [add_zero]
    | some z w hQ =>
      have hOpp : (x=z ∧ y=(src u).negY z w) ↔
          (x/u^2=z/u^2 ∧ y/u^3=(tgt (K:=K)).negY (z/u^2) (w/u^3)) := by
        simp only [negY_src,negY_tgt,←neg_div]
        constructor
        · rintro ⟨rfl,rfl⟩
          exact ⟨rfl,rfl⟩
        · rintro ⟨hx,hy⟩
          exact ⟨divide_injective (pow_ne_zero 2 hu) hx,divide_injective (pow_ne_zero 3 hu) hy⟩
      by_cases h : x=z ∧ y=(src u).negY z w
      · have h' := hOpp.mp h
        rw [Point.add_of_Y_eq h.1 h.2,normalize_some,normalize_some,
          Point.add_of_Y_eq h'.1 h'.2] <;> rfl
      · have h' := fun h0 => h (hOpp.mpr h0)
        rw [Point.add_some h,normalize_some,normalize_some,normalize_some,Point.add_some h']
        have hs := slope_scaled hu h h'
        apply transport_some
        · rw [hs,x_scaled u x z _ hu]
        · rw [hs,y_scaled u x z y _ hu]

def normalizeHom (h2 : (2:K)≠0) {u : K} (hu : u≠0) : (src u).Point→+WP K where
  toFun := normalize h2 hu
  map_zero' := rfl
  map_add' := normalize_add h2 hu

private theorem normalize_injective (h2 : (2:K)≠0) {u : K} (hu : u≠0) :
    Function.Injective (normalize h2 hu) := by
  intro P Q h
  cases P with
  | zero =>
    cases Q with
    | zero => rfl
    | some x y hn =>
      rw [normalize_some] at h
      change Point.zero=Point.some _ _ _ at h
      cases h
  | some x y hn =>
    cases Q with
    | zero =>
      rw [normalize_some] at h
      change Point.some _ _ _=Point.zero at h
      cases h
    | some z w hz =>
      rw [normalize_some,normalize_some] at h
      let xval : WP K → K := fun P => match P with | .zero => 0 | .some a _ _ => a
      let yval : WP K → K := fun P => match P with | .zero => 0 | .some _ b _ => b
      have hx : x/u^2=z/u^2 := congrArg xval h
      have hy : y/u^3=w/u^3 := congrArg yval h
      exact transport_some (divide_injective (pow_ne_zero 2 hu) hx)
        (divide_injective (pow_ne_zero 3 hu) hy)

private theorem normalize_surjective (h2 : (2:K)≠0) {u : K} (hu : u≠0) :
    Function.Surjective (normalize h2 hu) := by
  intro P
  cases P with
  | zero => exact ⟨Point.zero,rfl⟩
  | some x y hn =>
    have he := (literal_equation x y).mp hn.1
    have hc : (y*u^3)^2=(x*u^2)^3-u^4*(x*u^2) := by
      linear_combination u^6*he
    refine ⟨Point.some (x*u^2) (y*u^3) (source_nonsing h2 hu hc),?_⟩
    rw [normalize_some]
    exact transport_some (mul_div_cancel_right₀ _ (pow_ne_zero 2 hu))
      (mul_div_cancel_right₀ _ (pow_ne_zero 3 hu))

/-- The normalized original curve is reached by an actual stock
additive equivalence, not just a comparison of cubic equations. -/
def normalizeEquiv (h2 : (2:K)≠0) {u : K} (hu : u≠0) : (src u).Point≃+WP K :=
  AddEquiv.ofBijective (normalizeHom h2 hu)
    ⟨normalize_injective h2 hu,normalize_surjective h2 hu⟩

theorem normalizeEquiv_apply (h2 : (2:K)≠0) {u : K} (hu : u≠0) (P : (src u).Point) :
    normalizeEquiv h2 hu P=normalize h2 hu P := by unfold normalizeEquiv normalizeHom; rfl

end ActualGaussianWeberShortScale318
