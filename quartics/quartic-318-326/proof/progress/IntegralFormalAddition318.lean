module
public import GenericFormalAddition318
public section
namespace IntegralFormalAddition318
open MvPowerSeries
variable {R K : Type*} [CommRing R] [Field K] [CharZero K]
variable (φ : R →+* K)
abbrev S (R : Type*) := MvPowerSeries (Fin 2) R
@[expose] noncomputable def x : S R := X 0
@[expose] noncomputable def a : S R := X 1
@[expose] noncomputable def v (V : PowerSeries R) (g : S R) : S R := V.subst g
@[expose] noncomputable def q (D : R) : S R := 1+C D*x^2*a^2
@[expose] noncomputable def n (V : PowerSeries R) : S R := x*v V a+a*v V x
@[expose] noncomputable def f (D : R) (V : PowerSeries R) : S R :=
  n V*(q D).invOfUnit 1
@[simp] theorem x_zero : constantCoeff (x (R:=R))=0 := by simp [x]
@[simp] theorem a_zero : constantCoeff (a (R:=R))=0 := by simp [a]
@[simp] theorem q_zero (D : R) : constantCoeff (q D)=1 := by simp [q]
@[simp] theorem f_zero (D : R) (V : PowerSeries R) : constantCoeff (f D V)=0 := by simp [f,n]

@[simp] theorem map_x : (x (R:=R)).map φ=GenericFormalAddition318.x (K:=K) := by simp [x,GenericFormalAddition318.x]
@[simp] theorem map_a : (a (R:=R)).map φ=GenericFormalAddition318.a (K:=K) := by simp [a,GenericFormalAddition318.a]

theorem map_v (D : R) (V : PowerSeries R)
    (hV : V.map φ=GenericFormalDifferential318.branch (φ D)) (g : S R)
    (hg : constantCoeff g=0) :
    (v V g).map φ=GenericFormalAddition318.v (φ D) (g.map φ) := by
  rw [v,PowerSeries.map_subst (.of_constantCoeff_zero hg),hV]
  rfl

theorem map_q (D : R) : (q D).map φ=GenericFormalAddition318.q (φ D) := by
  simp only [q,map_add,map_one,map_mul,map_C,map_pow,map_x,map_a,GenericFormalAddition318.q]

theorem map_q_inverse (D : R) : ((q D).invOfUnit 1).map φ=(GenericFormalAddition318.q (φ D))⁻¹ := by
  apply (MvPowerSeries.eq_inv_iff_mul_eq_one (by simp :
    constantCoeff (GenericFormalAddition318.q (φ D))≠0)).mpr
  have h := congrArg (MvPowerSeries.map φ) (MvPowerSeries.invOfUnit_mul (q D) 1 (by simp))
  simpa only [map_mul,map_one,map_q] using h

theorem map_f (D : R) (V : PowerSeries R)
    (hV : V.map φ=GenericFormalDifferential318.branch (φ D)) :
    (f D V).map φ=GenericFormalAddition318.f (φ D) := by
  simp only [f,n,map_mul,map_add,map_x,map_a,map_v φ D V hV _ a_zero,
    map_v φ D V hV _ x_zero,map_q_inverse,GenericFormalAddition318.f,GenericFormalAddition318.n]

/-- Transfer the proved full formal identity to integral coefficient data.
Only coefficient-map bindings are required, never a group-law premise. -/
theorem formal_addition (hφ : Function.Injective φ) (D : R) (L V : PowerSeries R)
    (hL : L.map φ=GenericFormalDifferential318.integral (φ D))
    (hV : V.map φ=GenericFormalDifferential318.branch (φ D)) :
    L.subst (f D V)=L.subst (x (R:=R))+L.subst a := by
  have hi : Function.Injective (MvPowerSeries.map φ : S R → S K) := by
    intro F G he
    ext k
    apply hφ
    simpa only [coeff_map] using congrArg (coeff k) he
  apply hi
  rw [map_add,PowerSeries.map_subst (.of_constantCoeff_zero (f_zero D V)),
    PowerSeries.map_subst (.of_constantCoeff_zero x_zero),
    PowerSeries.map_subst (.of_constantCoeff_zero a_zero),hL,map_f φ D V hV,map_x,map_a]
  exact GenericFormalAddition318.formal_addition (φ D)

theorem formal_branch (hφ : Function.Injective φ) (D : R) (V : PowerSeries R)
    (hV : V.map φ=GenericFormalDifferential318.branch (φ D)) :
    V.subst (f D V)=
      (v V x*v V a*(1-C D*x^2*a^2)-2*C D*x*a*(x^2+a^2))*((q D).invOfUnit 1)^2 := by
  have hi : Function.Injective (MvPowerSeries.map φ : S R → S K) := by
    intro F G he
    ext k
    apply hφ
    simpa only [coeff_map] using congrArg (coeff k) he
  apply hi
  simp only [PowerSeries.map_subst (.of_constantCoeff_zero (f_zero D V)),hV,map_f φ D V hV,
    map_mul,map_sub,map_add,map_one,map_ofNat,map_pow,map_C,map_x,map_a,
    map_v φ D V hV _ x_zero,map_v φ D V hV _ a_zero,map_q_inverse]
  exact GenericFormalAddition318.f_branch (φ D)

end IntegralFormalAddition318
#print axioms IntegralFormalAddition318.formal_addition

#print axioms IntegralFormalAddition318.formal_branch
