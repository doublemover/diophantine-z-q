module
public import ReciprocalGroup318
public section
namespace ShortCurveBaseChange318
open ReciprocalDouble318 WeierstrassCurve.Affine
variable {F K : Type*} [Field F] [Field K] [CharZero F] [CharZero K] [DecidableEq F] [DecidableEq K]
noncomputable section

@[expose] def transport {L : Type*} [Field L] [DecidableEq L]
    {W V : WeierstrassCurve.Affine L} (h : W=V) : W.Point ≃+ V.Point := by
  subst V
  exact AddEquiv.refl _

@[simp] theorem transport_some {L : Type*} [Field L] [DecidableEq L]
    {W V : WeierstrassCurve.Affine L} (h : W=V) {x y : L} (hn : W.Nonsingular x y) :
    transport h (Point.some x y hn)=Point.some x y (h ▸ hn) := by
  subst V
  rfl

theorem map_curve (φ : F →+* K) (D : F) : (E D).map φ=E (φ D) := by
  apply WeierstrassCurve.ext
  · exact φ.map_zero
  · exact φ.map_zero
  · exact φ.map_zero
  · exact φ.map_neg D
  · exact φ.map_zero

theorem nonsingular_map (φ : F →+* K) (D x y : F) (h : (E D).Nonsingular x y) :
    (E (φ D)).Nonsingular (φ x) (φ y) := by
  rw [←map_curve φ D]
  exact ((E D).map_nonsingular φ.injective x y).mpr h

@[expose] def pointMap (φ : F →+* K) (D : F) : (E D).Point →+ (E (φ D)).Point := by
  letI : Algebra F K := φ.toAlgebra
  exact (transport (map_curve φ D)).toAddMonoidHom.comp (Point.baseChange F K (W':=E D))

theorem pointMap_some (φ : F →+* K) (D x y : F) (h : (E D).Nonsingular x y) :
    pointMap φ D (Point.some x y h)=Point.some (φ x) (φ y) (nonsingular_map φ D x y h) := by
  letI : Algebra F K := φ.toAlgebra
  change transport (map_curve φ D) (Point.some (φ x) (φ y)
    (((E D).map_nonsingular φ.injective x y).mpr h)) = _
  rw [transport_some]

@[simp] theorem pointMap_zero (φ : F →+* K) (D : F) : pointMap φ D 0=0 := map_zero _
theorem pointMap_add (φ : F →+* K) (D : F) (P Q : (E D).Point) :
    pointMap φ D (P+Q)=pointMap φ D P+pointMap φ D Q := map_add _ _ _
theorem pointMap_zsmul (φ : F →+* K) (D : F) (n : ℤ) (P : (E D).Point) :
    pointMap φ D (n • P)=n • pointMap φ D P := map_zsmul _ _ _


theorem pointMap_injective (φ : F →+* K) (D : F) : Function.Injective (pointMap φ D) := by
  intro P Q he
  cases P with
  | zero =>
    cases Q with
    | zero => rfl
    | some x y h =>
      change pointMap φ D 0=pointMap φ D (Point.some x y h) at he
      rw [pointMap_zero,pointMap_some] at he
      exact (Point.some_ne_zero _ he.symm).elim
  | some x y h =>
    cases Q with
    | zero =>
      change pointMap φ D (Point.some x y h)=pointMap φ D 0 at he
      rw [pointMap_some,pointMap_zero] at he
      exact (Point.some_ne_zero _ he).elim
    | some x' y' h' =>
      rw [pointMap_some,pointMap_some] at he
      have hh:=Point.some.inj he
      have hx:=φ.injective hh.1
      have hy:=φ.injective hh.2
      subst x'; subst y'; rfl

theorem pointMap_reciprocal (φ : F →+* K) (D u v : F) (hv : v≠0) (hc : v^2=1-D*u^4) :
    pointMap φ D (point D u v hv hc)=point (φ D) (φ u) (φ v)
      (fun h => hv (φ.injective (h.trans φ.map_zero.symm)))
      (by simpa only [map_pow,map_sub,map_one,map_mul] using congrArg φ hc) := by
  by_cases hu : u=0
  · subst u
    simp only [map_zero,point_zero]
  · have hu' : φ u≠0 := fun h => hu (φ.injective (h.trans φ.map_zero.symm))
    simp only [point,dite_eq_right hu,dite_eq_right hu',pointMap_some]
    congr 1
    · rw [map_div₀,map_one,map_pow]
    · rw [map_div₀,map_pow]

@[expose] def z (D : F) : (E D).Point → F
  | .zero => 0
  | .some x y _ => -x/y
@[expose] def w (D : F) : (E D).Point → F
  | .zero => 0
  | .some x _ _ => D/x^2

theorem z_map (φ : F →+* K) (D : F) (P : (E D).Point) :
    z (φ D) (pointMap φ D P)=φ (z D P) := by
  cases P with
  | zero =>
    change z (φ D) (pointMap φ D 0)=φ 0
    rw [pointMap_zero,map_zero]
    rfl
  | some x y h =>
    rw [pointMap_some]
    change -φ x/φ y=φ (-x/y)
    rw [map_div₀,map_neg]

theorem w_map (φ : F →+* K) (D : F) (P : (E D).Point) :
    w (φ D) (pointMap φ D P)=φ (w D P) := by
  cases P with
  | zero =>
    change w (φ D) (pointMap φ D 0)=φ 0
    rw [pointMap_zero,map_zero]
    rfl
  | some x y h =>
    rw [pointMap_some]
    change φ D/(φ x)^2=φ (D/x^2)
    rw [map_div₀,map_pow]

end
end ShortCurveBaseChange318
#print axioms ShortCurveBaseChange318.pointMap
#print axioms ShortCurveBaseChange318.pointMap_some

#print axioms ShortCurveBaseChange318.pointMap_injective
#print axioms ShortCurveBaseChange318.pointMap_reciprocal
#print axioms ShortCurveBaseChange318.z_map
