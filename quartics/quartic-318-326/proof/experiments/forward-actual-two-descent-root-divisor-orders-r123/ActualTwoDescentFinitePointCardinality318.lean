module
public import ActualTwoDescentFiniteEllipticDoubleQuotient318
public section
noncomputable section
namespace ActualTwoDescentFinitePointCardinality318
set_option maxHeartbeats 16000000

open ActualTwoDescentFiniteEllipticModel318
variable {K : Type*} [Field K] [NeZero (2 : K)] [NeZero (3 : K)] [DecidableEq K]

def pointCoordinates (n : K) : Point n → Option (K × K)
  | .zero => none
  | .some x y _ => some (x,y)

lemma actual_point_coordinates_injective (n : K) : Function.Injective (pointCoordinates n) := by
  intro P Q h
  cases P <;> cases Q <;> simp_all [pointCoordinates,WeierstrassCurve.Affine.Point.some.injEq]

lemma actual_finite_points [Finite K] (n : K) : Finite (Point n) :=
  Finite.of_injective (pointCoordinates n) (actual_point_coordinates_injective n)

def fourTorsion (n : K) (hn : n ≠ 0) : Fin 4 → Point n :=
  ![0,point n 0 0 hn (by ring),point n n 0 hn (by ring),point n (-3*n) 0 hn (by ring)]

lemma actual_four_torsion_double (n : K) (hn : n ≠ 0) (i : Fin 4) :
    fourTorsion n hn i+fourTorsion n hn i=0 := by
  fin_cases i
  · simp [fourTorsion]
  all_goals
    simp only [fourTorsion,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,point]
    apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
    rw [curve_negY]
    ring

lemma actual_four_torsion_injective (n : K) (hn : n ≠ 0) : Function.Injective (fourTorsion n hn) := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [fourTorsion,point,WeierstrassCurve.Affine.Point.some.injEq]
  all_goals exfalso
  all_goals first
    | apply hn; linear_combination h
    | apply mul_ne_zero good_three_ne hn; linear_combination h
    | apply mul_ne_zero good_four_ne hn; linear_combination h

lemma actual_two_torsion_exhaustion (n : K) (hn : n ≠ 0) (P : Point n) (hP : P+P=0) :
    ∃ i : Fin 4, P=fourTorsion n hn i := by
  cases P with
  | zero => exact ⟨0,rfl⟩
  | some x y h =>
    have hy : y=0 := by
      by_contra hy
      have hy' : y ≠ (curve n).toAffine.negY x y := by rw [curve_negY]; exact good_ne_neg hy
      rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy'] at hP
      exact WeierstrassCurve.Affine.Point.some_ne_zero _ hP
    have hc := (curve_equation n x y).mp h.left
    rw [hy,zero_pow (by decide : (2 : ℕ) ≠ 0)] at hc
    rcases mul_eq_zero.mp hc.symm with h01|h3
    · rcases mul_eq_zero.mp h01 with h0|h1
      · subst x; subst y; exact ⟨1,rfl⟩
      · have hx : x=n := sub_eq_zero.mp h1
        subst x; subst y; exact ⟨2,rfl⟩
    · have hx : x= -3*n := by linear_combination h3
      subst x; subst y; exact ⟨3,rfl⟩

/-- The actual doubling kernel has four elements in every characteristic other than2,3. -/
lemma actual_doubling_kernel_card (n : K) (hn : n ≠ 0) :
    Nat.card (nsmulAddMonoidHom (α:=Point n) 2).ker=4 := by
  let e : Fin 4 ≃ (nsmulAddMonoidHom (α:=Point n) 2).ker :=
    Equiv.ofBijective (fun i => ⟨fourTorsion n hn i,by
      simpa only [AddMonoidHom.mem_ker,nsmulAddMonoidHom_apply,two_nsmul] using actual_four_torsion_double n hn i⟩)
      ⟨fun i j h => actual_four_torsion_injective n hn (congrArg Subtype.val h),by
        rintro ⟨P,hP⟩
        have hh : P+P=0 := by simpa only [AddMonoidHom.mem_ker,nsmulAddMonoidHom_apply,two_nsmul] using hP
        obtain ⟨i,hi⟩ := actual_two_torsion_exhaustion n hn P hh
        exact ⟨i,Subtype.ext hi.symm⟩⟩
  rw [←Nat.card_congr e]
  exact Nat.card_fin 4

end ActualTwoDescentFinitePointCardinality318
