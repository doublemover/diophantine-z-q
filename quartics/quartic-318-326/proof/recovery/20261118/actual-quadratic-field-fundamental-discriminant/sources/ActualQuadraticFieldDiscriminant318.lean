module
public import IntegralQuadraticDiscriminant318
public section
noncomputable section
namespace ActualQuadraticFieldDiscriminant318
open NumberField Module

/-- Coordinates of the unit in a free rank-two algebra form a unimodular
column: the first coordinate of `1*B₀=B₀` gives the two Bézout coefficients
directly. This does not assume that an integral basis starts with one. -/
theorem exists_basis_one {A : Type*} [CommRing A]
    (B : Basis (Fin 2) ℤ A) : ∃ C : Basis (Fin 2) ℤ A, C 0=1 := by
  classical
  let a := B.repr 1 0
  let b := B.repr 1 1
  let c := B.coord 0 (B 0 * B 0)
  let d := B.coord 0 (B 1 * B 0)
  have hu : a • B 0+b • B 1=1 := by
    simpa only [Fin.sum_univ_two,a,b] using B.sum_repr (1:A)
  have h : c*a+d*b=1 := by
    have h' := congrArg (fun z : A => B.coord 0 (z*B 0)) hu
    simpa [add_mul,smul_mul_assoc,map_smul,smul_eq_mul,c,d,mul_comm] using h'
  let T : (Fin 2 → ℤ) ≃ₗ[ℤ] (Fin 2 → ℤ) :=
    { toFun := fun x => ![c*x 0+d*x 1, -b*x 0+a*x 1]
      invFun := fun z => ![a*z 0-d*z 1, b*z 0+c*z 1]
      left_inv := by intro x; funext i; fin_cases i <;> dsimp <;>
                       first | linear_combination x 0 * h | linear_combination x 1 * h
      right_inv := by intro x; funext i; fin_cases i <;> dsimp <;>
                        first | linear_combination x 0 * h | linear_combination x 1 * h
      map_add' := by intro x y; funext i; fin_cases i <;> dsimp <;> ring
      map_smul' := by intro k x; funext i; fin_cases i <;> dsimp <;> ring }
  let E := B.equivFun.trans T
  refine ⟨Basis.ofEquivFun E,?_⟩
  rw [Basis.coe_ofEquivFun]
  apply E.symm_apply_eq.mpr
  funext i
  fin_cases i
  · simpa [E,T,Basis.equivFun_apply,Pi.single_apply,a,b] using h.symm
  · simp [E,T,Basis.equivFun_apply,Pi.single_apply,a,b] <;> ring

/-- In a genuine integral basis (1,θ), the Gram determinant of the trace
pairing is the discriminant of the actual quadratic relation of θ. -/
theorem fundamental_of_one_basis (K : Type*) [Field K] [NumberField K]
    (B : Basis (Fin 2) ℤ (RingOfIntegers K)) (h1 : B 0=1) :
    Int.IsFundamentalDiscr (NumberField.discr K) := by
  classical
  let θ := B 1
  let a := B.repr (θ*θ) 0
  let t := B.repr (θ*θ) 1
  have hs : a • (1:RingOfIntegers K)+t • θ=θ*θ := by
    simpa only [Fin.sum_univ_two,h1,a,t,θ] using B.sum_repr (θ*θ)
  have hr : (θ:K)^2-(t:K)*(θ:K)+((-a:ℤ):K)=0 := by
    have eq := congrArg (fun z : RingOfIntegers K => (z:K)) hs
    simp [zsmul_eq_mul] at eq
    push_cast
    linear_combination -eq
  have htr1 : Algebra.trace ℤ (RingOfIntegers K) 1 = 2 := by
    rw [Algebra.trace_eq_matrix_trace B]
    simp [Matrix.trace,Matrix.diag,Fin.sum_univ_two]
  have htr : Algebra.trace ℤ (RingOfIntegers K) θ = t := by
    rw [Algebra.trace_eq_matrix_trace B]
    simp [Matrix.trace,Matrix.diag,Fin.sum_univ_two,Algebra.leftMulMatrix_eq_repr_mul,
          h1,θ,t,Basis.repr_self_apply]
  have htrsq : Algebra.trace ℤ (RingOfIntegers K) (θ*θ)=2*a+t^2 := by
    rw [←hs,map_add,map_smul,map_smul,htr1,htr]
    simp [smul_eq_mul] <;> ring
  have hd : NumberField.discr K=t^2-4*(-a) := by
    rw [←NumberField.discr_eq_discr K B,Algebra.discr_def,Matrix.det_fin_two]
    simp only [Algebra.traceMatrix_apply,Algebra.traceForm_apply,h1,one_mul,mul_one,
      ← show θ=B 1 from rfl,htr1,htr,htrsq]
    ring
  rw [hd]
  exact IntegralQuadraticDiscriminant318.fundamental_of_basis K B h1 t (-a) hr

/-- Every genuine quadratic number field has fundamental signed discriminant.
No quadratic-radicand classification, preselected integral generator, or
fundamentality certificate appears among the inputs. -/
theorem fundamental (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K=2) : Int.IsFundamentalDiscr (NumberField.discr K) := by
  classical
  let B := RingOfIntegers.basis K
  let e : Module.Free.ChooseBasisIndex ℤ (RingOfIntegers K) ≃ Fin 2 :=
    Fintype.equivFinOfCardEq (by
      rw [←Module.finrank_eq_card_basis B, RingOfIntegers.rank, hK])
  obtain ⟨C,hC⟩ := exists_basis_one (B.reindex e)
  exact fundamental_of_one_basis K C hC
end ActualQuadraticFieldDiscriminant318
