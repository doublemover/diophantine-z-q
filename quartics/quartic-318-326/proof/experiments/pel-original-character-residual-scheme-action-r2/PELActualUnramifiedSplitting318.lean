module
public import PELConicMatrixSplitting318
public section
noncomputable section
namespace PELActualUnramifiedSplitting318
set_option maxHeartbeats 1200000
variable (p : ℕ) [Fact p.Prime]
abbrev LocalAlgebra := QuaternionAlgebra ℚ_[p] (-210) 0 5

@[expose] def pointX (hp210 : ¬p ∣ 210) : ℚ_[p] :=
  Classical.choose (PELUnramifiedPadicConic318.field_conic p hp210)
@[expose] def pointY (hp210 : ¬p ∣ 210) : ℚ_[p] :=
  Classical.choose (Classical.choose_spec (PELUnramifiedPadicConic318.field_conic p hp210))
theorem point_equation (hp210 : ¬p ∣ 210) : (pointX p hp210)^2+210*(pointY p hp210)^2=5 :=
  Classical.choose_spec (Classical.choose_spec (PELUnramifiedPadicConic318.field_conic p hp210))

/-- An actual matrix-algebra equivalence for EVERY prime outside210. The
point is constructed over the actual p-adic field from its finite residue
field and Hensel; no local splitting assumption is taken. -/
@[expose] def splitting (hp210 : ¬p ∣ 210) :
    LocalAlgebra p ≃+* Matrix (Fin 2) (Fin 2) ℚ_[p] :=
  PELConicMatrixSplitting318.splitting (pointX p hp210) (pointY p hp210) (point_equation p hp210)

theorem splitting_scalar (hp210 : ¬p ∣ 210) (a : ℚ_[p]) :
    splitting p hp210 (algebraMap ℚ_[p] (LocalAlgebra p) a)=
      algebraMap ℚ_[p] (Matrix (Fin 2) (Fin 2) ℚ_[p]) a :=
  PELConicMatrixSplitting318.splitting_scalar _ _ _ a

@[expose] def rationalMap : PELQuaternionAlgebra318.B →+* LocalAlgebra p where
  toFun x := ⟨(x.re:ℚ_[p]),(x.imI:ℚ_[p]),(x.imJ:ℚ_[p]),(x.imK:ℚ_[p])⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' x y := by ext <;> simp
  map_mul' x y := by ext <;> simp <;> push_cast <;> norm_num <;> ring

/-- The matrix representation consumes the original rational quaternion,
with every signed coordinate and reduced norm unchanged. -/
@[expose] def originalRepresentation (hp210 : ¬p ∣ 210) :
    PELQuaternionAlgebra318.B →+* Matrix (Fin 2) (Fin 2) ℚ_[p] :=
  (splitting p hp210).toRingHom.comp (rationalMap p)

theorem original_norm (hp210 : ¬p ∣ 210) (q : PELQuaternionAlgebra318.B) :
    (originalRepresentation p hp210 q).det=(PELQuaternionAlgebra318.reducedNorm q:ℚ_[p]) := by
  change (PELConicMatrixSplitting318.matrix (pointX p hp210) (pointY p hp210)
    (rationalMap p q)).det=_
  rw [PELConicMatrixSplitting318.matrix_det _ _ (point_equation p hp210)]
  simp [rationalMap,PELQuaternionAlgebra318.reducedNorm] <;> push_cast <;> ring

theorem rationalMap_injective : Function.Injective (rationalMap p) := by
  intro x y h
  have hr := congrArg QuaternionAlgebra.re h
  have hi := congrArg QuaternionAlgebra.imI h
  have hj := congrArg QuaternionAlgebra.imJ h
  have hk := congrArg QuaternionAlgebra.imK h
  change (x.re:ℚ_[p])=(y.re:ℚ_[p]) at hr
  change (x.imI:ℚ_[p])=(y.imI:ℚ_[p]) at hi
  change (x.imJ:ℚ_[p])=(y.imJ:ℚ_[p]) at hj
  change (x.imK:ℚ_[p])=(y.imK:ℚ_[p]) at hk
  apply QuaternionAlgebra.ext
  · exact_mod_cast hr
  · exact_mod_cast hi
  · exact_mod_cast hj
  · exact_mod_cast hk

theorem originalRepresentation_injective (hp210 : ¬p ∣ 210) :
    Function.Injective (originalRepresentation p hp210) :=
  (splitting p hp210).injective.comp (rationalMap_injective p)

/-- A concrete zero-divisor pair distinguishes these actual local algebras
from the division presentations already constructed at2,3,5,7. -/
theorem zero_divisors (hp210 : ¬p ∣ 210) :
    ∃ a b : LocalAlgebra p, a≠0 ∧ b≠0 ∧ a*b=0 := by
  let e := splitting p hp210
  let A : Matrix (Fin 2) (Fin 2) ℚ_[p] := !![1,0;0,0]
  let B : Matrix (Fin 2) (Fin 2) ℚ_[p] := !![0,0;0,1]
  have hA : A≠0 := by
    intro h
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℚ_[p] => M 0 0) h
    norm_num [A] at this
  have hB : B≠0 := by
    intro h
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℚ_[p] => M 1 1) h
    norm_num [B] at this
  have hAB : A*B=0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [A,B,Matrix.mul_apply,Fin.sum_univ_two]
  refine ⟨e.symm A,e.symm B,?_,?_,?_⟩
  · exact fun h => hA (e.symm.injective (h.trans (map_zero e.symm).symm))
  · exact fun h => hB (e.symm.injective (h.trans (map_zero e.symm).symm))
  · rw [←map_mul,hAB,map_zero]
end PELActualUnramifiedSplitting318
