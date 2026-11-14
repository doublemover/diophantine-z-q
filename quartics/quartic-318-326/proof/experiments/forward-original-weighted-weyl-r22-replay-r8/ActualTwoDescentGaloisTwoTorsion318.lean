module
public import ActualTwoDescentGaloisFixedRational318
public section
noncomputable section
namespace ActualTwoDescentGaloisTwoTorsion318
set_option maxHeartbeats 16000000

open ActualTwoDescentEllipticModel318 ActualTwoDescentAlgebraicClosureHalving318
open ActualTwoDescentGaloisPointAction318
local instance : DecidableEq Qbar := Classical.decEq _

abbrev closedTwoTorsion (n : ℚ) := (nsmulAddMonoidHom (α:=Point (algebraMap ℚ Qbar n)) 2).ker

lemma actual_two_torsion_fixed (σ : GalQ) (n : ℚ) (hn : n ≠ 0)
    (P : Point (algebraMap ℚ Qbar n)) (hP : P+P=0) : galoisPointHom σ n hn P=P := by
  obtain ⟨i,rfl⟩ := ActualTwoDescentFinitePointCardinality318.actual_two_torsion_exhaustion
    (algebraMap ℚ Qbar n) (rational_parameter_ne n hn) P hP
  fin_cases i
  · rfl
  all_goals
    simp only [ActualTwoDescentFinitePointCardinality318.fourTorsion,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
      ActualTwoDescentFiniteEllipticModel318.point,galoisPointHom,AddMonoidHom.coe_mk,ZeroHom.coe_mk,
      galoisPoint,point,map_zero,map_mul,map_neg,map_ofNat,σ.commutes]

lemma actual_closed_two_torsion_card (n : ℚ) (hn : n ≠ 0) : Nat.card (closedTwoTorsion n)=4 :=
  ActualTwoDescentFinitePointCardinality318.actual_doubling_kernel_card _ (rational_parameter_ne n hn)

lemma actual_two_torsion_fixed_subtype (σ : GalQ) (n : ℚ) (hn : n ≠ 0) (P : closedTwoTorsion n) :
    galoisPointHom σ n hn P=P := by
  apply actual_two_torsion_fixed σ n hn P
  simpa only [AddMonoidHom.mem_ker,nsmulAddMonoidHom_apply,two_nsmul] using P.property

end ActualTwoDescentGaloisTwoTorsion318
