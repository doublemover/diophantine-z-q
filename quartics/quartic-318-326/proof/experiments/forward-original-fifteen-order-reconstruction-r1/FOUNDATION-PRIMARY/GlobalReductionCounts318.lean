module
public import GlobalGeneratorPoints318
public section
namespace GlobalReductionCounts318
open ConcreteG8Domain LocalGenerator318 GlobalGeneratorPoints318 WeierstrassCurve.Affine
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- The two good-reduction models of the actual normalized curve, at
sqrt(2)=6 modulo17 and sqrt(2)=5 modulo23. -/
@[expose] def E17 : WeierstrassCurve.Affine (ZMod 17) := ⟨0,0,0,-9,0⟩
@[expose] def E23 : WeierstrassCurve.Affine (ZMod 23) := ⟨0,0,0,-4,0⟩

instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 23) := ⟨by norm_num⟩

theorem residue_constants17 : (6:ZMod 17)^2=2 ∧ (3-6:ZMod 17)^2=9 := by norm_num <;> decide
theorem residue_constants23 : (5:ZMod 23)^2=2 ∧ (3-5:ZMod 23)^2=4 := by norm_num <;> decide

theorem discriminant17 : E17.Δ≠0 := by
  norm_num [E17,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,
    WeierstrassCurve.b₆,WeierstrassCurve.b₈] <;> decide
theorem discriminant23 : E23.Δ≠0 := by
  norm_num [E23,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,
    WeierstrassCurve.b₆,WeierstrassCurve.b₈] <;> decide

instance : E17.IsElliptic := ⟨isUnit_iff_ne_zero.mpr discriminant17⟩
instance : E23.IsElliptic := ⟨isUnit_iff_ne_zero.mpr discriminant23⟩

instance : DecidablePred (fun xy:ZMod 17×ZMod 17 => E17.Equation xy.1 xy.2) := by
  intro xy
  exact decidable_of_iff' (xy.2^2=xy.1^3-9*xy.1) (by
    change E17.Equation xy.1 xy.2 ↔ _
    rw [equation_iff]; simp [E17,sub_eq_add_neg])
instance : DecidablePred (fun xy:ZMod 23×ZMod 23 => E23.Equation xy.1 xy.2) := by
  intro xy
  exact decidable_of_iff' (xy.2^2=xy.1^3-4*xy.1) (by
    change E23.Equation xy.1 xy.2 ↔ _
    rw [equation_iff]; simp [E23,sub_eq_add_neg])

theorem affine_count17 : Fintype.card {xy:ZMod 17×ZMod 17 // E17.Equation xy.1 xy.2}=19 := by decide +kernel
theorem affine_count23 : Fintype.card {xy:ZMod 23×ZMod 23 // E23.Equation xy.1 xy.2}=23 := by decide +kernel

/-- Cardinalities include the identity, and are cardinalities of Mathlib's
actual nonsingular-point groups, not a detached affine point-list count. -/
theorem point_count17 : Nat.card E17.Point=20 := by
  rw [Nat.card_congr E17.pointEquiv]
  change Nat.card (Option {xy:ZMod 17×ZMod 17 // E17.Equation xy.1 xy.2})=20
  rw [Nat.card_eq_fintype_card,Fintype.card_option,affine_count17]
theorem point_count23 : Nat.card E23.Point=24 := by
  rw [Nat.card_congr E23.pointEquiv]
  change Nat.card (Option {xy:ZMod 23×ZMod 23 // E23.Equation xy.1 xy.2})=24
  rw [Nat.card_eq_fintype_card,Fintype.card_option,affine_count23]

theorem R_infinite_order (n:ℤ) (hn:n≠0) : n • R≠0 := by
  intro hz
  apply GeneratorMultiplesTwo318.generator_infinite_order n hn
  rw [←double_R,zsmul_add,hz,zero_add]

end GlobalReductionCounts318
