module
public import PELOrderReductionThree318
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import LevelThreeKernel318
public section
noncomputable section
namespace PELReductionResidueField318
open PELOrderReductionThree318
set_option maxHeartbeats 1200000

/-- The actual unramified quadratic residue field has j²=−1=2 in F3. -/
abbrev Residue := QuadraticAlgebra F3 2 0
instance quadratic_no_root : Fact (∀ r:F3, r^2 ≠ 2+0*r) := ⟨by
  intro r
  fin_cases r <;> decide⟩

noncomputable instance residueFintype : Fintype Residue :=
  Fintype.ofEquiv (F3×F3) (QuadraticAlgebra.equivProd (2:F3) 0).symm
noncomputable instance reductionFintype : Fintype Reduction :=
  Fintype.ofEquiv (Fin 4→F3) (QuaternionAlgebra.equivTuple (0:F3) 0 2).symm

/-- Projection kills the actual nilpotent i,k directions and preserves j. -/
@[expose] def residue : Reduction →+* Residue where
  toFun x := ⟨x.re,x.imJ⟩
  map_zero' := by ext <;> rfl
  map_one' := by ext <;> rfl
  map_add' x y := by ext <;> rfl
  map_mul' x y := by ext <;> simp <;> ring

theorem residue_surjective : Function.Surjective residue := by
  intro x
  exact ⟨⟨x.re,0,x.im,0⟩,by ext <;> rfl⟩

theorem radical_coordinates (x : Reduction) : residue x=0 ↔ x.re=0 ∧ x.imJ=0 := by
  constructor
  · intro h
    exact ⟨congrArg QuadraticAlgebra.re h,congrArg QuadraticAlgebra.im h⟩
  · rintro ⟨hr,hj⟩
    ext <;> assumption

/-- The entire actual radical has square-zero multiplication, not only
nilpotence of each individual element. -/
theorem radical_mul_zero (x y : Reduction) (hx : residue x=0) (hy : residue y=0) :
    x*y=0 := by
  obtain ⟨hr,hj⟩ := (radical_coordinates x).mp hx
  obtain ⟨hr',hj'⟩ := (radical_coordinates y).mp hy
  ext <;> simp [hr,hj,hr',hj']

theorem radical_square_zero (x : Reduction) (hx : residue x=0) : x^2=0 := by
  simpa only [pow_two] using radical_mul_zero x x hx hx

theorem residue_card : Nat.card Residue=9 := by
  rw [Nat.card_congr (QuadraticAlgebra.equivProd (2:F3) 0)]
  norm_num [Nat.card_eq_fintype_card]

theorem reduction_card : Nat.card Reduction=81 :=
  LevelThreeKernel318.ring_card_from_coordinates (QuaternionAlgebra.addEquivTuple (0:F3) 0 2)

theorem two_ne_zero : (2:Reduction)≠0 := by
  intro h
  have hr := congrArg QuaternionAlgebra.re h
  norm_num at hr

/-- Counts derived from the constructed ring and residue map. These do not
assert that global norm-one order units surject onto all finite units. -/
theorem reduction_counts : Nat.card Reduction=81 ∧
    Nat.card residue.toAddMonoidHom.ker=9 ∧ Nat.card Reductionˣ=72 ∧
      Nat.card (Reductionˣ ⧸ LevelThreeKernel318.signs Reduction)=36 := by
  exact ⟨reduction_card,
    LevelThreeKernel318.kernel_card residue residue_surjective reduction_card residue_card,
    LevelThreeKernel318.units_card residue residue_surjective radical_square_zero
      reduction_card residue_card,
    LevelThreeKernel318.effective_kernel_card residue residue_surjective radical_square_zero
      reduction_card residue_card two_ne_zero⟩
end PELReductionResidueField318
