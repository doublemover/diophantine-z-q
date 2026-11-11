module
public import TriangularTernaryBasis318
public section
noncomputable section
namespace TernaryChartModuli318
open scoped BigOperators
set_option maxHeartbeats 1000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def FiniteIndex {p : ι → ℕ} (t : ∀ i, Option (ZMod (p i))) := {i : ι // t i≠none}
@[expose] def InfinityIndex {p : ι → ℕ} (t : ∀ i, Option (ZMod (p i))) := {i : ι // ¬t i≠none}
@[expose] def finiteModulus (p : ι → ℕ) (t : ∀ i, Option (ZMod (p i))) : ℕ := by
  classical
  exact ∏ i : FiniteIndex t, p i.1
@[expose] def infinityModulus (p : ι → ℕ) (t : ∀ i, Option (ZMod (p i))) : ℕ := by
  classical
  exact ∏ i : InfinityIndex t, p i.1

theorem moduli_product (p : ι → ℕ) (t : ∀ i, Option (ZMod (p i))) :
    finiteModulus p t*infinityModulus p t=FixedSquarefreeCRT318.modulus p := by
  classical
  exact Fintype.prod_subtype_mul_prod_subtype (fun i => t i≠none) p

theorem moduli_positive (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (t : ∀ i, Option (ZMod (p i))) : 0<finiteModulus p t ∧ 0<infinityModulus p t := by
  classical
  constructor
  · exact FixedSquarefreeCRT318.modulus_positive (fun i : FiniteIndex t => p i.1) (fun i => hp i.1)
  · exact FixedSquarefreeCRT318.modulus_positive (fun i : InfinityIndex t => p i.1) (fun i => hp i.1)

/-- Actual least nonnegative simultaneous integer representatives. -/
theorem bounded_residue_lift (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hd : Function.Injective p) (f : ∀ i, ZMod (p i)) :
    ∃ a : ℤ, 0≤a ∧ a<(FixedSquarefreeCRT318.modulus p:ℤ) ∧
      ∀ i, (a : ZMod (p i))=f i := by
  letI : NeZero (FixedSquarefreeCRT318.modulus p) :=
    ⟨Nat.ne_of_gt (FixedSquarefreeCRT318.modulus_positive p hp)⟩
  let y := (FixedSquarefreeCRT318.ringEquiv p hp hd).symm f
  refine ⟨(y.val:ℤ),Int.natCast_nonneg _,?_,?_⟩
  · exact_mod_cast y.val_lt
  · intro i
    rw [Int.cast_natCast,←map_natCast (FixedSquarefreeCRT318.component p i) y.val,
      ZMod.natCast_zmod_val]
    exact congrFun ((FixedSquarefreeCRT318.ringEquiv p hp hd).apply_symm_apply f) i

/-- The actual finite-chart slope and quadratic coefficient are produced
simultaneously, with bounds suitable for a genuine integral basis. -/
theorem original_coefficients (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hd : Function.Injective p) (κ : ℤ) (t : ∀ i, Option (ZMod (p i))) :
    ∃ A B : ℤ, 0≤A ∧ A<(finiteModulus p t:ℤ) ∧ 0≤B ∧ B<(finiteModulus p t:ℤ) ∧
      ∀ i, t i≠none →
        (A : ZMod (p i))=(κ : ZMod (p i))*((t i).getD 0)^2*(2 : ZMod (p i))⁻¹ ∧
        (B : ZMod (p i))=(t i).getD 0 := by
  classical
  let pf (i : FiniteIndex t) := p i.1
  have hpf (i : FiniteIndex t) : (pf i).Prime := hp i.1
  have hdf : Function.Injective pf := hd.comp Subtype.val_injective
  obtain ⟨A,hA0,hA,hAr⟩ := bounded_residue_lift pf hpf hdf
    (fun i => (κ : ZMod (pf i))*((t i.1).getD 0)^2*(2 : ZMod (pf i))⁻¹)
  obtain ⟨B,hB0,hB,hBr⟩ := bounded_residue_lift pf hpf hdf (fun i => (t i.1).getD 0)
  refine ⟨A,B,hA0,hA,hB0,hB,?_⟩
  intro i hi
  exact ⟨hAr ⟨i,hi⟩,hBr ⟨i,hi⟩⟩

end TernaryChartModuli318
