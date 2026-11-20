module
public import CTCyclicTwoBar318
import all CTCyclicTwoBar318
public import CTRealClosureConjugation318
public import CTContinuousFieldHTwo318
public import Mathlib.Data.Fin.VecNotation
import all CTContinuousFieldHTwo318
import all Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Abel
public section
noncomputable section

namespace CTRealNativeBar318

open CTRealClosureConjugation318 CTFieldPrimitiveRestriction318 CTContinuousFieldHTwo318
open CategoryTheory groupCohomology

local instance : DecidableEq ℝ := Classical.decEq _

abbrev A := FieldUnitRep ℝ

/-- The literal representation action, merely forgetting ℤ-linearity. -/
def realBarAction : RealGal →* AddMonoid.End A where
  toFun g := ((FieldUnitRep ℝ).ρ g).toAddMonoidHom
  map_one' := by
    rw [map_one] <;> rfl
  map_mul' g h := by
    rw [map_mul] <;> rfl

def onPairs (z : (Fin 2 → RealGal) → A) (g h : RealGal) : A := z ![g,h]

private theorem pair_eta (s : Fin 2 → RealGal) : ![s 0,s 1]=s := by
  funext j
  fin_cases j <;> rfl

theorem native_d₂_apply (z : (Fin 2 → RealGal) → A) (s : Fin 3 → RealGal) :
    inhomogeneousCochains.d (FieldUnitRep ℝ) 2 z s =
      realBarAction (s 0) (onPairs z (s 1) (s 2)) -
      onPairs z (s 0*s 1) (s 2) + onPairs z (s 0) (s 1*s 2) -
      onPairs z (s 0) (s 1) := by
  change (FieldUnitRep ℝ).ρ (s 0) (z fun i => s i.succ) +
    (Finset.univ.sum fun i : Fin 3 =>
      (-1:ℤ)^((i:ℕ)+1) • z (Fin.contractNth i (· * ·) s)) = _
  have ct : (fun i : Fin 2 => s i.succ) = ![s 1,s 2] := by
    funext i
    fin_cases i <;> rfl
  have c₀ : Fin.contractNth (0:Fin 3) (· * ·) s = ![s 0*s 1,s 2] := by
    funext i
    fin_cases i <;> rfl
  have c₁ : Fin.contractNth (1:Fin 3) (· * ·) s = ![s 0,s 1*s 2] := by
    funext i
    fin_cases i <;> rfl
  have c₂ : Fin.contractNth (2:Fin 3) (· * ·) s = ![s 0,s 1] := by
    funext i
    fin_cases i <;> rfl
  rw [Fin.sum_univ_three,ct,c₀,c₁,c₂]
  change _ = (FieldUnitRep ℝ).ρ (s 0) (z ![s 1,s 2]) -
    z ![s 0*s 1,s 2] + z ![s 0,s 1*s 2] - z ![s 0,s 1]
  simp only [Fin.val_zero,Fin.val_one,Fin.val_two]
  norm_num <;> abel

theorem isCycle_pairs (z : continuousCycles ℝ) :
    CTCyclicTwoBar318.IsCycle realBarAction (onPairs z.val) := by
  intro g h k
  have hz := congrFun z.property.1 ![g,h,k]
  rw [native_d₂_apply] at hz
  exact hz

def ofPairs (z : RealGal → RealGal → A) (s : Fin 2 → RealGal) : A := z (s 0) (s 1)

theorem pairs_ofPairs (z : RealGal → RealGal → A) :
    onPairs (ofPairs z) = z := by
  funext g h
  rfl

theorem ofPairs_pairs (z : (Fin 2 → RealGal) → A) :
    ofPairs (onPairs z) = z := by
  funext s
  change z ![s 0,s 1] = z s
  rw [pair_eta]

theorem mkPairs_cycle (z : RealGal → RealGal → A)
    (hz : CTCyclicTwoBar318.IsCycle realBarAction z) :
    ∃ w : continuousCycles ℝ, w.val=ofPairs z := by
  letI : DiscreteTopology RealGal := realGal_discrete
  have hd : inhomogeneousCochains.d (FieldUnitRep ℝ) 2 (ofPairs z)=0 := by
    funext s
    rw [native_d₂_apply,pairs_ofPairs]
    exact hz (s 0) (s 1) (s 2)
  exact ⟨⟨ofPairs z,hd,IsLocallyConstant.of_discrete _⟩,rfl⟩

theorem class_zero_iff_bar (z : continuousCycles ℝ) :
    classOf ℝ z=0 ↔ ∃ b : RealGal → A,
      CTCyclicTwoBar318.coboundary realBarAction b=onPairs z.val := by
  rw [class_zero_iff]
  constructor
  · rintro ⟨b,hb⟩
    refine ⟨fun g => b.val (fun _ => g),?_⟩
    funext g h
    have hHere := congrFun hb ![g,h]
    rw [native_d₁_apply] at hHere
    exact hHere.symm
  · rintro ⟨b,hb⟩
    letI : DiscreteTopology RealGal := realGal_discrete
    let c (s : Fin 1 → RealGal) := b (s 0)
    refine ⟨⟨c,IsLocallyConstant.of_discrete c⟩,?_⟩
    funext s
    change z.val s = inhomogeneousCochains.d (FieldUnitRep ℝ) 1 c s
    rw [native_d₁_apply]
    have h := congrFun (congrFun hb (s 0)) (s 1)
    exact (congrArg z.val (pair_eta s)).symm.trans h.symm

theorem class_zero_iff_norm (z : continuousCycles ℝ) :
    classOf ℝ z=0 ↔ ∃ a : A, realBarAction realConjugation a+a =
      CTCyclicTwoBar318.normalizedValue realBarAction realConjugation (onPairs z.val) :=
  (class_zero_iff_bar z).trans
    (CTCyclicTwoBar318.exists_boundary_iff realBarAction realConjugation
      realConjugation_square realConjugation_ne_one realGal_cases _ (isCycle_pairs z))

end CTRealNativeBar318
