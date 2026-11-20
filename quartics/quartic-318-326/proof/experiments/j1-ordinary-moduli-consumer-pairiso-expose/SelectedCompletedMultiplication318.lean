module
public import SelectedCompletedAdditiveScaling318
public import SelectedLiteralTorsionKernel318
import all LiteralSchemePointGroup318
public section
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open WeierstrassGluing318

namespace SelectedCompletedMultiplication318
variable {R : Type u} [CommRing R] (A B : R)

abbrev OverEnd :=
  {f : scheme A B ⟶ scheme A B // f ≫ structureMap A B = structureMap A B}

/-- Actual relative pair of a morphism with the identity of the SAME
completed Scheme. -/
@[expose] def stepPair (f : OverEnd A B) :
    scheme A B ⟶ pullback (structureMap A B) (structureMap A B) :=
  pullback.lift f.val (𝟙 _) (by rw [f.property,Category.id_comp])

@[reassoc] theorem stepPair_fst (f : OverEnd A B) :
    stepPair A B f ≫ pullback.fst _ _ = f.val := by simp [stepPair]
@[reassoc] theorem stepPair_snd (f : OverEnd A B) :
    stepPair A B f ≫ pullback.snd _ _ = 𝟙 _ := by simp [stepPair]

variable (hD : IsUnit (-16*(4*A^3+27*B^2)))

/-- Recurrence by the actual completed addition. Its construction does not
need to postulate a second group law over a general test ring. -/
@[expose] def iterate : ℕ → OverEnd A B
  | 0 => ⟨structureMap A B ≫ infinity A B,by
      simp only [Category.assoc,infinity_section,Category.comp_id]⟩
  | k+1 => ⟨stepPair A B (iterate k) ≫ CompletedAddition318.addition A B hD,by
      rw [Category.assoc,CompletedAddition318.addition_over_base,stepPair_fst_assoc,
        (iterate k).property]⟩

abbrev mul (m : ℕ) : scheme A B ⟶ scheme A B := (iterate A B hD m).val

@[simp] theorem mul_zero : mul A B hD 0 = structureMap A B ≫ infinity A B := rfl

theorem mul_succ (m : ℕ) :
    mul A B hD (m+1) =
      stepPair A B (iterate A B hD m) ≫ CompletedAddition318.addition A B hD := rfl

@[reassoc] theorem mul_base (m : ℕ) : mul A B hD m ≫ structureMap A B = structureMap A B :=
  (iterate A B hD m).property

section Literal
open LiteralSchemePointOperations318 SelectedLiteralTorsionKernel318
variable (n : ℕ)
local notation "a" => OpenJAffineScheme318.A n
local notation "b" => OpenJAffineScheme318.B n
local notation "H" => OpenJAffineScheme318.discriminant_unit n
local notation "e" => identityPoint n

/-- The recurrence is EXACTLY the original literal [m] used in the
kernel: compare on the genuine identity of the completed Scheme,
using the existing group operation at that test object. -/
theorem literal_mul (m : ℕ) : mul a b H m = mulMap n m := by
  induction m with
  | zero =>
      change structureMap a b ≫ infinity a b = ((0 : ℕ) • e).val
      rw [zero_nsmul] <;> rfl
  | succ k ih =>
      have hn : (k+1) • e = k • e + e := by
        simpa only [Nat.succ_eq_add_one,add_comm] using (succ_nsmul k e)
      rw [mul_succ]
      change stepPair a b (iterate a b H k) ≫ CompletedAddition318.addition a b H =
        ((k+1) • e).val
      rw [hn]
      change stepPair a b (iterate a b H k) ≫ CompletedAddition318.addition a b H =
        pair n (projection n) (k • e) e ≫ CompletedAddition318.addition a b H
      congr 1
      apply pullback.hom_ext
      · rw [stepPair_fst,pair_fst] <;> exact ih
      · rw [stepPair_snd,pair_snd] <;> rfl

/-- At any genuine Scheme test, the same multiplication predicts exactly
the original nsmul of that point, not a point selected anew. -/
theorem literal_eval (m : ℕ) {T : Scheme} (j : T ⟶ Base n) (P : Points n j) :
    P.val ≫ mul a b H m = (m • P).val := by
  rw [literal_mul]
  exact (mul_value n m j P).symm
end Literal

section Scale
open SelectedPointedShortScaling318 SelectedCompletedAdditiveScaling318
variable (C D : R) (r : Rˣ) (hA : A = (r:R)^4*C) (hB : B = (r:R)^6*D)
variable (g : IsUnit (-16*(4*C^3+27*D^2)))
local notation "γ" => gluedMap A B C D r hA hB
local notation "P" => pairMap A B C D r hA hB
local notation "g₁" => target_smooth_disc A B C D r hA hB g

/-- Naturality of genuine multiplication, for the chosen scale r over
the entire ring. No reduction to geometric field points. -/
theorem conjugate (m : ℕ) : γ ≫ mul A B g₁ m = mul C D g m ≫ γ := by
  induction m with
  | zero =>
      simp only [mul_zero,Category.assoc,zero_preserved]
      rw [←Category.assoc,glued_base]
  | succ k ih =>
      rw [mul_succ,mul_succ]
      have he : γ ≫ stepPair A B (iterate A B g₁ k) =
          stepPair C D (iterate C D g k) ≫ P := by
        apply pullback.hom_ext
        · simp only [Category.assoc,stepPair_fst,pair_fst,stepPair_fst_assoc]
          exact ih
        · simp only [Category.assoc,stepPair_snd,pair_snd,stepPair_snd_assoc,
            Category.id_comp,Category.comp_id]
      rw [←Category.assoc,he,Category.assoc,SelectedCompletedAdditiveScaling318.addition,
        ←Category.assoc]

/-- The SAME tested point is killed by [m] on one model iff its image
is killed by [m] on the other. In particular, the equivalence is valid
for the full order and for EVERY lower-order vanishing test. -/
theorem kills_iff (m : ℕ) {T : Scheme.{u}} (p : T ⟶ scheme C D) :
    ((p ≫ γ) ≫ mul A B g₁ m = ((p ≫ γ) ≫ structureMap A B) ≫ infinity A B) ↔
      p ≫ mul C D g m = (p ≫ structureMap C D) ≫ infinity C D := by
  haveI : IsIso γ := by
    change IsIso (SelectedPointedShortScaling318.iso A B C D r hA hB).hom
    infer_instance
  have hl : (p ≫ γ) ≫ mul A B g₁ m = (p ≫ mul C D g m) ≫ γ := by
    rw [Category.assoc,conjugate,←Category.assoc]
  have hr : ((p ≫ γ) ≫ structureMap A B) ≫ infinity A B =
      ((p ≫ structureMap C D) ≫ infinity C D) ≫ γ := by
    calc
      _ = (p ≫ structureMap C D) ≫ infinity A B := by
        rw [Category.assoc p γ (structureMap A B),glued_base]
      _ = _ := by
        rw [Category.assoc (p ≫ structureMap C D) (infinity C D) γ,zero_preserved]
  rw [hl,hr]
  exact cancel_mono γ
end Scale
end SelectedCompletedMultiplication318

#print axioms SelectedCompletedMultiplication318.literal_mul
#print axioms SelectedCompletedMultiplication318.literal_eval
#print axioms SelectedCompletedMultiplication318.kills_iff
