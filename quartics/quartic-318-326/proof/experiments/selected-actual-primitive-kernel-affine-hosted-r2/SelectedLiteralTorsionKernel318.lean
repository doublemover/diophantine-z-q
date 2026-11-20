module
public import LiteralSchemePointGroup318
public import CubicClosedImmersion318
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.GroupTheory.OrderOfElement
import all LiteralSchemePointGroup318
public section
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LiteralSchemePointOperations318

namespace SelectedLiteralTorsionKernel318

abbrev Base (n : ℕ) := Spec (CommRingCat.of (OpenJModel318.Base n))
abbrev Curve (n : ℕ) := WeierstrassGluing318.scheme
  (OpenJAffineScheme318.A n) (OpenJAffineScheme318.B n)
abbrev projection (n : ℕ) : Curve n ⟶ Base n :=
  WeierstrassGluing318.structureMap (OpenJAffineScheme318.A n) (OpenJAffineScheme318.B n)
abbrev origin (n : ℕ) : Base n ⟶ Curve n :=
  WeierstrassGluing318.infinity (OpenJAffineScheme318.A n) (OpenJAffineScheme318.B n)

/-- Pullback of actual points by a test Scheme map. The dependent base changes
from b to f≫b; no pointwise identification is imposed. -/
@[expose] def precomp (n : ℕ) {T U : Scheme} (b : T ⟶ Base n) (f : U ⟶ T) :
    Points n b →+ Points n (f ≫ b) := by
  let L (p : Points n b) : Points n (f ≫ b) :=
    ⟨f ≫ p.val,by rw [Category.assoc,p.property]⟩
  refine { toFun := L, map_zero' := ?_, map_add' := ?_ }
  · apply Subtype.ext
    change f ≫ (b ≫ origin n) = (f ≫ b) ≫ origin n
    exact (Category.assoc _ _ _).symm
  · intro p q
    have hpq : f ≫ pair n b p q = pair n (f ≫ b) (L p) (L q) := by
      apply pullback.hom_ext
      · simp only [Category.assoc,pair_fst] <;> rfl
      · simp only [Category.assoc,pair_snd] <;> rfl
    apply Subtype.ext
    change f ≫ (pair n b p q ≫ CompletedAddition318.addition _ _ _) =
      pair n (f ≫ b) (L p) (L q) ≫ CompletedAddition318.addition _ _ _
    rw [← Category.assoc,hpq]

@[simp] theorem precomp_val (n : ℕ) {T U : Scheme} (b : T ⟶ Base n)
    (f : U ⟶ T) (p : Points n b) :
    (precomp n b f p).val = f ≫ p.val := rfl

@[expose] def identityPoint (n : ℕ) : Points n (projection n) :=
  ⟨𝟙 _,Category.id_comp _⟩

/-- The actual arbitrary-n multiplication morphism on the literal proper
short-Weierstrass curve. It is not a specialized tripling formula. -/
@[expose] def mulMap (n m : ℕ) : Curve n ⟶ Curve n :=
  (m • identityPoint n).val

@[reassoc] theorem mul_over (n m : ℕ) : mulMap n m ≫ projection n = projection n :=
  (m • identityPoint n).property

/-- The universal morphism evaluates to the actual scalar operation on every
test Scheme, including nilpotent or disconnected tests. -/
theorem mul_value (n m : ℕ) {T : Scheme} (b : T ⟶ Base n) (p : Points n b) :
    (m • p).val = p.val ≫ mulMap n m := by
  obtain ⟨p,hp⟩ := p
  subst b
  let P : Points n (p ≫ projection n) := ⟨p,rfl⟩
  have hu : precomp n (projection n) p (identityPoint n) = P := by
    apply Subtype.ext
    simp only [precomp_val,identityPoint,Category.comp_id]
  have h := congrArg Subtype.val
    (map_nsmul (precomp n (projection n) p) (identityPoint n) m)
  rw [precomp_val,hu] at h
  exact h.symm

@[reassoc] theorem origin_mul (n m : ℕ) : origin n ≫ mulMap n m = origin n := by
  have h := (mul_value n m (𝟙 (Base n)) (0 : Points n (𝟙 (Base n)))).symm
  have hz : (0 : Points n (𝟙 (Base n))).val = origin n := by
    change (𝟙 (Base n)) ≫ origin n = origin n
    exact Category.id_comp _
  rwa [nsmul_zero,hz] at h

theorem mul_commute (n m k : ℕ) :
    mulMap n m ≫ mulMap n k = mulMap n k ≫ mulMap n m := by
  have hm := mul_value n k (projection n) (m • identityPoint n)
  have hk := mul_value n m (projection n) (k • identityPoint n)
  change (k • (m • identityPoint n)).val = mulMap n m ≫ mulMap n k at hm
  change (m • (k • identityPoint n)).val = mulMap n k ≫ mulMap n m at hk
  rw [← hm,← hk,smul_smul,smul_smul,Nat.mul_comm]

abbrev Kernel (n m : ℕ) := pullback (mulMap n m) (origin n)
abbrev inclusion (n m : ℕ) : Kernel n m ⟶ Curve n := pullback.fst _ _
abbrev kernelProjection (n m : ℕ) : Kernel n m ⟶ Base n := pullback.snd _ _

@[reassoc] theorem kernel_equation (n m : ℕ) :
    inclusion n m ≫ mulMap n m = kernelProjection n m ≫ origin n :=
  pullback.condition

@[reassoc] theorem inclusion_over (n m : ℕ) :
    inclusion n m ≫ projection n = kernelProjection n m := by
  have hz : origin n ≫ projection n = 𝟙 (Base n) :=
    WeierstrassGluing318.infinity_section _ _
  rw [← mul_over n m,← Category.assoc,kernel_equation,Category.assoc,hz,Category.comp_id]

/-- The zero section inside this actual full kernel (the same K_M will be
used for all lower-order tests). -/
@[expose] def zeroSection (n m : ℕ) : Base n ⟶ Kernel n m :=
  pullback.lift (origin n) (𝟙 _) (by simp only [origin_mul,Category.id_comp])

@[reassoc] theorem zeroSection_inclusion (n m : ℕ) :
    zeroSection n m ≫ inclusion n m = origin n := by simp [zeroSection]

@[reassoc] theorem zeroSection_projection (n m : ℕ) :
    zeroSection n m ≫ kernelProjection n m = 𝟙 _ := by simp [zeroSection]

/-- Every lower multiplication actually maps the same M-kernel into itself:
commutation and the real zero section supply the pullback equation. -/
@[expose] def mulInside (n m k : ℕ) : Kernel n m ⟶ Kernel n m :=
  pullback.lift (inclusion n m ≫ mulMap n k) (kernelProjection n m) (by
    rw [Category.assoc,mul_commute n k m,← Category.assoc,kernel_equation,
      Category.assoc,origin_mul])

@[reassoc] theorem mulInside_inclusion (n m k : ℕ) :
    mulInside n m k ≫ inclusion n m = inclusion n m ≫ mulMap n k := by
  simp [mulInside]

@[reassoc] theorem mulInside_projection (n m k : ℕ) :
    mulInside n m k ≫ kernelProjection n m = kernelProjection n m := by simp [mulInside]

private theorem origin_closed (n : ℕ) : IsClosedImmersion (origin n) :=
  CubicClosedImmersion318.infinity_closed _ _

instance inclusion_closed (n m : ℕ) : IsClosedImmersion (inclusion n m) := by
  letI := origin_closed n
  infer_instance

/-- The actual kernel point of a test morphism into the actual pullback. -/
@[expose] def pointOf (n m : ℕ) {T : Scheme} (p : T ⟶ Kernel n m) :
    Points n (p ≫ kernelProjection n m) :=
  ⟨p ≫ inclusion n m,
    (Category.assoc p (inclusion n m) (projection n)).trans
      (congrArg (fun z : Kernel n m ⟶ Base n => p ≫ z) (inclusion_over n m))⟩

theorem pointOf_killed (n m : ℕ) {T : Scheme} (p : T ⟶ Kernel n m) :
    m • pointOf n m p = 0 := by
  apply Subtype.ext
  rw [mul_value]
  change (p ≫ inclusion n m) ≫ mulMap n m = (p ≫ kernelProjection n m) ≫ origin n
  simp only [Category.assoc,kernel_equation]

end SelectedLiteralTorsionKernel318
#print axioms SelectedLiteralTorsionKernel318.mul_value
#print axioms SelectedLiteralTorsionKernel318.mulInside_inclusion
#print axioms SelectedLiteralTorsionKernel318.pointOf_killed
