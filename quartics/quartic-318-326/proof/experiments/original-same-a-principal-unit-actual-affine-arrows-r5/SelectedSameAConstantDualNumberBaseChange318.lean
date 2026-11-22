module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Identify the actual base change of a constant affine chart

The base generator is inr 1 of the fixed dual numbers. The equivalence
intertwines literal restriction on both coefficients.
-/

public section

open scoped TensorProduct

namespace SelectedSameAConstantDualNumberBaseChange318

variable {k B B' : Type*} [CommRing k] [CommRing B] [CommRing B']
  [Algebra k B] [Algebra k B']

/-- A coefficient ring map on the actual square-zero algebras. -/
def coeffMap {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    TrivSqZeroExt R R →+* TrivSqZeroExt S S where
  toFun z := TrivSqZeroExt.inl (f z.fst) + TrivSqZeroExt.inr (f z.snd)
  map_one' := by
    apply TrivSqZeroExt.ext <;> simp only [TrivSqZeroExt.fst_add,
      TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
      TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr,
      TrivSqZeroExt.fst_one, TrivSqZeroExt.snd_one, add_zero, zero_add, map_one, map_zero]
  map_zero' := by
    apply TrivSqZeroExt.ext <;> simp only [TrivSqZeroExt.fst_add,
      TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
      TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr,
      TrivSqZeroExt.fst_zero, TrivSqZeroExt.snd_zero, add_zero, zero_add, map_zero]
  map_add' a b := by
    apply TrivSqZeroExt.ext <;> simp only [TrivSqZeroExt.fst_add,
      TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
      TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, add_zero, zero_add, map_add]
  map_mul' a b := by
    apply TrivSqZeroExt.ext <;> simp only [TrivSqZeroExt.fst_add,
      TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
      TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, add_zero, zero_add,
      TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, op_smul_eq_smul, smul_eq_mul, map_add, map_mul]

theorem coeffMap_fst {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (z : TrivSqZeroExt R R) : (coeffMap f z).fst = f z.fst := by
  change (TrivSqZeroExt.inl (f z.fst) + TrivSqZeroExt.inr (f z.snd) :
    TrivSqZeroExt S S).fst = f z.fst
  simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]

theorem coeffMap_snd {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (z : TrivSqZeroExt R R) : (coeffMap f z).snd = f z.snd := by
  change (TrivSqZeroExt.inl (f z.fst) + TrivSqZeroExt.inr (f z.snd) :
    TrivSqZeroExt S S).snd = f z.snd
  simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]

local notation "D" => TrivSqZeroExt k k
local notation "T" => TrivSqZeroExt B B
local notation "eps" => (TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k)

private def right : TrivSqZeroExt k k →ₐ[k] TrivSqZeroExt B B :=
  { coeffMap (algebraMap k B) with
    commutes' := fun a => by
      apply TrivSqZeroExt.ext
      · change (coeffMap (algebraMap k B) (algebraMap k D a)).fst =
          (algebraMap k T a).fst
        simp only [coeffMap_fst, TrivSqZeroExt.algebraMap_eq_inl',
          TrivSqZeroExt.fst_inl, Algebra.algebraMap_self, RingHom.id_apply]
      · change (coeffMap (algebraMap k B) (algebraMap k D a)).snd =
          (algebraMap k T a).snd
        simp only [coeffMap_snd, TrivSqZeroExt.algebraMap_eq_inl',
          TrivSqZeroExt.snd_inl, map_zero] }

private def forward : (B ⊗[k] TrivSqZeroExt k k) →ₐ[k] TrivSqZeroExt B B :=
  Algebra.TensorProduct.lift (TrivSqZeroExt.inlAlgHom k B B) (right (k := k) (B := B))
    (fun _ _ => mul_comm _ _)

private theorem forward_tmul (b : B) (z : D) :
    forward (b ⊗ₜ[k] z) =
      TrivSqZeroExt.inl (b * algebraMap k B z.fst) +
        TrivSqZeroExt.inr (b * algebraMap k B z.snd) := by
  have h : forward (b ⊗ₜ[k] z) =
      TrivSqZeroExt.inlAlgHom k B B b * (right (k := k) (B := B) z) :=
    Algebra.TensorProduct.lift_tmul (TrivSqZeroExt.inlAlgHom k B B) (right (k := k) (B := B))
      (fun _ _ => mul_comm _ _) b z
  rw [h]
  change TrivSqZeroExt.inl b * (TrivSqZeroExt.inl (algebraMap k B z.fst) +
    TrivSqZeroExt.inr (algebraMap k B z.snd)) = _
  rw [mul_add, TrivSqZeroExt.inl_mul_inl, TrivSqZeroExt.inl_mul_inr, smul_eq_mul]

private def split (z : TrivSqZeroExt B B) : B ⊗[k] TrivSqZeroExt k k :=
  (z.fst ⊗ₜ[k] (1 : D)) + (z.snd ⊗ₜ[k] eps)

private theorem split_forward (x : B ⊗[k] TrivSqZeroExt k k) : split (forward x) = x := by
  induction x using TensorProduct.induction_on with
  | zero =>
    rw [map_zero]
    simp only [split, TrivSqZeroExt.fst_zero, TrivSqZeroExt.snd_zero,
      TensorProduct.zero_tmul, zero_add]
  | tmul b z =>
    have shift (a : k) (r : D) :
        (b * algebraMap k B a) ⊗ₜ[k] r = b ⊗ₜ[k] (a • r) := by
      rw [mul_comm b, ← Algebra.smul_def, TensorProduct.smul_tmul]
    have h₁ (a : k) : a • (1 : D) = TrivSqZeroExt.inl a := by
      calc
        _ = algebraMap k D a := (Algebra.algebraMap_eq_smul_one a).symm
        _ = _ := congrFun (TrivSqZeroExt.algebraMap_eq_inl k k) a
    have h₂ (a : k) : a • eps = TrivSqZeroExt.inr a := by
      calc
        a • eps = (algebraMap k D a) * eps := Algebra.smul_def a (eps : D)
        _ = (TrivSqZeroExt.inl a : D) * eps :=
          congrArg (fun w : D => w * eps) (congrFun (TrivSqZeroExt.algebraMap_eq_inl k k) a)
        _ = TrivSqZeroExt.inr a := by
          rw [TrivSqZeroExt.inl_mul_inr, smul_eq_mul, mul_one]
    rw [forward_tmul]
    simp only [split, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add,
      TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inl,
      TrivSqZeroExt.snd_inr, add_zero, zero_add, shift, h₁, h₂, ← TensorProduct.tmul_add,
      TrivSqZeroExt.inl_fst_add_inr_snd_eq]
  | add x y ihx ihy =>
    rw [map_add]
    simp only [split, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TensorProduct.add_tmul]
    have hx := ihx
    have hy := ihy
    unfold split at hx hy
    rw [add_add_add_comm, hx, hy]

private theorem forward_split (z : TrivSqZeroExt B B) :
    forward (k := k) (B := B) (split (k := k) z) = z := by
  unfold split
  simp only [map_add, forward_tmul, TrivSqZeroExt.fst_one, TrivSqZeroExt.snd_one,
    TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, map_one, map_zero, mul_one, mul_zero,
    TrivSqZeroExt.inl_zero, TrivSqZeroExt.inr_zero, add_zero, zero_add,
    TrivSqZeroExt.inl_fst_add_inr_snd_eq]

/-- The actual affine base-change tensor ring is the ring of both coefficients. -/
noncomputable def tensorIso : (B ⊗[k] TrivSqZeroExt k k) ≃+* TrivSqZeroExt B B :=
  RingEquiv.ofBijective (forward (k := k) (B := B)).toRingHom
    ⟨(show Function.LeftInverse split (forward (k := k) (B := B)) from split_forward).injective,
      (show Function.RightInverse split (forward (k := k) (B := B)) from forward_split).surjective⟩

/-- Both pure tensor coordinates, including the actual right scalar. -/
theorem tensorIso_tmul (b : B) (z : D) :
    tensorIso (b ⊗ₜ[k] z) =
      TrivSqZeroExt.inl (b * algebraMap k B z.fst) +
        TrivSqZeroExt.inr (b * algebraMap k B z.snd) := by
  unfold tensorIso
  exact forward_tmul b z

theorem tensorIso_from_base (z : D) :
    tensorIso (k := k) (B := B) (1 ⊗ₜ[k] z) = coeffMap (algebraMap k B) z := by
  simp only [tensorIso_tmul, one_mul]
  apply TrivSqZeroExt.ext
  · simp only [coeffMap_fst, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.fst_inr, add_zero]
  · simp only [coeffMap_snd, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
      TrivSqZeroExt.snd_inr, zero_add]

theorem tensorIso_from_chart (b : B) :
    tensorIso (b ⊗ₜ[k] (1 : D)) = (TrivSqZeroExt.inl b : T) := by
  simp only [tensorIso_tmul, TrivSqZeroExt.fst_one, TrivSqZeroExt.snd_one,
    map_one, map_zero, mul_one, mul_zero, TrivSqZeroExt.inr_zero, add_zero]

theorem coeffMap_chart_comp (f : B →ₐ[k] B') :
    (coeffMap f.toRingHom).comp (TrivSqZeroExt.inlHom B B) =
      (TrivSqZeroExt.inlHom B' B').comp f.toRingHom := by
  apply RingHom.ext
  intro b
  change coeffMap f.toRingHom (TrivSqZeroExt.inl b) = TrivSqZeroExt.inl (f b)
  apply TrivSqZeroExt.ext
  · simp only [coeffMap_fst, TrivSqZeroExt.fst_inl] <;> rfl
  · simp only [coeffMap_snd, TrivSqZeroExt.snd_inl, map_zero]

theorem coeffMap_base_comp (f : B →ₐ[k] B') :
    (coeffMap f.toRingHom).comp (coeffMap (algebraMap k B)) =
      coeffMap (algebraMap k B') := by
  apply RingHom.ext
  intro z
  apply TrivSqZeroExt.ext
  · simp only [RingHom.comp_apply, coeffMap_fst]
    change f (algebraMap k B z.fst) = algebraMap k B' z.fst
    exact f.commutes z.fst
  · simp only [RingHom.comp_apply, coeffMap_snd]
    change f (algebraMap k B z.snd) = algebraMap k B' z.snd
    exact f.commutes z.snd

theorem coeffMap_constants_comp :
    (TrivSqZeroExt.inlHom B B).comp (algebraMap k B) =
      (coeffMap (algebraMap k B)).comp (algebraMap k D) := by
  apply RingHom.ext
  intro a
  change TrivSqZeroExt.inl (algebraMap k B a) =
    coeffMap (algebraMap k B) (algebraMap k D a)
  exact ((right (k := k) (B := B)).commutes a).symm

/-- The original restriction map base-changed along the actual dual-number
extension is exactly the coefficientwise map under the canonical identifications. -/
theorem tensorIso_naturality (f : B →ₐ[k] B') (x : B ⊗[k] TrivSqZeroExt k k) :
    tensorIso (Algebra.TensorProduct.map f (AlgHom.id k (TrivSqZeroExt k k)) x) =
      coeffMap f.toRingHom (tensorIso x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul b z =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, tensorIso_tmul, tensorIso_tmul]
    apply TrivSqZeroExt.ext
    · simp only [coeffMap_fst, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
        TrivSqZeroExt.fst_inr, add_zero, map_mul]
      change f b * algebraMap k B' z.fst = f b * f (algebraMap k B z.fst)
      exact congrArg (fun x : B' => f b * x) (f.commutes z.fst).symm
    · simp only [coeffMap_snd, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
        TrivSqZeroExt.snd_inr, zero_add, map_mul]
      change f b * algebraMap k B' z.snd = f b * f (algebraMap k B z.snd)
      exact congrArg (fun x : B' => f b * x) (f.commutes z.snd).symm
  | add x y hx hy => simp only [map_add, hx, hy]

end SelectedSameAConstantDualNumberBaseChange318
