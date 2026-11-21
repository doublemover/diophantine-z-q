module
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Tactic.Ring
public section
noncomputable section

namespace SelectedSameAPrimitiveKSSpecialization318

section
variable {R : Type*} [CommRing R]

/-- The image of the basis of a free line under an actual linear isomorphism is
a unit. The inverse coefficient comes from the inverse *same* isomorphism. -/
def frameUnit (e : R ≃ₗ[R] R) : Rˣ := by
  have h : e 1 * e.symm 1 = 1 := by
    calc
      e 1 * e.symm 1 = (e.symm 1) • e 1 := mul_comm _ _
      _ = e ((e.symm 1) • (1:R)) := (e.map_smul _ _).symm
      _ = 1 := by rw [smul_eq_mul, mul_one, LinearEquiv.apply_symm_apply]
  have he : e.symm 1 * e 1 = 1 := (mul_comm _ _).trans h
  exact ⟨e 1, e.symm 1, h, he⟩

@[simp] theorem frameUnit_val (e : R ≃ₗ[R] R) :
    ((frameUnit e : Rˣ) : R) = e 1 := by unfold frameUnit <;> rfl
end

variable {R S L M N V : Type*}
variable [CommRing R] [CommRing S] [Field L]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable [AddCommGroup V] [Module L V]

/-- The integral unit of the divided map, evaluated in the *actual* trait ring.
No inversion of 210 or assumption of flatness on the trait is involved. -/
def specializedUnit (ev : R →+* S) (h : M ≃ₗ[R] R) (d : N ≃ₗ[R] R)
    (normalized : M ≃ₗ[R] N) : Sˣ :=
  Units.map ev.toMonoidHom
    (frameUnit ((h.symm.trans normalized).trans d))

@[simp] theorem specializedUnit_val (ev : R →+* S) (h : M ≃ₗ[R] R)
    (d : N ≃ₗ[R] R) (normalized : M ≃ₗ[R] N) :
    ((specializedUnit ev h d normalized : Sˣ) : S) =
      ev (d (normalized (h.symm 1))) := by unfold specializedUnit frameUnit <;> rfl

/-- Apply actual KS base change on *one* primitive tensor. Here `dt2`
is the selected generic (dt)^2, and `τ` is its *linear* dt coefficient
before squaring. `ks` evaluates the unscaled determinant in the
global Hodge-square basis. The result supplies the exact raw scalar
and integral unit, not a presumed norm comparison. This works without
flatness or injectivity of the stalk-to-trait evaluation. -/
theorem raw_in_marked_dt (ev : R →+* S) (inc : S →+* L)
    (h : M ≃ₗ[R] R) (d : N ≃ₗ[R] R)
    (normalized : M ≃ₗ[R] N) (raw : M →ₗ[R] N)
    (push : N →ₛₗ[inc.comp ev] V) (ks : L ≃ₗ[L] V)
    (δ ρ τ : L) (dt2 : V)
    (normalize : ∀ x, raw x = (210:R) • normalized x)
    (naturality : ks (ρ^2) = push (raw (h.symm 1)))
    (globalFrame : ks 1 = δ • dt2)
    (sameDt : dt2 = τ^2 • push (d.symm 1)) :
    δ * ρ^2 * τ^2 = (210:L) * inc ↑(specializedUnit ev h d normalized) := by
  let z := push (d.symm 1)
  have hn : normalized (h.symm 1) =
      d (normalized (h.symm 1)) • d.symm 1 := by
    apply d.injective
    simp only [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  have he : ks (ρ^2) =
      ((210:L) * inc ↑(specializedUnit ev h d normalized)) • z := by
    calc
      ks (ρ^2) = push (raw (h.symm 1)) := naturality
      _ = push ((210:R) • normalized (h.symm 1)) := congrArg push (normalize _)
      _ = push (((210:R)*d (normalized (h.symm 1))) • d.symm 1) := by
        rw [← smul_smul]
        exact congrArg (fun x : N => push ((210:R) • x)) hn
      _ = _ := by
        rw [push.map_smulₛₗ, RingHom.comp_apply]
        simp only [map_mul, map_ofNat, specializedUnit_val, z]
  have hm : ks (ρ^2) = (δ*ρ^2*τ^2) • z := by
    calc
      ks (ρ^2) = ks (ρ^2 • (1:L)) := by rw [smul_eq_mul, mul_one]
      _ = (ρ^2*(δ*τ^2)) • z := by
        simp only [map_smul, globalFrame, sameDt, smul_smul, mul_assoc, z]
      _ = (δ*ρ^2*τ^2) • z := by
        rw [show ρ^2*(δ*τ^2) = δ*ρ^2*τ^2 by ring]
  have hz : z ≠ 0 := by
    intro hz0
    have hz' : push (d.symm 1) = 0 := hz0
    have heq := globalFrame
    rw [sameDt, hz', smul_zero, smul_zero] at heq
    exact one_ne_zero (ks.injective (heq.trans (map_zero ks).symm))
  apply sub_eq_zero.mp
  have hc : (δ*ρ^2*τ^2 - (210:L)*inc ↑(specializedUnit ev h d normalized)) • z = 0 := by
    rw [sub_smul, ← hm, ← he, sub_self]
  let c := δ*ρ^2*τ^2 - (210:L)*inc ↑(specializedUnit ev h d normalized)
  change c = 0
  by_contra hc0
  apply hz
  calc
    z = c⁻¹ • (c • z) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
    _ = 0 := by rw [show c • z = 0 from hc, smul_zero]

/-- The normalized coefficient survives in the residue field; the raw
one vanishes exactly when the residue characteristic kills 210. -/
theorem residue_comparison {k : Type*} [Field k] (reduction : S →+* k)
    (ev : R →+* S) (h : M ≃ₗ[R] R) (d : N ≃ₗ[R] R)
    (normalized : M ≃ₗ[R] N) :
    let η := specializedUnit ev h d normalized
    reduction (η:S) ≠ 0 ∧
      (reduction ((210:S) * (η:S)) = 0 ↔ (210:k) = 0) := by
  let η := specializedUnit ev h d normalized
  have hη : reduction (η:S) ≠ 0 := by
    intro bad
    have e := congrArg reduction η.mul_inv
    change reduction ((η:S) * (↑η⁻¹:S)) = reduction 1 at e
    rw [map_mul, bad, zero_mul, map_one] at e
    exact zero_ne_one e
  refine ⟨hη, ?_⟩
  rw [map_mul, map_ofNat, mul_eq_zero]
  exact or_iff_left hη

end SelectedSameAPrimitiveKSSpecialization318

#print axioms SelectedSameAPrimitiveKSSpecialization318.raw_in_marked_dt
