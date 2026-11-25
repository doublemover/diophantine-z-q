module
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.Tactic.Ring

@[expose] public section
noncomputable section

namespace OriginalAffineOriginCotangent318

universe u v w

variable {R : Type u} [CommRing R]
variable {B C E : Type*} [CommRing B] [CommRing C] [CommRing E]
variable [Algebra R B] [Algebra R C] [Algebra R E]

/-- Conormal of the actual origin of the affine R-chart. The augmentation
is the comorphism of that origin, not a separately supplied residue point. -/
abbrev originIdeal (e : B →ₐ[R] R) : Ideal B := RingHom.ker e.toRingHom
abbrev Cot (e : B →ₐ[R] R) := (originIdeal e).Cotangent

variable (e : B →ₐ[R] R)

def center : B →ₗ[R] (originIdeal e) :=
  LinearMap.codRestrict ((originIdeal e).restrictScalars R)
    (LinearMap.id - (Algebra.ofId R B).toLinearMap.comp e.toLinearMap) (by
      intro b
      change e (b - algebraMap R B (e b)) = 0
      rw [map_sub, e.commutes, sub_self])

@[simp] theorem center_val (b : B) :
    ((center e b : originIdeal e) : B) = b - algebraMap R B (e b) := rfl

/-- Universal first-order coordinate read, in the actual I/I². -/
def differential : B →ₗ[R] Cot e :=
  ((originIdeal e).toCotangent.restrictScalars R).comp (center e)

@[simp] theorem differential_ideal (x : originIdeal e) :
    differential e (x : B) = (originIdeal e).toCotangent x := by
  change (originIdeal e).toCotangent (center e (x : B)) = (originIdeal e).toCotangent x
  congr 1
  apply Subtype.ext
  have hx : e (x : B) = 0 := x.property
  simp [center_val, hx]

theorem differential_surjective : Function.Surjective (differential e) := by
  intro t
  obtain ⟨x, rfl⟩ := (originIdeal e).toCotangent_surjective t
  exact ⟨x, differential_ideal e x⟩

@[simp] theorem differential_base (r : R) :
    differential e (algebraMap R B r) = 0 := by
  have hz : center e (algebraMap R B r) = 0 := by
    apply Subtype.ext
    simp [center_val, e.commutes]
  change (originIdeal e).toCotangent (center e (algebraMap R B r)) = 0
  rw [hz, map_zero]

/-- Centering removes the quadratic error: product of two centered functions
lies in I². No assumption on the base (reduced, flat, or a field). -/
theorem differential_leibniz (a b : B) :
    differential e (a * b) = e a • differential e b + e b • differential e a := by
  let K := (originIdeal e).toCotangent.restrictScalars R
  change K (center e (a * b)) = e a • K (center e b) + e b • K (center e a)
  rw [← map_smul, ← map_smul, ← map_add]
  change (originIdeal e).toCotangent _ = (originIdeal e).toCotangent _
  apply (Ideal.toCotangent_eq _).2
  change (a * b - algebraMap R B (e (a * b))) -
    (algebraMap R B (e a) * (b - algebraMap R B (e b)) +
      algebraMap R B (e b) * (a - algebraMap R B (e a))) ∈ (originIdeal e) ^ 2
  have h : (a * b - algebraMap R B (e (a * b))) -
      (algebraMap R B (e a) * (b - algebraMap R B (e b)) +
        algebraMap R B (e b) * (a - algebraMap R B (e a))) =
      ((center e a : originIdeal e) : B) * (center e b : B) := by
    simp only [center_val, map_mul]
    ring
  rw [h, pow_two]
  exact Ideal.mul_mem_mul (center e a).property (center e b).property

/-- The exact first-order universal property of the actual origin conormal. -/
structure BasedDerivation (M : Type*) [AddCommGroup M] [Module R M] where
  linear : B →ₗ[R] M
  base_zero (c : R) : linear (algebraMap R B c) = 0
  leibniz (a b : B) : linear (a * b) = e a • linear b + e b • linear a

section Universal
variable {M : Type*} [AddCommGroup M] [Module R M]

def derivationOf (k : Cot e →ₗ[R] M) : BasedDerivation e M where
  linear := k.comp (differential e)
  base_zero r := by simp
  leibniz a b := by simp only [LinearMap.comp_apply, differential_leibniz, map_add, map_smul]

def universal (d : BasedDerivation e M) : Cot e →ₗ[R] M :=
  let k := d.linear.comp ((originIdeal e).restrictScalars R).subtype
  Ideal.Cotangent.lift k (by
    intro a b
    have ha : e (a : B) = 0 := a.property
    have hb : e (b : B) = 0 := b.property
    change d.linear ((a : B) * (b : B)) = 0
    rw [d.leibniz, ha, hb, zero_smul, zero_smul, add_zero])

@[simp] theorem universal_ideal (d : BasedDerivation e M) (x : originIdeal e) :
    universal e d ((originIdeal e).toCotangent x) = d.linear x := rfl

@[simp] theorem universal_differential (d : BasedDerivation e M) (b : B) :
    universal e d (differential e b) = d.linear b := by
  change universal e d ((originIdeal e).toCotangent (center e b)) = d.linear b
  rw [universal_ideal, center_val, map_sub, d.base_zero, sub_zero]

theorem ext_differential {k l : Cot e →ₗ[R] M}
    (h : ∀ b, k (differential e b) = l (differential e b)) : k = l := by
  ext t
  obtain ⟨b, rfl⟩ := differential_surjective e t
  exact h b

/-- The inverse universal endpoint does not require testing residue fields. -/
def universalEquiv : (Cot e →ₗ[R] M) ≃ BasedDerivation e M where
  toFun := derivationOf e
  invFun := universal e
  left_inv k := ext_differential e (by intro b; simp [derivationOf])
  right_inv d := by
    have hl : (derivationOf e (universal e d)).linear = d.linear := by
      ext b
      exact universal_differential e d b
    have extLinear : ∀ (d₁ d₂ : BasedDerivation e M), d₁.linear = d₂.linear → d₁ = d₂ := by
      rintro ⟨f, _, _⟩ ⟨g, _, _⟩ h
      cases h
      rfl
    exact extLinear _ _ hl

end Universal

section PointedMaps
variable (e' : C →ₐ[R] R) (e'' : E →ₐ[R] R)

def pullCot (h : B →ₐ[R] C) (atOrigin : e'.comp h = e) : Cot e →ₗ[R] Cot e' :=
  Ideal.mapCotangent (originIdeal e) (originIdeal e') h (fun x hx => by
    change e' (h x) = 0
    exact (congrArg (fun k : B →ₐ[R] R => k x) atOrigin).trans hx)

theorem pullCot_ideal (h : B →ₐ[R] C) (atOrigin : e'.comp h = e) (x : originIdeal e) :
    pullCot e e' h atOrigin ((originIdeal e).toCotangent x) =
      (originIdeal e').toCotangent ⟨h x, by
        change e' (h x) = 0
        exact (congrArg (fun k : B →ₐ[R] R => k x) atOrigin).trans x.property⟩ := rfl

theorem pullCot_differential (h : B →ₐ[R] C) (atOrigin : e'.comp h = e) (b : B) :
    pullCot e e' h atOrigin (differential e b) = differential e' (h b) := by
  change pullCot e e' h atOrigin ((originIdeal e).toCotangent (center e b)) =
    (originIdeal e').toCotangent (center e' (h b))
  rw [pullCot_ideal]
  congr 1
  apply Subtype.ext
  have hh : e' (h b) = e b := congrArg (fun k : B →ₐ[R] R => k b) atOrigin
  simp only [center_val, map_sub, h.commutes, hh]

theorem pullCot_comp (h : B →ₐ[R] C) (k : C →ₐ[R] E)
    (hh : e'.comp h = e) (hk : e''.comp k = e') :
    pullCot e e'' (k.comp h) (by rw [← AlgHom.comp_assoc, hk, hh]) =
      (pullCot e' e'' k hk).comp (pullCot e e' h hh) := by
  apply ext_differential e
  intro b
  simp only [pullCot_differential, LinearMap.comp_apply, AlgHom.comp_apply]

/-- The actual tangent/Lie map, dual to pullback of the identity
cotangent; order of geometric composition is retained. -/
def pushLie (h : B →ₐ[R] C) (atOrigin : e'.comp h = e) :
    Module.Dual R (Cot e') →ₗ[R] Module.Dual R (Cot e) :=
  (pullCot e e' h atOrigin).dualMap

theorem pushLie_comp (h : B →ₐ[R] C) (k : C →ₐ[R] E)
    (hh : e'.comp h = e) (hk : e''.comp k = e') :
    pushLie e e'' (k.comp h) (by rw [← AlgHom.comp_assoc, hk, hh]) =
      (pushLie e e' h hh).comp (pushLie e' e'' k hk) := by
  unfold pushLie
  rw [pullCot_comp]
  rfl

end PointedMaps
end OriginalAffineOriginCotangent318

#print axioms OriginalAffineOriginCotangent318.differential_leibniz
#print axioms OriginalAffineOriginCotangent318.universalEquiv
#print axioms OriginalAffineOriginCotangent318.pullCot_differential
#print axioms OriginalAffineOriginCotangent318.pushLie_comp
