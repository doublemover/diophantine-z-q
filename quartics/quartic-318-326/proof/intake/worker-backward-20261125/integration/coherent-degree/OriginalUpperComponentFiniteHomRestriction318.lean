module
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Module.LinearMap.Basic

public section
noncomputable section
namespace OriginalUpperComponentFiniteHomRestriction318

variable {A B M V : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
  [AddCommGroup V] [Module A V]

/-- The action by multiplication in the actual finite-pencil algebra on the
first input to its Hom coefficient. This is not the trace pairing. -/
def Balanced (F : M →ₗ[A] B →ₗ[A] V) : Prop :=
  ∀ (b c : B) (m : M), F (b • m) c = F m (b * c)

/-- Multiplying the actual input by the actual algebra element gives the
inverse to the counit (evaluation at one). No trace/separable extension. -/
def coextend (u : M →ₗ[A] V) : M →ₗ[A] (B →ₗ[A] V) where
  toFun m :=
    { toFun := fun b => u (b • m)
      map_add' := by intro b c; rw [add_smul, map_add]
      map_smul' := by intro a b; rw [smul_assoc, map_smul] }
  map_add' m n := by
    apply LinearMap.ext
    intro b
    change u (b • (m + n)) = u (b • m) + u (b • n)
    rw [smul_add, map_add]
  map_smul' a m := by
    apply LinearMap.ext
    intro b
    change u (b • a • m) = a • u (b • m)
    rw [smul_comm b a m, map_smul]

@[simp]
theorem coextend_apply (u : M →ₗ[A] V) (m : M) (b : B) :
    coextend u m b = u (b • m) := rfl

theorem coextend_balanced (u : M →ₗ[A] V) : Balanced (coextend u) := by
  intro b c m
  rw [coextend_apply, coextend_apply, mul_comm b c, mul_smul]

/-- Actual Hom counit of the finite affine map, evaluated at 1. -/
def atOne (F : M →ₗ[A] B →ₗ[A] V) : M →ₗ[A] V where
  toFun m := F m 1
  map_add' m n := by simp
  map_smul' a m := by simp

@[simp]
theorem atOne_apply (F : M →ₗ[A] B →ₗ[A] V) (m : M) : atOne F m = F m 1 := rfl

@[simp]
theorem atOne_coextend (u : M →ₗ[A] V) : atOne (coextend u) = u := by
  apply LinearMap.ext
  intro m
  simp

theorem coextend_atOne (F : M →ₗ[A] B →ₗ[A] V) (hF : Balanced F) :
    coextend (atOne F) = F := by
  apply LinearMap.ext
  intro m
  apply LinearMap.ext
  intro b
  rw [coextend_apply, atOne_apply, hF b 1 m, mul_one]

/-- The actual affine finite-pushforward Hom read, with its scalar
multiplication condition rather than an independent dual-space isomorphism. -/
def counitEquiv : { F : M →ₗ[A] B →ₗ[A] V // Balanced F } ≃ (M →ₗ[A] V) where
  toFun F := atOne F.1
  invFun u := ⟨coextend u, coextend_balanced u⟩
  left_inv F := Subtype.ext (coextend_atOne F.1 F.2)
  right_inv u := atOne_coextend u

/-- Overlap transport is automatic once the arrows commute on the finite
algebra and module: at one preserves the actual coefficients. Stated on
underlying elements so base extensions need no competing module instance. -/
theorem counit_overlap
    {A' B' M' V' : Type*} [CommRing A'] [CommRing B'] [Algebra A' B']
    [AddCommGroup M'] [Module A' M'] [AddCommGroup V'] [Module A' V']
    (Bmap : B →+* B') (Mmap : M → M') (Vmap : V → V')
    (F : M →ₗ[A] B →ₗ[A] V) (F' : M' →ₗ[A'] B' →ₗ[A'] V')
    (h : ∀ m b, F' (Mmap m) (Bmap b) = Vmap (F m b)) (m : M) :
    atOne F' (Mmap m) = Vmap (atOne F m) := by
  simpa only [atOne_apply, map_one] using h m 1

end OriginalUpperComponentFiniteHomRestriction318
