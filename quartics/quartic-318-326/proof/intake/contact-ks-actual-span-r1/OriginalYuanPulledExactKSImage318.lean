module

public import OriginalRawKSPrimitive210318
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Algebra.Module.LinearMap.Basic

@[expose] public section
noncomputable section

namespace OriginalYuanPulledExactKSImage318

open scoped TensorProduct
open OriginalRawKSPrimitive210318

variable {A R E M N : Type*}
  [CommRing A] [CommRing R] [Field E] [Algebra A R] [Algebra R E]
  [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]

abbrev coeffLine (x : E) : Submodule R E := Submodule.span R ({x} : Set E)

def multiplyBy (c : E) : E→ₗ[R]E where
  toFun z := z*c
  map_add' x y := add_mul x y c
  map_smul' r z := by
    rw [RingHom.id_apply]
    exact Algebra.smul_mul_assoc r z c

@[simp]
theorem multiplyBy_apply (c z : E) : multiplyBy (R:=R) c z=z*c := rfl

theorem map_line (c z : E) :
    (coeffLine (R:=R) z).map (multiplyBy c)=coeffLine (R:=R) (z*c) := by
  rw [coeffLine,Submodule.map_span,Set.image_singleton] <;> rfl

variable (raw : M→ₗ[A]N)
variable (rawInj : Function.Injective raw)
variable (regular210 : Function.Injective (scale210 : N→ₗ[A]N))
variable (exactImage : LinearMap.range raw=LinearMap.range (scale210 : N→ₗ[A]N))

variable (a b k : E)
variable (hodgeCoeff : (R⊗[A]M) ≃ₗ[R] coeffLine (R:=R) (a^2))
variable (canonicalCoeff : (R⊗[A]N) ≃ₗ[R] coeffLine (R:=R) b)

/-- Explicitly transport the *pre-change* normalized isomorphism
between the two genuine local coefficient lattices. -/
def actualPrimitive :
    coeffLine (R:=R) (a^2) ≃ₗ[R] coeffLine (R:=R) b :=
  hodgeCoeff.symm.trans ((changed raw rawInj regular210 exactImage R).trans canonicalCoeff)

variable (genericRead : ∀ m : R⊗[A]M,
  ((canonicalCoeff (raw.baseChange R m) : coeffLine (R:=R) b) : E)=
    ((hodgeCoeff m : coeffLine (R:=R) (a^2)) : E)*k)

include genericRead in
theorem actual_raw_on_every_local_section (z : coeffLine (R:=R) (a^2)) :
    (z:E)*k =
      (210:E) * ((actualPrimitive raw rawInj regular210 exactImage a b
        hodgeCoeff canonicalCoeff z : coeffLine (R:=R) b):E) := by
  have h := genericRead (hodgeCoeff.symm z)
  rw [LinearEquiv.apply_symm_apply] at h
  rw [changed_raw raw rawInj regular210 exactImage R] at h
  simp only [LinearMap.smul_apply,LinearEquiv.coe_coe,map_smul] at h
  change ((210:R) •
    ((canonicalCoeff (changed raw rawInj regular210 exactImage R (hodgeCoeff.symm z)) :
      coeffLine (R:=R) b):E))=(z:E)*k at h
  simpa only [Algebra.smul_def,map_ofNat,actualPrimitive,LinearEquiv.trans_apply] using h.symm

include rawInj regular210 exactImage genericRead in
/-- Native finite-image statement in the original Q-coordinate
gauge. It follows from the entire local lattice and the actual
generic raw map, not by presuming a primitive unit or absolute
norm identity on the retained height field. -/
theorem exact_coefficient_lattices :
    coeffLine (R:=R) (a^2*k)=coeffLine (R:=R) ((210:E)*b) := by
  rw [←map_line k (a^2),mul_comm (210:E) b,←map_line (210:E) b]
  let P := actualPrimitive raw rawInj regular210 exactImage a b hodgeCoeff canonicalCoeff
  have h := actual_raw_on_every_local_section raw rawInj regular210 exactImage a b k
    hodgeCoeff canonicalCoeff genericRead
  apply SetLike.ext
  intro z
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨(P ⟨x,hx⟩:E),(P ⟨x,hx⟩).property,?_⟩
    exact (mul_comm (P ⟨x,hx⟩:E) (210:E)).trans (h ⟨x,hx⟩).symm
  · rintro ⟨y,hy,rfl⟩
    refine ⟨(P.symm ⟨y,hy⟩:E),(P.symm ⟨y,hy⟩).property,?_⟩
    exact (h (P.symm ⟨y,hy⟩)).trans
      (by rw [show actualPrimitive raw rawInj regular210 exactImage a b hodgeCoeff canonicalCoeff
        (P.symm ⟨y,hy⟩)=⟨y,hy⟩ from P.apply_symm_apply _]
          ; exact mul_comm _ _)

/-- Each truly pulled original section already belongs to the
same canonical local lattice; its scale in Q is not recomputed
in an independent field at each place. -/
theorem integral_original_coefficient (s : R⊗[A]N) (literal : E)
    (read : (canonicalCoeff s:E)=literal) :
    literal∈coeffLine (R:=R) b :=
  read ▸ (canonicalCoeff s).property

end OriginalYuanPulledExactKSImage318
