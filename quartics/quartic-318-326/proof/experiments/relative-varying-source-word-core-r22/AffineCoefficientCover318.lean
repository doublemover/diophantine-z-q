module
public import VaryingSourceCoefficientPullback318
public import AffineSchemeAlgebraMap318
public import Mathlib.AlgebraicGeometry.Gluing
public section
noncomputable section
namespace AffineCoefficientCover318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
/-- Genuine affine coefficient charts, with actual R-algebra arrows,
open immersions and coverage of EVERY coefficient-spectrum point. -/
structure Data where
  Index : Type u
  ring : Index → CommRingCat.{u}
  [algebra : ∀ i, Algebra R (ring i)]
  coefficient : ∀ i, S →ₐ[R] ring i
  open_map : ∀ i, IsOpenImmersion (Spec.map (CommRingCat.ofHom (coefficient i).toRingHom))
  covers : ∀ x : Spec (CommRingCat.of S), ∃ i,
    x ∈ Set.range (Spec.map (CommRingCat.ofHom (coefficient i).toRingHom))
attribute [instance] Data.algebra Data.open_map
variable (C : Data R S)
@[expose] def cover : (Spec (CommRingCat.of S)).OpenCover where
  I₀ := C.Index
  X i := Spec (C.ring i)
  f i := Spec.map (CommRingCat.ofHom (C.coefficient i).toRingHom)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨C.covers,fun i => inferInstance⟩
@[reassoc] lemma over_base (i : C.Index) : (cover R S C).f i ≫
    VaryingSourceCoefficientPullback318.base R S=VaryingSourceCoefficientPullback318.base R (C.ring i) :=
  VaryingSourceCoefficientPullback318.coefficient_base R S (C.ring i) (C.coefficient i)
end AffineCoefficientCover318
