module

public import OriginalYuanPulledExactKSImage318
public import OriginalFiveContactExactGauge318
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Tactic.NormNum

@[expose] public section
noncomputable section

namespace OriginalYuanAtPlaceFiniteProducer318

open scoped TensorProduct nonZeroDivisors
open NumberField SectionHeight318
open OriginalRawKSPrimitive210318 OriginalYuanPulledExactKSImage318
open OriginalExactLocalKSUnit318 OriginalFiveContactExactGauge318

variable {E : Type*} [Field E] [NumberField E] (w : FinitePlace E)
local notation "V" => localRing w

theorem local_integral_norm (u : V) : w (u:E)≤1 := by
  letI : IsLocalization (placePrime w).primeCompl V :=
    Localization.subalgebra.isLocalization_subalgebra E (placePrime w).primeCompl (placePrime w).primeCompl_le_nonZeroDivisors
  obtain ⟨⟨x,y⟩,e⟩ := IsLocalization.surj (placePrime w).primeCompl u
  have nx : w (algebraMap (𝓞 E) E x)≤1 :=
    (FinitePlace.norm_embedding_eq w _).ge.trans
      (FinitePlace.norm_le_one E (FinitePlace.maximalIdeal w) x)
  have ny : w (algebraMap (𝓞 E) E (y:𝓞 E))=1 :=
    (FinitePlace.norm_embedding_eq w _).symm.trans
      ((FinitePlace.norm_eq_one_iff_notMem E (FinitePlace.maximalIdeal w) (y:𝓞 E)).mpr y.property)
  have ee := congrArg (fun t:V=>w (t:E)) e
  change w ((u:E)*algebraMap (𝓞 E) E (y:𝓞 E))=w (algebraMap (𝓞 E) E x) at ee
  rw [map_mul,ny,mul_one] at ee
  exact ee.trans_le nx

theorem paid_section_coefficient (C : FrameNorms E) (b s : E) (hb : b≠0)
    (canonicalNorm : C.finiteNorm w=(w b)⁻¹)
    (genuine : s∈coeffLine (R:=V) b) :
    w s*C.finiteNorm w≤1 := by
  obtain ⟨r,e⟩ := Submodule.mem_span_singleton.mp genuine
  change (r:E)*b=s at e
  have nb : w b≠0 := ((FinitePlace.pos_iff (w:=w)).mpr hb).ne'
  rw [←e,canonicalNorm,map_mul,mul_assoc,mul_inv_cancel₀ nb,mul_one]
  exact local_integral_norm w r

variable {A M N : Type*} [CommRing A] [Algebra A V]
  [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
variable (raw : M→ₗ[A]N)
variable (rawInj : Function.Injective raw)
variable (regular : Function.Injective (scale210 : N→ₗ[A]N))
variable (trueImage : LinearMap.range raw=LinearMap.range (scale210 : N→ₗ[A]N))
variable (H C : FrameNorms E) (a b k : E)
variable (ha : a≠0) (hb : b≠0)
variable (hodgeNorm : H.finiteNorm w=(w a)⁻¹)
variable (canonicalNorm : C.finiteNorm w=(w b)⁻¹)
variable (η : (V⊗[A]M) ≃ₗ[V] coeffLine (R:=V) (a^2))
variable (δ : (V⊗[A]N) ≃ₗ[V] coeffLine (R:=V) b)
variable (rawFromSameGlobalMap : ∀ m : V⊗[A]M,
  (δ (raw.baseChange V m):E)=(η m:E)*k)

/-- This is the unchanged v1.1 field; the input a is the true
primitive generator relative to the rational ℓ, not to ℓ².
The model tensor identifications and generic equality use the
same pulled universal group and the same Q. -/
def exact_place_image : OriginalFiveContactExactGauge318.FiniteImage H C k w where
  hodgePrimitive := a
  canonicalPrimitive := b
  hodge_ne := ha
  canonical_ne := hb
  hodge_norm := hodgeNorm
  canonical_norm := canonicalNorm
  exact_image := exact_coefficient_lattices raw rawInj regular trueImage a b k η δ rawFromSameGlobalMap

/-- In the Q gauge the literal coefficients are J² and T J².
The outputs use the genuine globally extended sections at the
actual centre via their exact tensor evaluations, not two
integral witnesses recomputed in residue fields. -/
include hb canonicalNorm in
theorem exact_place_paid_pair
    (y : Fin 2→V⊗[A]N) (t : E)
    (read : ∀ i, (δ (y i):E)=![(2765952000:E)^2,t*(2765952000:E)^2] i)
    (i : Fin 2) :
    w (![ (2765952000:E)^2,t*(2765952000:E)^2] i)*C.finiteNorm w≤1 :=
  paid_section_coefficient w C b _ hb canonicalNorm
    (integral_original_coefficient b δ (y i) _ (read i))

end OriginalYuanAtPlaceFiniteProducer318
