module
public import OriginalR8FirstSlotSplitEqualizer318
public import OriginalR8WildFixedFlatBase318
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public section
namespace OriginalR8RepresentedFirstSlotEqualizer318
open scoped TensorProduct
open TensorProduct
open OriginalR8WildFixedFlatBase318 (defect defect_piece pieces)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w r s
variable {F : Type u} {K : Type v} {A : Type w} {B : Type r}
  [CommRing F] [CommRing K] [CommRing A] [CommRing B]
  [Algebra F K] [Algebra F A] [Algebra F B]
variable {G I J : Type s} [Fintype G] [DecidableEq G] [SMul G I]
variable (ι : A →ₐ[F] B) (σ : G → B ≃ₐ[F] B)

private theorem tensor_zero_iff_fixed (z : K ⊗[F] B) :
    (defect σ).lTensor K z = 0 ↔ ∀ g : G, ((σ g).toLinearMap.lTensor K) z = z := by
  constructor
  · intro h g
    have h' := defect_piece σ z g
    rw [h,map_zero] at h'
    exact sub_eq_zero.mp h'.symm
  · intro h
    apply pieces.injective
    funext g
    simp only [defect_piece σ z g,h g,sub_self,map_zero,Pi.zero_apply]

/-- The affine orbit ring A maps to the represented frame ring B by
the whole first-record map iota. Once their splitting isomorphisms read
that actual map and action, faithful flatness proves the equalizer over F. -/
theorem equalizer_of_split_product [Module.FaithfullyFlat F K]
    (eA : (K ⊗[F] A) ≃ₐ[K] (J → K))
    (eB : (K ⊗[F] B) ≃ₐ[K] (I → K))
    (p : I → J) (hsurj : Function.Surjective p)
    (constant : ∀ (g : G) (i : I), p (g • i) = p i)
    (fibre : ∀ i j, p i = p j → ∃ g : G, g • i = j)
    (readι : ∀ a i, eB (ι.toLinearMap.lTensor K a) i = eA a (p i))
    (readσ : ∀ g z i, eB (((σ g).toLinearMap.lTensor K) z) i = eB z (g • i)) :
    Function.Exact ι.toLinearMap (defect σ) := by
  apply Module.FaithfullyFlat.lTensor_reflects_exact F K
  intro z
  change (defect σ).lTensor K z = 0 ↔ ∃ a, ι.toLinearMap.lTensor K a = z
  rw [tensor_zero_iff_fixed σ]
  constructor
  · intro hz
    have hF (g : G) (i : I) : eB z (g • i) = eB z i :=
      (readσ g z i).symm.trans (congrArg (fun v => eB v i) (hz g))
    obtain ⟨f,hf,-⟩ :=
      (OriginalR8FirstSlotSplitEqualizer318.image_eq_fixed p hsurj constant fibre (eB z)).mp hF
    refine ⟨eA.symm f,eB.injective ?_⟩
    funext i
    rw [readι,AlgEquiv.apply_symm_apply]
    exact congrFun hf i
  · rintro ⟨a,rfl⟩ g
    apply eB.injective
    funext i
    rw [readσ,readι,readι,constant]

/-- Ring-element form of the genuine represented first-slot equalizer. -/
theorem fixed_iff_in_image [Module.FaithfullyFlat F K]
    (eA : (K ⊗[F] A) ≃ₐ[K] (J → K))
    (eB : (K ⊗[F] B) ≃ₐ[K] (I → K))
    (p : I → J) (hsurj : Function.Surjective p)
    (constant : ∀ (g : G) (i : I), p (g • i) = p i)
    (fibre : ∀ i j, p i = p j → ∃ g : G, g • i = j)
    (readι : ∀ a i, eB (ι.toLinearMap.lTensor K a) i = eA a (p i))
    (readσ : ∀ g z i, eB (((σ g).toLinearMap.lTensor K) z) i = eB z (g • i))
    (b : B) : (∀ g : G, σ g b = b) ↔ ∃ a : A, ι a = b := by
  have h := equalizer_of_split_product ι σ eA eB p hsurj constant fibre readι readσ b
  change defect σ b = 0 ↔ ∃ a : A, ι a = b at h
  refine (?_ : (∀ g : G, σ g b = b) ↔ defect σ b = 0).trans h
  constructor
  · intro hb
    funext g
    change σ g b - b = 0
    exact sub_eq_zero.mpr (hb g)
  · intro hh g
    exact sub_eq_zero.mp (congrFun hh g)

end OriginalR8RepresentedFirstSlotEqualizer318
#print axioms OriginalR8RepresentedFirstSlotEqualizer318.equalizer_of_split_product
#print axioms OriginalR8RepresentedFirstSlotEqualizer318.fixed_iff_in_image
