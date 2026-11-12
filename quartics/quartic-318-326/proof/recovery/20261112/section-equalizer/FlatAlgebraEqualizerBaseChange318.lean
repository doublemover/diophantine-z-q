module
public import TwoOpenSectionRingEqualizer318
public import TensorAlgebraBaseChange318
public section
noncomputable section
namespace FlatAlgebraEqualizerBaseChange318
open scoped TensorProduct
universe u
variable {R C D : Type u} [CommRing R] [CommRing C] [CommRing D]
  [Algebra R C] [Algebra R D]
variable (A : Type u) [CommRing A] [Algebra R A]
variable (f g : C →ₐ[R] D)
open TensorAlgebraBaseChange318
abbrev original := AlgHom.equalizer f g
abbrev pulled := AlgHom.equalizer (map A f) (map A g)
lemma compatibility (z : A ⊗[R] original f g) :
    map A f (map A (original f g).val z)=map A g (map A (original f g).val z) := by
  have h : f.comp (original f g).val=g.comp (original f g).val := by
    ext x
    exact x.property
  rw [←AlgHom.comp_apply,←AlgHom.comp_apply,←composition,←composition,h]
/-- The full algebra equalizer comparison is the ACTUAL tensor of its
inclusion, with no module-carrier identification hidden. -/
def comparison : A ⊗[R] original f g →ₐ[A] pulled A f g :=
  (map A (original f g).val).codRestrict _ (compatibility A f g)
@[simp] lemma value (z : A ⊗[R] original f g) :
    (comparison A f g z).val=map A (original f g).val z := rfl
lemma difference (z : A ⊗[R] C) :
    (f.toLinearMap-g.toLinearMap).lTensor A z=map A f z-map A g z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero,sub_self]
  | tmul a c => exact TensorProduct.tmul_sub _ _ _
  | add x y hx hy => simp only [map_add,hx,hy];abel
variable [hflat : Module.Flat R A]
include hflat in
lemma injective : Function.Injective (comparison A f g) := by
  intro x y h
  exact TensorAlgebraBaseChange318.injective A (original f g).val Subtype.val_injective
    (congrArg Subtype.val h)
include hflat in
lemma surjective : Function.Surjective (comparison A f g) := by
  have he : Function.Exact (original f g).val.toLinearMap (f.toLinearMap-g.toLinearMap) := by
    rw [LinearMap.exact_iff]
    ext x
    change f x-g x=0 ↔ ∃ y : original f g, y.val=x
    constructor
    · intro h
      exact ⟨⟨x,sub_eq_zero.mp h⟩,rfl⟩
    · rintro ⟨y,rfl⟩
      exact sub_eq_zero.mpr y.property
  have ht := Module.Flat.lTensor_exact (M:=A) he
  intro z
  have hz : z.val∈LinearMap.ker ((f.toLinearMap-g.toLinearMap).lTensor A) := by
    change (f.toLinearMap-g.toLinearMap).lTensor A z.val=0
    rw [difference,z.property,sub_self]
  rw [LinearMap.exact_iff.mp ht] at hz
  obtain ⟨w,hw⟩ := hz
  refine ⟨w,Subtype.ext ?_⟩
  exact (map_apply_lTensor A (original f g).val w).trans hw
/-- Flatness, rather than a splitting or a projective H0 assumption,
produces the full multiplicative basechange isomorphism. -/
def equivalence : A ⊗[R] original f g ≃ₐ[A] pulled A f g :=
  AlgEquiv.ofBijective (comparison A f g) ⟨injective A f g,surjective A f g⟩
@[simp] lemma tmul (a : A) (z : original f g) :
    (equivalence A f g (a ⊗ₜ[R] z)).val=a ⊗ₜ[R] z.val := rfl
end FlatAlgebraEqualizerBaseChange318
