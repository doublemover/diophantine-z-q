module
public import ActualTwoDescentOriginalGlobalRootAffineFrames318
public section
noncomputable section
namespace ActualTwoDescentLocalizedInclusionIsomorphism318
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra ChangeOfRings
open ActualTwoDescentLocalizedIdealTensorEquivalence318
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (I : Ideal R)

include M in
/-- The exact scalar-extension map of the literal ideal inclusion is
invertible when its actual extended ideal is top. No arbitrary frame map. -/
lemma actual_extended_inclusion_isIso (hI : I.map (algebraMap R S)=⊤) :
    IsIso ((ModuleCat.extendScalars (algebraMap R S)).map (ModuleCat.ofHom I.subtype)) := by
  let eI := (ScalarExtensionTensor318.tensorEquiv (T:=S) (ModuleCat.of R I)).trans
    (localizedIdealTensorEquiv S M I)
  let eR := ScalarExtensionTensor318.tensorEquiv (T:=S) (ModuleCat.of R R)
  let f := (ModuleCat.extendScalars (algebraMap R S)).map (ModuleCat.ofHom I.subtype)
  let v := fun z => (TensorProduct.rid R S) (eR z)
  have hv : Function.Bijective v := (TensorProduct.rid R S).bijective.comp eR.bijective
  have he : ∀ z, v (f z)=(eI z : S) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | zero => simp [v,f,eI,eR]
    | tmul s x =>
      change (TensorProduct.rid R S) (s ⊗ₜ[R] (x:R))=
        (localizedIdealTensorEquiv S M I (s ⊗ₜ[R] x) : S)
      rw [TensorProduct.rid_tmul,actual_localized_ideal_tensor_value,Algebra.smul_def,mul_comm]
    | add z w hz hw =>
      change (TensorProduct.rid R S) (eR (f (z+w)))=(eI (z+w):S)
      simpa only [v,map_add,Submodule.coe_add] using congrArg₂ (·+·) hz hw
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · intro x y h
    apply eI.injective
    apply Subtype.ext
    exact (he x).symm.trans ((congrArg v h).trans (he y))
  · intro y
    have hy : v y ∈ I.map (algebraMap R S) := by rw [hI]; trivial
    obtain ⟨x,hx⟩ := eI.surjective ⟨v y,hy⟩
    refine ⟨x,hv.injective ?_⟩
    rw [he,hx]
end ActualTwoDescentLocalizedInclusionIsomorphism318
