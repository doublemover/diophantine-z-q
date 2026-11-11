module
public import FourRootActualFractionField318
public import FourRootInertiaLabelCardinality318
public import ActualKummerGalois318
public section
noncomputable section
namespace FourRootActualOrderAutomorphisms318
open FourRootActualGenericField318 FourRootAffineTensorPresentation318
open FourRootActualFractionField318 FourBinaryCharacters318
open scoped TensorProduct
variable (b:Fin 4→ℂ) (hb:Function.Injective b)
local instance independentFact:Fact (QuadraticTower318.Independent (parameter b)):=⟨independent b hb⟩
local instance affineDomain:IsDomain (A b):=affine_domain b hb
local instance polyAlgebra:Algebra P (A b):=
  (Polynomial.aeval (FourRootAffineCoordinateRing318.coordinate b none)).toAlgebra
local instance rawAlgebra:Algebra (A b) (L b):=(affineEmbedding b).toAlgebra
local instance rawFraction:IsFractionRing (A b) (L b):=actual_fractionField b hb

/-- Same literal root action, now with its ORIGINAL unshifted polynomial
base action retained rather than only its complex scalar restriction. -/
@[expose] def polynomialSign (g:FourBinaryCharacters318.Group):A b≃ₐ[P]A b:=
  (polynomialEquivalence b).trans
    ((FourRootOrderSigns318.signEquiv (radicand b) (signPattern g)).trans
      (polynomialEquivalence b).symm)
lemma polynomialSign_apply (g:FourBinaryCharacters318.Group) (x:A b):
    polynomialSign b g x=FourRootCoordinateRingSigns318.finiteEquiv b g x:=by
  apply (equivalence b).injective
  change equivalence b ((polynomialEquivalence b).symm
    (FourRootOrderSigns318.signEquiv (radicand b) (signPattern g) (equivalence b x)))=_
  rw [show equivalence b=(polynomialEquivalence b : A b→TensorRing b) from rfl,
    AlgEquiv.apply_symm_apply]
  exact (FourRootActualGenericSigns318.tensor_equivariant b g x).symm

@[expose] def fieldEquivalence:K⊗[P]A b≃ₐ[K]L b:=
  (Algebra.TensorProduct.congr (AlgEquiv.refl:K≃ₐ[K]K) (polynomialEquivalence b)).trans
    (genericFiber b)
lemma fieldEquivalence_embedding (x:A b):
    fieldEquivalence b (1⊗ₜ[P]x)=affineEmbedding b x:=by
  change genericFiber b ((Algebra.TensorProduct.congr (AlgEquiv.refl:K≃ₐ[K]K)
    (polynomialEquivalence b)) (1⊗ₜ[P]x))=_
  rw [Algebra.TensorProduct.congr_apply,Algebra.TensorProduct.map_tmul]
  rfl

/-- Every actual polynomial-order automorphism extends to the specified
whole generic field by its genuine coefficient base change. -/
@[expose] def extend (e:A b≃ₐ[P]A b):L b≃ₐ[K]L b:=
  (fieldEquivalence b).symm.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl:K≃ₐ[K]K) e).trans (fieldEquivalence b))
lemma extend_embedding (e:A b≃ₐ[P]A b) (x:A b):
    extend b e (affineEmbedding b x)=affineEmbedding b (e x):=by
  rw [←fieldEquivalence_embedding,←fieldEquivalence_embedding]
  change fieldEquivalence b ((Algebra.TensorProduct.congr (AlgEquiv.refl:K≃ₐ[K]K) e)
    ((fieldEquivalence b).symm (fieldEquivalence b (1⊗ₜ[P]x))))=_
  rw [AlgEquiv.symm_apply_apply,Algebra.TensorProduct.congr_apply,Algebra.TensorProduct.map_tmul]
  rfl
lemma extend_sign (g:FourBinaryCharacters318.Group):
    extend b (polynomialSign b g)=FourRootActualGenericSigns318.genericAutomorphism b g:=by
  have he:(extend b (polynomialSign b g)).toRingHom=
      (FourRootActualGenericSigns318.genericAutomorphism b g).toRingHom:=by
    apply IsFractionRing.ringHom_ext (A:=A b)
    intro x
    change extend b (polynomialSign b g) (affineEmbedding b x)=
      FourRootActualGenericSigns318.genericAutomorphism b g (affineEmbedding b x)
    rw [extend_embedding,polynomialSign_apply]
    exact FourRootActualGenericSigns318.affineEmbedding_equivariant b g x
  ext x
  exact RingHom.congr_fun he x
lemma sign_injective:Function.Injective (polynomialSign b):=by
  intro g h he
  have hh:=congrArg (extend b) he
  rw [extend_sign,extend_sign] at hh
  apply FourRootInertiaLabelCardinality318.signEquivalence.injective
  exact FourRootAutomorphisms318.signEquiv_injective (parameter b) hh

/-- No further polynomial-order automorphisms are omitted: all extend
into the actual degree-sixteen Kummer field and hence are original signs. -/
theorem sign_surjective:Function.Surjective (polynomialSign b):=by
  intro e
  obtain ⟨s,hs⟩:=FourRootGalois318.signAutomorphism_surjective (parameter b)
    ((AlgEquiv.autCongr (KummerTensorField318.rawEquiv (parameter b))) (extend b e))
  have hf:FourRootAutomorphisms318.signEquiv (parameter b) s=extend b e:=
    (AlgEquiv.autCongr (KummerTensorField318.rawEquiv (parameter b))).injective hs
  let g:=FourRootInertiaLabelCardinality318.signEquivalence.symm s
  have hg:signPattern g=s:=FourRootInertiaLabelCardinality318.signEquivalence.apply_symm_apply s
  refine ⟨g,?_⟩
  ext x
  apply affineEmbedding_injective b
  have hx:=congrArg (fun f:L b≃ₐ[K]L b=>f (affineEmbedding b x)) hf
  rw [extend_embedding] at hx
  rw [polynomialSign_apply,FourRootActualGenericSigns318.affineEmbedding_equivariant]
  simpa only [FourRootActualGenericSigns318.genericAutomorphism,hg] using hx

@[expose] def signEquivalence:FourBinaryCharacters318.Group≃(A b≃ₐ[P]A b):=
  Equiv.ofBijective (polynomialSign b) ⟨sign_injective b hb,sign_surjective b hb⟩
theorem automorphism_card:Nat.card (A b≃ₐ[P]A b)=16:=by
  rw [←Nat.card_congr (signEquivalence b hb),
    Nat.card_congr FourRootInertiaLabelCardinality318.signEquivalence]
  simp
end FourRootActualOrderAutomorphisms318
