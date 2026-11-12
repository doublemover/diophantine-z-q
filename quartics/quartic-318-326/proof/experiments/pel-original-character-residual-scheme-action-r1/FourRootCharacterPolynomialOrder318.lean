module
public import FourRootActualCharacterFields318
public import ContactGenericFiber318
public import TensorFractionField318
public section
noncomputable section
namespace FourRootCharacterPolynomialOrder318
open scoped TensorProduct
open Polynomial QuadraticPresentation318
open FourRootAffineTensorPresentation318 FourRootActualGenericField318
variable (b:Fin 4→ℂ) (hb:Function.Injective b) (s:Finset (Fin 4)) (hs:s.Nonempty)
local instance independentFact:Fact (QuadraticTower318.Independent (parameter b)):=⟨independent b hb⟩
local instance nonsquareFact:Fact (¬IsSquare (CharacterRoot318.radicand (parameter b) s)):=
  ⟨product_nonsquare b hb s hs⟩

/-- The whole polynomial order of the literal character monomial, over
same unshifted complex t-coordinate. No root or field component is selected. -/
@[expose] def radicand:P:=∏k∈s,FourRootAffineTensorPresentation318.radicand b k
abbrev Order:=RootRing (radicand b s)
abbrev Field:=FourRootActualCharacterFields318.field b hb s hs
local instance orderFree:Module.Free P (Order b s):=FourRootOrder318.root_free _

lemma parameter_eq:algebraMap P K (radicand b s)=
    CharacterRoot318.radicand (parameter b) s:=by
  simp only [radicand,CharacterRoot318.radicand,map_prod,parameter]

/-- Base changing the entire polynomial order gives the specified actual
intermediate field, rather than an isomorphic but unmarked quadratic field. -/
@[expose] def genericFiber:K⊗[P]Order b s≃ₐ[K]Field b hb s hs:=
  (((ContactGenericFiber318.rootBaseChange (S:=K) (radicand b s)).trans
    (ContactGenericFiber318.rootParameterEquiv (parameter_eq b s))).trans
      (presentationEquiv (CharacterRoot318.radicand (parameter b) s)).symm).trans
    (CharacterQuadraticField318.equiv _ _)

@[expose] def embedding:Order b s→+*Field b hb s hs:=
  (genericFiber b hb s hs).toRingHom.comp
    (Algebra.TensorProduct.includeRight:Order b s→ₐ[P]K⊗[P]Order b s).toRingHom

lemma embedding_root:
    (embedding b hb s hs (AdjoinRoot.root (polynomial (radicand b s))):
      KummerTensorField318.Raw (parameter b))=CharacterRoot318.root (parameter b) s:=by
  let c:=CharacterRoot318.radicand (parameter b) s
  have hc:(presentationEquiv c).symm (AdjoinRoot.root (polynomial c))=QuadraticAlgebra.omega:=by
    apply (presentationEquiv c).injective
    simp
  change ((genericFiber b hb s hs (1⊗ₜ[P]AdjoinRoot.root (polynomial (radicand b s)))):
    KummerTensorField318.Raw (parameter b))=_
  simp only [genericFiber,AlgEquiv.trans_apply,ContactGenericFiber318.rootBaseChange_generator,
    ContactGenericFiber318.rootParameterEquiv_generator]
  rw [hc]
  change CharacterQuadraticField318.lift (parameter b) s QuadraticAlgebra.omega=_
  simp [CharacterQuadraticField318.lift,QuadraticAlgebra.lift_apply_apply,QuadraticAlgebra.omega]

lemma embedding_injective:Function.Injective (embedding b hb s hs):=
  (genericFiber b hb s hs).injective.comp
    (Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective P K))
local instance orderAlgebra:Algebra (Order b s) (Field b hb s hs):=(embedding b hb s hs).toAlgebra

@[expose] def genericEquiv:Order b s⊗[P]K≃ₐ[Order b s]Field b hb s hs:=
  { (Algebra.TensorProduct.comm P (Order b s) K).toRingEquiv.trans
      (genericFiber b hb s hs).toRingEquiv with commutes':=by intro x;rfl }

theorem fractionField:IsFractionRing (Order b s) (Field b hb s hs):=by
  letI:IsDomain (Order b s):=Function.Injective.isDomain
    (embedding b hb s hs) (embedding_injective b hb s hs)
  exact TensorFractionField318.fractionRing (genericEquiv b hb s hs)

lemma embedding_on_polynomial (p:P):
    embedding b hb s hs (algebraMap P (Order b s) p)=
      algebraMap K (Field b hb s hs) (algebraMap P K p):=by
  unfold embedding
  simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,AlgHom.commutes]
  rw [IsScalarTower.algebraMap_apply P K (K⊗[P]Order b s)]
  exact (genericFiber b hb s hs).commutes _

theorem finite_free:Module.Finite P (Order b s)∧Module.Free P (Order b s):=
  ⟨FourRootOrder318.root_finite _,FourRootOrder318.root_free _⟩
theorem rank_two:Module.finrank P (Order b s)=2:=FourRootOrder318.root_rank _
end FourRootCharacterPolynomialOrder318
