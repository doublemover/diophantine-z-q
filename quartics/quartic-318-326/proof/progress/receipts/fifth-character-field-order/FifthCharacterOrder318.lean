module
public import FifthCharacterField318
public import SourceCharacterFields318
public import FourRootOrder318
public import TensorFractionField318
public section
noncomputable section
namespace FifthCharacterOrder318
open scoped TensorProduct
open Polynomial QuadraticPresentation318 SourceTwistArithmetic318
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev R:=ℚ[X]
abbrev K:=RatFunc ℚ
abbrev Order:=RootRing (FifthCharacterPolynomial318.quartic)
abbrev Field:=FifthCharacterField318.field
local instance orderFree:Module.Free R (Order):=FourRootOrder318.root_free _

lemma parameter_eq:algebraMap R K (FifthCharacterPolynomial318.quartic)=
    CharacterRoot318.radicand (SourceKummerField318.parameter units) (FifthCharacterField318.support):=by
  exact FifthCharacterField318.radicand_quartic.symm

/-- The actual generic fiber of the entire quartic order is the actual
specified character subfield of the original degree-sixteen contact field. -/
@[expose] def genericFiber:K⊗[R]Order≃ₐ[K]Field:=
  (((ContactGenericFiber318.rootBaseChange (S:=K) (FifthCharacterPolynomial318.quartic)).trans
    (ContactGenericFiber318.rootParameterEquiv (parameter_eq))).trans
      (presentationEquiv (CharacterRoot318.radicand (SourceKummerField318.parameter units)
        (FifthCharacterField318.support))).symm).trans
    (CharacterQuadraticField318.equiv _ _)

@[expose] def embedding:Order→+*Field:=
  (genericFiber).toRingHom.comp
    (Algebra.TensorProduct.includeRight : Order→ₐ[R]K⊗[R]Order).toRingHom

theorem embedding_root:
    (embedding (AdjoinRoot.root (polynomial (FifthCharacterPolynomial318.quartic))) :
      KummerTensorField318.Raw (SourceKummerField318.parameter units))=
    CharacterRoot318.root (SourceKummerField318.parameter units) (FifthCharacterField318.support):=by
  let b:=CharacterRoot318.radicand (SourceKummerField318.parameter units) (FifthCharacterField318.support)
  have hb:(presentationEquiv b).symm (AdjoinRoot.root (polynomial b))=QuadraticAlgebra.omega:=by
    apply (presentationEquiv b).injective
    simp
  change (((genericFiber) (1⊗ₜ[R]AdjoinRoot.root
    (polynomial (FifthCharacterPolynomial318.quartic)))) :
      KummerTensorField318.Raw (SourceKummerField318.parameter units))=_
  simp only [genericFiber,AlgEquiv.trans_apply,ContactGenericFiber318.rootBaseChange_generator,
    ContactGenericFiber318.rootParameterEquiv_generator]
  rw [hb]
  change CharacterQuadraticField318.lift (SourceKummerField318.parameter units)
    (FifthCharacterField318.support) QuadraticAlgebra.omega=_
  simp [CharacterQuadraticField318.lift,QuadraticAlgebra.lift_apply_apply,QuadraticAlgebra.omega]

theorem embedding_injective:Function.Injective (embedding):=by
  exact (genericFiber).injective.comp
    (Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective R K))

local instance orderDomain:IsDomain (Order):=(embedding_injective).isDomain
local instance orderAlgebra:Algebra (Order) (Field):=(embedding).toAlgebra

@[expose] def genericEquiv:Order⊗[R]K≃ₐ[Order]Field:=
  { (Algebra.TensorProduct.comm R (Order) K).toRingEquiv.trans (genericFiber).toRingEquiv with
    commutes':=by intro x;rfl }

theorem actual_fractionField:IsFractionRing (Order) (Field):=
  TensorFractionField318.fractionRing (genericEquiv)

theorem embedding_on_polynomial (p:R):
    embedding (algebraMap R (Order) p)=algebraMap K (Field) (algebraMap R K p):=by
  unfold embedding
  simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,AlgHom.commutes]
  rw [IsScalarTower.algebraMap_apply R K (K⊗[R]Order)]
  exact (genericFiber).commutes _
end FifthCharacterOrder318
