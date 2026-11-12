module
public import CubicWeierstrassPolynomial318
public import SourceCharacterFields318
public import FourRootOrder318
public import TensorFractionField318
public section
noncomputable section
namespace CubicCharacterFraction318
open scoped TensorProduct
open Polynomial QuadraticPresentation318 SourceTwistArithmetic318
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev R:=ℚ[X]
abbrev K:=RatFunc ℚ
abbrev Order (i:Fin 4):=RootRing (CubicWeierstrassPolynomial318.radicand i)
abbrev Field (i:Fin 4):=SourceCharacterFields318.field units i
local instance orderFree (i:Fin 4):Module.Free R (Order i):=FourRootOrder318.root_free _

lemma parameter_eq (i:Fin 4):algebraMap R K (CubicWeierstrassPolynomial318.radicand i)=
    CharacterRoot318.radicand (SourceKummerField318.parameter units) (SourceCharacterFields318.complement i):=by
  rw [SourceCharacterFields318.radicand_cubic,SourceCharacterFields318.fixed_twist_product]
  rfl

/-- The actual generic fiber of the entire cubic order is the actual
specified character subfield of the original degree-sixteen contact field. -/
@[expose] def genericFiber (i:Fin 4):K⊗[R]Order i≃ₐ[K]Field i:=
  (((ContactGenericFiber318.rootBaseChange (S:=K) (CubicWeierstrassPolynomial318.radicand i)).trans
    (ContactGenericFiber318.rootParameterEquiv (parameter_eq i))).trans
      (presentationEquiv (CharacterRoot318.radicand (SourceKummerField318.parameter units)
        (SourceCharacterFields318.complement i))).symm).trans
    (CharacterQuadraticField318.equiv _ _)

@[expose] def embedding (i:Fin 4):Order i→+*Field i:=
  (genericFiber i).toRingHom.comp
    (Algebra.TensorProduct.includeRight : Order i→ₐ[R]K⊗[R]Order i).toRingHom

theorem embedding_root (i:Fin 4):
    (embedding i (AdjoinRoot.root (polynomial (CubicWeierstrassPolynomial318.radicand i))) :
      KummerTensorField318.Raw (SourceKummerField318.parameter units))=
    CharacterRoot318.root (SourceKummerField318.parameter units) (SourceCharacterFields318.complement i):=by
  let b:=CharacterRoot318.radicand (SourceKummerField318.parameter units) (SourceCharacterFields318.complement i)
  have hb:(presentationEquiv b).symm (AdjoinRoot.root (polynomial b))=QuadraticAlgebra.omega:=by
    apply (presentationEquiv b).injective
    simp
  change (((genericFiber i) (1⊗ₜ[R]AdjoinRoot.root
    (polynomial (CubicWeierstrassPolynomial318.radicand i)))) :
      KummerTensorField318.Raw (SourceKummerField318.parameter units))=_
  simp only [genericFiber,AlgEquiv.trans_apply,ContactGenericFiber318.rootBaseChange_generator,
    ContactGenericFiber318.rootParameterEquiv_generator]
  rw [hb]
  change CharacterQuadraticField318.lift (SourceKummerField318.parameter units)
    (SourceCharacterFields318.complement i) QuadraticAlgebra.omega=_
  simp [CharacterQuadraticField318.lift,QuadraticAlgebra.lift_apply_apply,QuadraticAlgebra.omega]

theorem embedding_injective (i:Fin 4):Function.Injective (embedding i):=by
  exact (genericFiber i).injective.comp
    (Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective R K))

local instance orderDomain (i:Fin 4):IsDomain (Order i):=(embedding_injective i).isDomain
local instance orderAlgebra (i:Fin 4):Algebra (Order i) (Field i):=(embedding i).toAlgebra

@[expose] def genericEquiv (i:Fin 4):Order i⊗[R]K≃ₐ[Order i]Field i:=
  { (Algebra.TensorProduct.comm R (Order i) K).toRingEquiv.trans (genericFiber i).toRingEquiv with
    commutes':=by intro x;rfl }

theorem actual_fractionField (i:Fin 4):IsFractionRing (Order i) (Field i):=
  TensorFractionField318.fractionRing (genericEquiv i)

theorem embedding_on_polynomial (i:Fin 4) (p:R):
    embedding i (algebraMap R (Order i) p)=algebraMap K (Field i) (algebraMap R K p):=by
  unfold embedding
  simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,AlgHom.commutes]
  rw [IsScalarTower.algebraMap_apply R K (K⊗[R]Order i)]
  exact (genericFiber i).commutes _
end CubicCharacterFraction318
