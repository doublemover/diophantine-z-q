module
public import FourRootActualCharacterFields318
public import TensorFractionField318
public section
noncomputable section
namespace FourRootActualFractionField318
open scoped TensorProduct
open FourRootActualGenericField318 FourRootAffineTensorPresentation318
variable (b:Fin 4→ℂ) (hb:Function.Injective b)
abbrev A:=FourRootAffineCoordinateRing318.Ring b
abbrev L:=KummerTensorField318.Raw (parameter b)
local instance independentFact:Fact (QuadraticTower318.Independent (parameter b)):=⟨independent b hb⟩
local instance affineDomain:IsDomain (A b):=affine_domain b hb
local instance polyAlgebra:Algebra P (A b):=
  (Polynomial.aeval (FourRootAffineCoordinateRing318.coordinate b none)).toAlgebra
local instance fieldAlgebra:Algebra (A b) (L b):=(affineEmbedding b).toAlgebra

@[expose] def polynomialEquivalence:A b≃ₐ[P]TensorRing b:=
  { (equivalence b).toRingEquiv with commutes':=equivalence_base b }
local instance affineFree:Module.Free P (A b):=by
  letI:Module.Free P (TensorRing b):=(FourRootOrder318.finite_free (radicand b)).2
  exact Module.Free.of_equiv (polynomialEquivalence b).symm.toLinearEquiv

/-- The original coefficient-preserving tensor equivalence exhibits the
specified actual field embedding as the entire generic localization. -/
@[expose] def genericEquivalence:A b⊗[P]K≃ₐ[A b]L b:=
  { ((Algebra.TensorProduct.congr (polynomialEquivalence b)
       (AlgEquiv.refl : K≃ₐ[P]K)).toRingEquiv.trans
       ((Algebra.TensorProduct.comm P (TensorRing b) K).toRingEquiv.trans
         (genericFiber b).toRingEquiv)) with
    commutes':=by
      intro x
      change genericFiber b (1⊗ₜ[P](equivalence b x))=
        affineEmbedding b x
      rfl }

/-- The field used for the actual character fixed fields is genuinely the
fraction field of the SAME whole finite coordinate ring. -/
theorem actual_fractionField:IsFractionRing (A b) (L b):=
  TensorFractionField318.fractionRing (genericEquivalence b)

lemma actual_embedding (x:A b):algebraMap (A b) (L b) x=affineEmbedding b x:=rfl
lemma embedding_on_polynomial (p:P):
    affineEmbedding b (algebraMap P (A b) p)=
      algebraMap K (L b) (algebraMap P K p):=by
  change embedding b (equivalence b (algebraMap P (A b) p))=_
  rw [equivalence_base]
  unfold embedding
  simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,AlgHom.commutes]
  rw [IsScalarTower.algebraMap_apply P K (K⊗[P]TensorRing b)]
  exact (genericFiber b).commutes _
end FourRootActualFractionField318
