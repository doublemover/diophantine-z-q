module
public import FourRootAffineTensorPresentation318
public import KummerTensorField318
public section
noncomputable section
namespace FourRootActualGenericField318
open Polynomial FourRootOrder318 FourRootAffineTensorPresentation318
open scoped TensorProduct
variable (b:Fin 4→ℂ) (hb:Function.Injective b)
abbrev K:=RatFunc ℂ
@[expose] def parameter (k:Fin 4):K:=algebraMap P K (radicand b k)

/-- Every nonempty product is nonsquare in the ACTUAL complex rational
function field; distinct marked branches produce the independence. -/
include hb in
theorem product_nonsquare (s:Finset (Fin 4)) (hs:s.Nonempty):
    ¬IsSquare (∏k∈s,parameter b k):=by
  have h:=LinearContactSquareclass318.twisted_product_nonsquare b hb s hs (1:ℂ) one_ne_zero
  simpa only [Polynomial.C_1,one_mul,map_prod,parameter,radicand] using h

include hb in
theorem independent:QuadraticTower318.Independent (parameter b):=
  SourceKummerField318.independent_of_products _ (product_nonsquare b hb)
local instance independentFact:Fact (QuadraticTower318.Independent (parameter b)):=⟨independent b hb⟩

/-- No field component is selected: the entire fourfold generic tensor
algebra is a field, of exact degree16 over the original t-coordinate. -/
theorem actual_field:IsField (KummerTensorField318.Raw (parameter b)):=
  KummerTensorField318.actual_field _
theorem actual_degree:Module.finrank K (KummerTensorField318.Raw (parameter b))=16:=
  KummerTensorField318.actual_degree _

@[expose] def genericFiber:
    K⊗[P]TensorRing b≃ₐ[K]KummerTensorField318.Raw (parameter b):=
  FourRootOrder318.baseChange (radicand b) K

@[expose] def embedding:TensorRing b→+*KummerTensorField318.Raw (parameter b):=
  (genericFiber b).toRingHom.comp
    (Algebra.TensorProduct.includeRight:TensorRing b→ₐ[P]K⊗[P]TensorRing b).toRingHom

theorem embedding_injective:Function.Injective (embedding b):=by
  letI:Module.Free P (TensorRing b):=(FourRootOrder318.finite_free (radicand b)).2
  exact (genericFiber b).injective.comp
    (Algebra.TensorProduct.includeRight_injective (R:=P) (A:=K) (B:=TensorRing b)
      (IsFractionRing.injective P K))

include hb in
theorem tensor_domain:IsDomain (TensorRing b):=by
  letI:Field (KummerTensorField318.Raw (parameter b)):=(actual_field b hb).toField
  exact Function.Injective.isDomain (embedding b) (embedding_injective b)

/-- This is the independently defined finite polynomial quotient used in
the analytic and scheme charts, not a substituted generic field carrier. -/
include hb in
theorem affine_domain:IsDomain (FourRootAffineCoordinateRing318.Ring b):=by
  letI:IsDomain (TensorRing b):=tensor_domain b hb
  exact Function.Injective.isDomain (equivalence b) (equivalence b).injective

@[expose] def affineEmbedding:FourRootAffineCoordinateRing318.Ring b→+*
    KummerTensorField318.Raw (parameter b):=
  (embedding b).comp (equivalence b).toRingHom

theorem affineEmbedding_injective:Function.Injective (affineEmbedding b):=
  (embedding_injective b).comp (equivalence b).injective
end FourRootActualGenericField318
