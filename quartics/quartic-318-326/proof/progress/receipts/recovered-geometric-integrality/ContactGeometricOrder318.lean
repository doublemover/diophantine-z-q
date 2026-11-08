module
public import ContactKummerOrder318
public section
noncomputable section
namespace ContactGeometricOrder318
open Polynomial
open scoped TensorProduct
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (F:Type u) [Field F] [CharZero F] [Algebra ℚ F]
variable (c:Fin 4→ℚˣ)
@[expose] def contacts (i:Fin 4) : F:=algebraMap ℚ F (LinearContactSquareclass318.contacts i)
lemma contacts_injective : Function.Injective (contacts F):=
  (algebraMap ℚ F).injective.comp LinearContactSquareclass318.contacts_injective
@[expose] def coefficient (i:Fin 4) : F[X]:=
  C (algebraMap ℚ F (c i:ℚ))*(X-C (contacts F i))
@[expose] def parameter (i:Fin 4) : RatFunc F:=
  algebraMap F[X] (RatFunc F) (coefficient F c i)

/-- Distinct linear branch valuations survive every characteristic-zero
coefficient field, regardless of whether the rational twists become squares. -/
lemma product_nonsquare (s:Finset (Fin 4)) (hs:s.Nonempty) :
    ¬IsSquare (∏i∈s,parameter F c i):=by
  have hp:(∏i∈s,parameter F c i)=algebraMap F[X] (RatFunc F)
      (C (∏i∈s,algebraMap ℚ F (c i:ℚ))*∏i∈s,(X-C (contacts F i))):=by
    simp only [parameter,coefficient,←map_prod,Finset.prod_mul_distrib]
  rw [hp]
  apply LinearContactSquareclass318.twisted_product_nonsquare (contacts F)
    (contacts_injective F) s hs
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  simpa only [map_zero] using (algebraMap ℚ F).injective.ne (c i).ne_zero

lemma independent : QuadraticTower318.Independent (parameter F c):=
  SourceKummerField318.independent_of_products _ (product_nonsquare F c)
local instance independentFact : Fact (QuadraticTower318.Independent (parameter F c)):=⟨independent F c⟩
lemma raw_field : IsField (KummerTensorField318.Raw (parameter F c)):=
  KummerTensorField318.actual_field _
lemma raw_degree : Module.finrank (RatFunc F) (KummerTensorField318.Raw (parameter F c))=16:=
  KummerTensorField318.actual_degree _

abbrev Order:=FourRootOrder318.Order (coefficient F c)
@[expose] def genericFiber :
    RatFunc F⊗[F[X]]Order F c≃ₐ[RatFunc F]KummerTensorField318.Raw (parameter F c):=
  FourRootOrder318.baseChange (coefficient F c) (RatFunc F)
@[expose] def embedding : Order F c→+*KummerTensorField318.Raw (parameter F c):=
  (genericFiber F c).toRingHom.comp
    (Algebra.TensorProduct.includeRight : Order F c→ₐ[F[X]]RatFunc F⊗[F[X]]Order F c).toRingHom
lemma embedding_injective : Function.Injective (embedding F c):=by
  letI:Module.Free F[X] (Order F c):=(FourRootOrder318.finite_free (coefficient F c)).2
  exact (genericFiber F c).injective.comp
    (Algebra.TensorProduct.includeRight_injective (R:=F[X]) (A:=RatFunc F) (B:=Order F c)
      (IsFractionRing.injective F[X] (RatFunc F)))
lemma order_domain : IsDomain (Order F c):=by
  letI:Field (KummerTensorField318.Raw (parameter F c)):=(raw_field F c).toField
  exact Function.Injective.isDomain (embedding F c) (embedding_injective F c)
end ContactGeometricOrder318
