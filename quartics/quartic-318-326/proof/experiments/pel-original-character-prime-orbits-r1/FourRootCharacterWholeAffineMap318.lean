module
public import FourRootCharacterPolynomialOrder318
public import FourRootActualOrderGalois318
public section
noncomputable section
namespace FourRootCharacterWholeAffineMap318
open Polynomial
open FourRootAffineTensorPresentation318 FourRootActualGenericField318
open FourRootActualFractionField318 FourRootCharacterPolynomialOrder318
variable (b:Fin 4→ℂ) (hb:Function.Injective b) (s:Finset (Fin 4)) (hs:s.Nonempty)
local instance independentFact:Fact (QuadraticTower318.Independent (parameter b)):=⟨independent b hb⟩
local instance affineDomain:IsDomain (A b):=affine_domain b hb
local instance polyAlgebra:Algebra P (A b):=
  (Polynomial.aeval (FourRootAffineCoordinateRing318.coordinate b none)).toAlgebra
local instance rawAlgebra:Algebra (A b) (L b):=(affineEmbedding b).toAlgebra
local instance baseAlgebra:Algebra P (L b):=
  ((algebraMap K (L b)).comp (algebraMap P K)).toAlgebra
local instance affineTower:IsScalarTower P (A b) (L b):=
  IsScalarTower.of_algebraMap_eq (fun p=>(FourRootActualFractionField318.embedding_on_polynomial b p).symm)
local instance affineClosure:IsIntegralClosure (A b) P (L b):=
  FourRootActualOrderGalois318.integralClosure b hb
local instance orderFinite:Module.Finite P (Order b s):=(finite_free b s).1

@[expose] def toRaw:Order b s→+*L b:=
  (Field b hb s hs).subtype.comp (embedding b hb s hs)
lemma toRaw_on_polynomial (p:P):
    toRaw b hb s hs (algebraMap P (Order b s) p)=algebraMap P (L b) p:=by
  exact congrArg (fun x:Field b hb s hs=>(x:L b)) (embedding_on_polynomial b hb s hs p)
local instance characterAlgebra:Algebra (Order b s) (L b):=(toRaw b hb s hs).toAlgebra
local instance characterTower:IsScalarTower P (Order b s) (L b):=
  IsScalarTower.of_algebraMap_eq (fun p=>(toRaw_on_polynomial b hb s hs p).symm)

/-- Integral closure produces the actual whole affine character map. Its
regularity holds at every finite branch point, not just the generic open. -/
@[expose] def toSource:Order b s→ₐ[P]A b:=IsIntegralClosure.lift P (A b) (L b)
lemma embedding_square (x:Order b s):
    affineEmbedding b (toSource b hb s hs x)=toRaw b hb s hs x:=
  IsIntegralClosure.algebraMap_lift P (A b) (L b) x

/-- The produced coordinate is precisely the product of the original
root coordinates, with no constant, sign, or generic denominator ambiguity. -/
lemma on_root:toSource b hb s hs
    (AdjoinRoot.root (QuadraticPresentation318.polynomial (radicand b s)))=
      FourRootActualCharacterFields318.monomial b s:=by
  apply affineEmbedding_injective b
  rw [embedding_square,FourRootActualCharacterFields318.affine_monomial]
  exact embedding_root b hb s hs

lemma injective:Function.Injective (toSource b hb s hs):=by
  intro x y h
  apply embedding_injective b hb s hs
  apply Subtype.ext
  exact (embedding_square b hb s hs x).symm.trans
    ((congrArg (affineEmbedding b) h).trans (embedding_square b hb s hs y))

local instance sourceCharacterAlgebra:Algebra (Order b s) (A b):=(toSource b hb s hs).toAlgebra
local instance sourceCharacterTower:IsScalarTower P (Order b s) (A b):=
  IsScalarTower.of_algebraMap_eq (fun p=>(toSource b hb s hs).commutes p |>.symm)

theorem finite:(toSource b hb s hs).toRingHom.Finite:=by
  letI:Module.Finite P (A b):=(FourRootActualOrderGalois318.finite_free b).1
  exact Module.Finite.of_restrictScalars_finite P (Order b s) (A b)

/-- The same relative degree eight belongs to the specified fraction
extension of this actual finite ring map. The embedding square above
identifies the map, before the degree is consumed. -/
theorem relative_degree:Module.finrank (Field b hb s hs) (L b)=8:=
  FourRootActualCharacterFields318.relative_degree_eight b hb s hs
end FourRootCharacterWholeAffineMap318
