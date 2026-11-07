module
public import AffineHeightOneStalk318
public import NormalizedContactOrder318
public section
noncomputable section
namespace HeightOneContact318
set_option maxHeartbeats 700000
open PowerSeries AffineHeightOneStalk318
open scoped TensorProduct
variable {A R:Type*} [CommRing A] [CommRing R] [Algebra A R]
  [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]

/-- The actual base algebra and actual Spec stalk supply the coefficient map;
the target is the constructed complete local DVR of that codimension-one point. -/
theorem source_formal_map (x:Point R) (u:(Stalk R x)ˣ) (pi:Stalk R x) (m:ℕ)
    (hp:Irreducible pi) (hm:0<m) :
    ∃e:A⟦X⟧→+*CompletedStalk R x,
      e X=algebraMap (Stalk R x) (CompletedStalk R x) ((u:Stalk R x)*pi^(2*m)) ∧
      ∀a:A,e (C a)=algebraMap (Stalk R x) (CompletedStalk R x)
        (algebraMap R (Stalk R x) (algebraMap A R a)) :=
  ActualDVRCompletion318.completed_contact_map (Stalk R x)
    ((algebraMap R (Stalk R x)).comp (algebraMap A R)) u pi m hp hm

/-- Actual finite etale normalization at the height-one point, with its local
DVR structure derived from the normal affine model rather than supplied. -/
theorem source_local_normalization (x:Point R) (u:(Stalk R x)ˣ) (pi:Stalk R x) (m:ℕ)
    (h2:IsUnit (2:Stalk R x)) (hp:pi≠0) :
    let B:=Stalk R x
    let K:=FractionRing B
    letI:=NormalizedContactOrder318.orderAlgebra (K:=K) u pi m
    IsIntegralClosure (EvenContactEtale318.RootRing u)
      (QuadraticPresentation318.RootRing ((u:B)*pi^(2*m)))
      (EvenContactEtale318.RootRing u ⊗[B] K) ∧
    Algebra.Etale B (EvenContactEtale318.RootRing u) ∧
    Module.Finite B (EvenContactEtale318.RootRing u) ∧
    Function.Injective (NormalizedContactOrder318.orderToGeneric (K:=K) u pi m) ∧
    Nonempty (K ⊗[B] QuadraticPresentation318.RootRing ((u:B)*pi^(2*m)) ≃ₐ[B]
      EvenContactEtale318.RootRing u ⊗[B] K) :=
  NormalizedContactOrder318.normalized_even_contact u pi m h2 hp

end HeightOneContact318
