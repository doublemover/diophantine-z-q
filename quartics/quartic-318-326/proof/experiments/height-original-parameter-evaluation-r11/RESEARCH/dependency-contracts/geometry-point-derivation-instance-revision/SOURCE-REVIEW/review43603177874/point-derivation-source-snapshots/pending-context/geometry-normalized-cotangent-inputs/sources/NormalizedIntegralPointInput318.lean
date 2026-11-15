module
public import NormalizedChartFiniteType318
public import DVRNormalizedAllPlaceCharts318
public section
noncomputable section
namespace NormalizedIntegralPointInput318
open Polynomial
open scoped TensorProduct
variable (V : Type*) [CommRing V]

/-- The point's A-action on V, not an unrelated algebra action. -/
@[expose] def pointAlgebra {A : Type*} [CommRing A] [Algebra V A]
    (f : A →ₐ[V] V) : Algebra A V := f.toRingHom.toAlgebra

theorem point_tower {A : Type*} [CommRing A] [Algebra V A] (f : A →ₐ[V] V) :
    letI : Algebra A V := pointAlgebra V f
    IsScalarTower V A V := by
  letI : Algebra A V := pointAlgebra V f
  exact IsScalarTower.of_algHom f

/-- With finite type already proved for the actual order, both the true
cotangent pullback and its tensor square are finite. This says nothing about
regularity, a dualizing comparison or a generic evaluation functional. -/
theorem cotangent_finite {A : Type*} [CommRing A] [Algebra V A]
    [Algebra.FiniteType V A] (f : A →ₐ[V] V) :
    letI : Algebra A V := pointAlgebra V f
    Module.Finite V (V ⊗[A] KaehlerDifferential V A) ∧
      Module.Finite V ((V ⊗[A] KaehlerDifferential V A) ⊗[V]
        (V ⊗[A] KaehlerDifferential V A)) := by
  letI : Algebra A V := pointAlgebra V f
  constructor <;> infer_instance

theorem finite_chart_cotangent (d a : Fin 4 → V)
    (f : DVRNormalizedFiniteOrder318.Order V d a →ₐ[V] V) :
    letI : Algebra (DVRNormalizedFiniteOrder318.Order V d a) V := pointAlgebra V f
    Module.Finite V (V ⊗[DVRNormalizedFiniteOrder318.Order V d a]
      KaehlerDifferential V (DVRNormalizedFiniteOrder318.Order V d a)) := by
  letI : Algebra.FiniteType V (DVRNormalizedFiniteOrder318.Order V d a) :=
    NormalizedChartFiniteType318.finite_order V d a
  exact (cotangent_finite V f).1

theorem infinity_chart_cotangent (d a : Fin 4 → V)
    (f : DVRNormalizedInfinityOrder318.Order V d a →ₐ[V] V) :
    letI : Algebra (DVRNormalizedInfinityOrder318.Order V d a) V := pointAlgebra V f
    Module.Finite V (V ⊗[DVRNormalizedInfinityOrder318.Order V d a]
      KaehlerDifferential V (DVRNormalizedInfinityOrder318.Order V d a)) := by
  letI : Algebra.FiniteType V (DVRNormalizedInfinityOrder318.Order V d a) :=
    NormalizedChartFiniteType318.infinity_order V d a
  exact (cotangent_finite V f).1

variable [IsDomain V] [IsDiscreteValuationRing V]
  (K : Type*) [Field K] [Algebra V K] [IsFractionRing V K]

/-- Upgrade the existing ALL-place signed chart center to an actual V-algebra
point, keeping the same normalized twists, polynomial coordinate and every
signed root. No unit-2/good-prime or regular-model hypothesis is introduced. -/
theorem chart_center_alg (pi : V) (hp : Irreducible pi) (c : Fin 4 → Kˣ)
    (a : Fin 4 → V) (t : K) (y : Fin 4 → K)
    (hy : ∀ i,(y i)^2=(c i:K)*(t-algebraMap V K (a i))) :
    ∃ (u : Fin 4 → Vˣ) (e : Fin 4 → Fin 2) (s : Fin 4 → K),
      (∀ i,s i≠0) ∧
      (∀ i,(c i:K)=algebraMap V K ((u i:V)*pi^(e i:ℕ))*(s i)^2) ∧
      ((∃ (T : V) (f : DVRNormalizedFiniteOrder318.Order V
          (fun i => (u i:V)*pi^(e i:ℕ)) a →ₐ[V] V),
        algebraMap V K T=t ∧
        (∀ p : V[X], f (algebraMap V[X] (DVRNormalizedFiniteOrder318.Order V
          (fun i => (u i:V)*pi^(e i:ℕ)) a) p)=Polynomial.eval T p) ∧
        (∀ i,s i*algebraMap V K (f (FourRootOrderSigns318.generator
          (DVRNormalizedFiniteOrder318.coefficient V (fun j => (u j:V)*pi^(e j:ℕ)) a) i))=y i)) ∨
       (∃ (w : V) (f : DVRNormalizedInfinityOrder318.Order V
          (fun i => (u i:V)*pi^(e i:ℕ)) a →ₐ[V] V),
        t≠0 ∧ algebraMap V K w=t⁻¹ ∧ ¬IsUnit w ∧
        (∀ p : V[X], f (algebraMap V[X] (DVRNormalizedInfinityOrder318.Order V
          (fun i => (u i:V)*pi^(e i:ℕ)) a) p)=Polynomial.eval w p) ∧
        (∀ i,s i*t*algebraMap V K (f (FourRootOrderSigns318.generator
          (DVRNormalizedInfinityOrder318.coefficient V (fun j => (u j:V)*pi^(e j:ℕ)) a) i))=y i))) := by
  obtain ⟨u,e,s,hs,hc,hcharts⟩ := DVRNormalizedAllPlaceCharts318.chart_center V K pi hp c a t y hy
  refine ⟨u,e,s,hs,hc,?_⟩
  rcases hcharts with ⟨T,f,hT,hf,hr⟩ | ⟨w,f,ht,hw,hwn,hf,hr⟩
  · exact Or.inl ⟨T,NormalizedChartFiniteType318.pointAlgHom V T f hf,hT,hf,hr⟩
  · exact Or.inr ⟨w,NormalizedChartFiniteType318.pointAlgHom V w f hf,ht,hw,hwn,hf,hr⟩
end NormalizedIntegralPointInput318
