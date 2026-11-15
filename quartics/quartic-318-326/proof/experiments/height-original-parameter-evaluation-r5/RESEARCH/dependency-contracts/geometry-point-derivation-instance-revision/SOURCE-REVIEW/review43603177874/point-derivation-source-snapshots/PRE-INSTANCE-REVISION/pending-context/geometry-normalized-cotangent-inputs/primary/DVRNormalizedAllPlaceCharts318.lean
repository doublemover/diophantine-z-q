module
public import DVRNormalizedInfinityOrder318
public section
noncomputable section
namespace DVRNormalizedAllPlaceCharts318
open Polynomial
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (V K : Type*) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [Field K] [Algebra V K] [IsFractionRing V K]

/-- Every original signed four-root field point has a genuine integral
finite or reciprocal chart point after ONE common normalization of its four
twists. This covers nonunit original twists and nonintegral original t.
The displayed polynomial maps and all signed roots identify the actual data;
regularity and gluing of these potentially singular models remain separate. -/
theorem chart_center (pi : V) (hp : Irreducible pi) (c : Fin 4 → Kˣ)
    (a : Fin 4 → V) (t : K) (y : Fin 4 → K)
    (hy : ∀ i,(y i)^2=(c i:K)*(t-algebraMap V K (a i))) :
    ∃ (u : Fin 4 → Vˣ) (e : Fin 4 → Fin 2) (s : Fin 4 → K),
      (∀ i,s i≠0) ∧
      (∀ i,(c i:K)=algebraMap V K ((u i:V)*pi^(e i:ℕ))*(s i)^2) ∧
      ((∃ (T : V) (f : DVRNormalizedFiniteOrder318.Order V
          (fun i => (u i:V)*pi^(e i:ℕ)) a →+* V),
        algebraMap V K T=t ∧
        (∀ p : V[X], f (algebraMap V[X] (DVRNormalizedFiniteOrder318.Order V
          (fun i => (u i:V)*pi^(e i:ℕ)) a) p)=Polynomial.eval T p) ∧
        (∀ i,s i*algebraMap V K (f (FourRootOrderSigns318.generator
          (DVRNormalizedFiniteOrder318.coefficient V (fun j => (u j:V)*pi^(e j:ℕ)) a) i))=y i)) ∨
       (∃ (w : V) (f : DVRNormalizedInfinityOrder318.Order V
          (fun i => (u i:V)*pi^(e i:ℕ)) a →+* V),
        t≠0 ∧ algebraMap V K w=t⁻¹ ∧ ¬IsUnit w ∧
        (∀ p : V[X], f (algebraMap V[X] (DVRNormalizedInfinityOrder318.Order V
          (fun i => (u i:V)*pi^(e i:ℕ)) a) p)=Polynomial.eval w p) ∧
        (∀ i,s i*t*algebraMap V K (f (FourRootOrderSigns318.generator
          (DVRNormalizedInfinityOrder318.coefficient V (fun j => (u j:V)*pi^(e j:ℕ)) a) i))=y i))) := by
  obtain ⟨u,e,s,hs,hc⟩ := DVRTwistSquareNormalization318.normalize_four V K pi hp c
  refine ⟨u,e,s,hs,hc,?_⟩
  by_cases ht : IsLocalization.IsInteger V t
  · obtain ⟨T,hT⟩ := ht
    have h (i : Fin 4) : ∃ z : V, algebraMap V K z=y i/s i ∧
        z^2=((u i:V)*pi^(e i:ℕ))*(T-a i) := by
      apply IntegralValuativeRootCoordinates318.square_preimage V K
      rw [map_mul,map_sub,hT]
      exact DVRNormalizedContactPoint318.root_relation _ _ _ _ _ _ (hs i) (hc i) (hy i)
    choose z hz hz2 using h
    left
    refine ⟨T,DVRNormalizedFiniteOrder318.pointMap V _ a T z hz2,hT,
      DVRNormalizedFiniteOrder318.pointMap_polynomial V _ a T z hz2,?_⟩
    intro i
    rw [DVRNormalizedFiniteOrder318.pointMap_root,hz]
    exact DVRNormalizedContactPoint318.original_root _ _ (hs i)
  · have ht0 : t≠0 := by
      intro h
      exact ht ⟨0,by simpa only [map_zero] using h.symm⟩
    obtain ⟨w,hw⟩ := (ValuationRing.isInteger_or_isInteger V t).resolve_left ht
    have hwn : ¬IsUnit w := by
      rintro ⟨v,hv⟩
      apply ht
      refine ⟨(↑v⁻¹:V),?_⟩
      rw [map_units_inv,hv,hw,inv_inv]
    obtain ⟨z,hz,hz2,hr⟩ := DVRNormalizedInfinityOrder318.integral_roots V K
      (fun i => (u i:V)*pi^(e i:ℕ)) a c s hs hc t ht0 w hw y hy
    right
    refine ⟨w,DVRNormalizedInfinityOrder318.pointMap V _ a w z hz2,ht0,hw,hwn,
      DVRNormalizedInfinityOrder318.pointMap_polynomial V _ a w z hz2,?_⟩
    intro i
    rw [DVRNormalizedInfinityOrder318.pointMap_root]
    exact hr i
end DVRNormalizedAllPlaceCharts318
