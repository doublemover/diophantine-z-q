module
public import ActualDvrMeromorphicOrder318
public section
noncomputable section
namespace ActualDvrFractionValuationTransport318
open IsDiscreteValuationRing
variable {R S:Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
/-- A genuine local-ring isomorphism preserves the normalized DVR
valuation. Its normalization follows from actual irreducible factors,
not from agreeing only on the support of the maximal ideal. -/
lemma integral_value(e:R≃+*S)(x:R):addVal S (e x)=addVal R x:=by
  by_cases hx:x=0
  · rw [hx,map_zero,addVal_zero,addVal_zero]
  · obtain ⟨π,hπ⟩:=exists_prime R
    obtain ⟨n,u,hu⟩:=eq_unit_mul_pow_irreducible hx hπ.irreducible
    have hi:Irreducible (e π):=
      (MulEquiv.irreducible_iff (f:=e.toMulEquiv)).mpr hπ.irreducible
    have he:e x=(Units.map e.toMonoidHom u:Sˣ)*(e π)^n:=by
      rw [hu,map_mul,map_pow]
      rfl
    rw [addVal_def x u hπ.irreducible n hu,
      addVal_def (e x) (Units.map e.toMonoidHom u) hi n he]
variable {K L:Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra S L] [IsFractionRing S L]
/-- Exact covariance under a specified field map extending the SAME
local-ring equivalence. All original coefficient embeddings are kept in
this hypothesis and later instantiated by actual generic stalk maps. -/
theorem fraction_value(e:R≃+*S)(f:K→+*L)
    (hf:∀r:R,f (algebraMap R K r)=algebraMap S L (e r))(x:K):
    ActualDvrMeromorphicOrder318.value S L (f x)=
      ActualDvrMeromorphicOrder318.value R K x:=by
  have hint(r:R):ActualDvrMeromorphicOrder318.value S L (f (algebraMap R K r))=
      ActualDvrMeromorphicOrder318.value R K (algebraMap R K r):=by
    rw [hf]
    by_cases hr:r=0
    · simp only [hr,map_zero]
    · rw [ActualDvrMeromorphicOrder318.value_integral S L (e r)
        ((map_ne_zero_iff e e.injective).mpr hr),
        ActualDvrMeromorphicOrder318.value_integral R K r hr,integral_value e r]
  obtain ⟨a,b,hb,rfl⟩:=IsFractionRing.div_surjective (A:=R) x
  rw [map_div₀,(ActualDvrMeromorphicOrder318.value S L).map_div,
    (ActualDvrMeromorphicOrder318.value R K).map_div,hint a,hint b]
theorem fraction_order(e:R≃+*S)(f:K→+*L)
    (hf:∀r:R,f (algebraMap R K r)=algebraMap S L (e r))(x:K):
    ActualDvrMeromorphicOrder318.order S L (f x)=
      ActualDvrMeromorphicOrder318.order R K x:=by
  unfold ActualDvrMeromorphicOrder318.order
  rw [fraction_value e f hf x]
end ActualDvrFractionValuationTransport318
