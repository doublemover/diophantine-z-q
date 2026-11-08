module
public import AllCuspHausdorff318
public section
noncomputable section
open Function Filter Topology TopologicalSpace GammaOneFiber318 PeterssonQuotient318
open WidthQParameter318 FiniteCuspEnds318 AllCuspOverlap318 AllCuspFilling318 QuotientJ318 AllCuspQJ318
namespace AllCuspInfinity318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

/-- The genuine j-map on the actual all-cusp compactification, with every cusp
mapped to infinity in the honest one-point compactification of C. -/
@[expose] def jInfinity (N:ℕ) (hN:5≤N) (z:Filled N hN) : OnePoint ℂ := by
  classical
  exact if hz:∃b,original N hN b=z then ↑(jMap N hz.choose) else OnePoint.infty

theorem jInfinity_original (N:ℕ) (hN:5≤N) (b:Base (image N)) :
    jInfinity N hN (original N hN b)=↑(jMap N b) := by
  classical
  have hb:∃b',original N hN b'=original N hN b:=⟨b,rfl⟩
  have he:hb.choose=b:=(original_openEmbedding N hN).injective hb.choose_spec
  simp only [jInfinity,dif_pos hb,he]

theorem jInfinity_cusp (N:ℕ) (hN:5≤N) (c:End N) :
    jInfinity N hN (cusp N hN c)=OnePoint.infty := by
  classical
  have hc:¬∃b,original N hN b=cusp N hN c:=by
    rintro ⟨b,hb⟩;exact original_ne_cusp N hN b c hb
  simp only [jInfinity,dif_neg hc]

theorem jInfinity_disc (N:ℕ) (hN:5≤N) (c:End N) (q:disc N hN c) :
    jInfinity N hN (cuspChart N hN c q)=FilledJInfinity318.localJ (q.val^natWidth N hN c) := by
  classical
  by_cases hq:q.val=0
  · have he:q=zeroPoint N hN c:=Subtype.ext hq
    rw [he]
    change jInfinity N hN (cusp N hN c)=FilledJInfinity318.localJ ((0:ℂ)^natWidth N hN c)
    rw [jInfinity_cusp,zero_pow (Nat.ne_of_gt (natWidth_pos N hN c)),FilledJInfinity318.localJ_zero]
  · let p:Punctures N hN:=⟨c,⟨q.val,hq,q.property⟩⟩
    rw [show cuspChart N hN c q=original N hN (oldMap N hN p) from (original_oldMap N hN p).symm,
      jInfinity_original,j_oldMap]
    simp only [FilledJInfinity318.localJ,if_neg (pow_ne_zero _ hq)]

theorem localJ_continuous (N:ℕ) (hN:5≤N) (c:End N) :
    Continuous (fun q:disc N hN c=>FilledJInfinity318.localJ (q.val^natWidth N hN c)) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  apply (FilledJInfinity318.localJ_continuousAt _ ?_).comp
    (continuous_subtype_val.continuousAt.pow _)
  change ‖q.val^natWidth N hN c‖<1
  rw [norm_pow]
  apply pow_lt_one₀ (norm_nonneg _) _ (Nat.ne_of_gt (natWidth_pos N hN c))
  exact lt_trans q.property (radius_lt_one _ _ (width_pos N hN c) (by norm_num))

/-- A global continuous extension of genuine j across every cusp. Its exact
local expression has the actual conjugate cusp width. -/
theorem jInfinity_continuous (N:ℕ) (hN:5≤N) : Continuous (jInfinity N hN) := by
  let f:Base (image N) ⊕ Discs N hN→Filled N hN:=Sum.elim (original N hN) (discsMap N hN)
  have hc:Continuous f:=continuous_sum_dom.mpr
    ⟨(original_openEmbedding N hN).continuous,(discsMap_openEmbedding N hN).continuous⟩
  have ho:IsOpenMap f:=(original_openEmbedding N hN).isOpenMap.sumElim
    (discsMap_openEmbedding N hN).isOpenMap
  have hs:Surjective f:=by
    intro z
    rcases TwoChartGluing318.jointly_surjective (overlap N hN) z with ⟨b,hb⟩|⟨q,hq⟩
    · exact ⟨Sum.inl b,hb⟩
    · exact ⟨Sum.inr q,hq⟩
  have hf:IsOpenQuotientMap f:=⟨hs,hc,ho⟩
  apply hf.isQuotientMap.continuous_iff.mpr
  apply continuous_sum_dom.mpr
  constructor
  · have he:(jInfinity N hN ∘ f) ∘ Sum.inl=fun b=>(jMap N b:OnePoint ℂ):=by
      funext b;exact jInfinity_original N hN b
    rw [he]
    exact OnePoint.continuous_coe.comp (HolomorphicQuotientJ318.jMap_continuous N hN)
  · apply continuous_sigma
    intro c
    have he:(fun q:disc N hN c=>(jInfinity N hN ∘ f) (Sum.inr ⟨c,q⟩))=
      fun q:disc N hN c=>FilledJInfinity318.localJ (q.val^natWidth N hN c):=by
      funext q;exact jInfinity_disc N hN c q
    change Continuous (fun q:disc N hN c=>(jInfinity N hN ∘ f) (Sum.inr ⟨c,q⟩))
    rw [he]
    exact localJ_continuous N hN c

end AllCuspInfinity318
