module
public import AllCuspConnected318
public import Mathlib.Analysis.Meromorphic.Order
public section
noncomputable section
open Function Filter Topology TopologicalSpace GammaOneFiber318 PeterssonQuotient318
open FiniteCuspEnds318 AllCuspOverlap318 AllCuspFilling318 AllCuspCharts318 QuotientJ318 AllCuspQJ318
namespace AllCuspJ318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

/-- Genuine j on the original locus, with the meromorphic totalization zero
at every added pole. The honest sphere-valued extension is in AllCuspInfinity318. -/
@[expose] def filledJ (N:ℕ) (hN:5≤N) (z:Filled N hN) : ℂ := by
  classical
  exact if hz:∃b,original N hN b=z then jMap N hz.choose else 0

theorem filledJ_original (N:ℕ) (hN:5≤N) (b:Base (image N)) : filledJ N hN (original N hN b)=jMap N b := by
  classical
  have hb:∃b',original N hN b'=original N hN b:=⟨b,rfl⟩
  simp only [filledJ,dite_eq_left hb]
  congr 1
  exact (original_openEmbedding N hN).injective hb.choose_spec

theorem filledJ_cusp (N:ℕ) (hN:5≤N) (c:End N) : filledJ N hN (cusp N hN c)=0 := by
  classical
  have hc:¬∃b,original N hN b=cusp N hN c:=by
    rintro ⟨b,hb⟩;exact original_ne_cusp N hN b c hb
  simp only [filledJ,dite_eq_right hc]

theorem filledJ_disc (N:ℕ) (hN:5≤N) (c:End N) (q:disc N hN c) :
    filledJ N hN (cuspChart N hN c q)=ActualQJ318.G (q.val^natWidth N hN c)/(q.val^natWidth N hN c) := by
  by_cases hq:q.val=0
  · have he:q=zeroPoint N hN c:=Subtype.ext hq
    rw [he]
    change filledJ N hN (cusp N hN c)=ActualQJ318.G ((0:ℂ)^natWidth N hN c)/((0:ℂ)^natWidth N hN c)
    simp only [filledJ_cusp,zero_pow (Nat.ne_of_gt (natWidth_pos N hN c)),div_zero]
  · let p:Punctures N hN:=⟨c,⟨q.val,hq,q.property⟩⟩
    rw [show cuspChart N hN c q=original N hN (oldMap N hN p) from (original_oldMap N hN p).symm,
      filledJ_original]
    exact j_oldMap N hN c p.2

theorem new_symm (N:ℕ) (hN:5≤N) (c:End N) (q:ℂ) (hq:q∈disc N hN c) :
    (newChart N hN c).symm q=cuspChart N hN c ⟨q,hq⟩ := by
  have hs:cuspChart N hN c ⟨q,hq⟩∈(newChart N hN c).source:=by
    rw [new_source];exact ⟨⟨q,hq⟩,rfl⟩
  simpa only [new_apply] using (newChart N hN c).left_inv hs

theorem filledJ_coordinate (N:ℕ) (hN:5≤N) (c:End N) (q:ℂ) (hq:q∈disc N hN c) :
    filledJ N hN ((newChart N hN c).symm q)=ActualQJ318.G (q^natWidth N hN c)/(q^natWidth N hN c) := by
  rw [new_symm N hN c q hq]
  exact filledJ_disc N hN c ⟨q,hq⟩

end AllCuspJ318
