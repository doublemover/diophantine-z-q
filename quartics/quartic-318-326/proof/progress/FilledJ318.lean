module
public import FilledCuspEmbeddings318
public import Mathlib.Analysis.Meromorphic.Order
public section
noncomputable section
open Function Filter Topology TopologicalSpace GammaOneFiber318
open PeterssonQuotient318 ActualSingleCusp318 FilledCuspCharts318 QuotientJ318
namespace FilledJ318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

/-- The genuine quotient j-function on the old locus, totalized to zero at the
new pole. Meromorphic statements concern the punctured germ, not this value. -/
@[expose] def filledJ (N:ℕ) (z:Filled N) : ℂ := by
  classical
  exact if h:∃b,original N b=z then jMap N h.choose else 0

theorem filledJ_original (N:ℕ) (b:Base (image N)) : filledJ N (original N b)=jMap N b := by
  classical
  have h:∃c,original N c=original N b := ⟨b,rfl⟩
  simp only [filledJ,dif_pos h]
  congr 1
  exact (original_isOpenEmbedding N).injective h.choose_spec

theorem filledJ_cusp (N:ℕ) : filledJ N (cusp N)=0 := by
  classical
  have h:¬∃b,original N b=cusp N := by rintro ⟨b,hb⟩;exact original_ne_cusp N b hb
  simp only [filledJ,dif_neg h]

theorem filledJ_disc (N:ℕ) (q:disc) : filledJ N (cuspChart N q)=ActualQJ318.G q/(q:ℂ) := by
  by_cases hq:(q:ℂ)=0
  · have he:q=zeroPoint:=Subtype.ext hq
    rw [he]
    change filledJ N (cusp N)=ActualQJ318.G 0/0
    simp only [filledJ_cusp,div_zero]
  · have hn:cuspChart N q≠cusp N := by
      intro h
      have := (cuspChart_isOpenEmbedding N).injective h
      exact hq (congrArg Subtype.val this)
    obtain ⟨b,hb⟩:∃b,original N b=cuspChart N q :=
      (Set.ext_iff.mp (range_original N) _).mpr hn
    rw [←hb,filledJ_original]
    exact CuspSeparation318.identification_j N b q hb

theorem new_symm (N:ℕ) (q:ℂ) (hq:q∈disc) :
    (newChart N).symm q=cuspChart N ⟨q,hq⟩ := by
  have hs:cuspChart N ⟨q,hq⟩∈(newChart N).source := by
    rw [new_source];exact ⟨⟨q,hq⟩,rfl⟩
  simpa only [new_apply] using (newChart N).left_inv hs

theorem filledJ_coordinate (N:ℕ) (q:ℂ) (hq:q∈disc) :
    filledJ N ((newChart N).symm q)=ActualQJ318.G q/q := by
  rw [new_symm N q hq]
  exact filledJ_disc N ⟨q,hq⟩

end FilledJ318
