module
public import GammaHCuspEnds318
public import AllCuspInfinity318
public section
noncomputable section
open Function Filter Topology TopologicalSpace UpperHalfPlane
open GammaHGroup318 GammaHDiamond318 GammaHAction318 GammaHCuspEnds318
open FiniteCuspEnds318 AllCuspOverlap318 AllCuspFilling318 AllCuspInfinity318
open scoped MatrixGroups
namespace GammaHFilledAction318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

/-- The actual filled-disc range meets the original locus exactly in its
actual high-neighborhood end. -/
theorem original_mem_chart (N:ℕ) (hN:5≤N) (c:End N) (b:Fine N) :
    original N hN b∈Set.range (cuspChart N hN c) ↔ b∈c.val := by
  constructor
  · rintro ⟨q,hq⟩
    have hn:q.val≠0:=AllCuspHausdorff318.identification_nonzero N hN b c q hq.symm
    let p:Punctures N hN:=⟨c,⟨q.val,hn,q.property⟩⟩
    have hb:b=oldMap N hN p:=
      (original_openEmbedding N hN).injective (hq.symm.trans (original_oldMap N hN p).symm)
    rw [hb]
    exact oldMap_mem N hN p
  · intro hb
    let x:RotatedProjection318.neighborhood N (representative N c):=
      ⟨b,by rwa [representative_region]⟩
    let q:=RotatedHomeomorph318.cuspHomeomorph N hN (representative N c) x
    have he:oldMap N hN ⟨c,q⟩=b:=
      congrArg Subtype.val ((RotatedHomeomorph318.cuspHomeomorph N hN (representative N c)).symm_apply_apply x)
    refine ⟨inclusion N hN c q,?_⟩
    exact (original_oldMap N hN ⟨c,q⟩).symm.trans (congrArg (original N hN) he)

/-- Extend the actual matrix action to the actual all-cusp filling, using the
proved permutation of its actual finite end type. -/
@[expose] def filledAct (N:ℕ) (hN:5≤N) (H:Subgroup (ZMod N)ˣ) (g:gammaH N H)
    (z:Filled N hN) : Filled N hN := by
  classical
  exact if hz:∃b,original N hN b=z then original N hN (matrixAct N H g hz.choose)
    else cusp N hN (matrixEnd N H g ((original_or_cusp N hN z).resolve_left hz).choose)

theorem filledAct_original (N:ℕ) (hN:5≤N) (H:Subgroup (ZMod N)ˣ)
    (g:gammaH N H) (b:Fine N) :
    filledAct N hN H g (original N hN b)=original N hN (matrixAct N H g b) := by
  classical
  have hb:∃b',original N hN b'=original N hN b:=⟨b,rfl⟩
  have he:hb.choose=b:=(original_openEmbedding N hN).injective hb.choose_spec
  simp only [filledAct,dif_pos hb,he]

theorem filledAct_cusp (N:ℕ) (hN:5≤N) (H:Subgroup (ZMod N)ˣ)
    (g:gammaH N H) (c:End N) :
    filledAct N hN H g (cusp N hN c)=cusp N hN (matrixEnd N H g c) := by
  classical
  have hc:¬∃b,original N hN b=cusp N hN c:=by
    rintro ⟨b,hb⟩;exact original_ne_cusp N hN b c hb
  simp only [filledAct,dif_neg hc]
  congr 2
  exact cusp_injective N hN ((original_or_cusp N hN (cusp N hN c)).resolve_left hc).choose_spec

theorem filledAct_maps_chart (N:ℕ) (hN:5≤N) (H:Subgroup (ZMod N)ˣ)
    (g:gammaH N H) (c:End N) :
    Set.MapsTo (filledAct N hN H g) (Set.range (cuspChart N hN c))
      (Set.range (cuspChart N hN (matrixEnd N H g c))) := by
  rintro z ⟨q,rfl⟩
  by_cases hq:q.val=0
  · have he:q=zeroPoint N hN c:=Subtype.ext hq
    rw [he]
    change filledAct N hN H g (cusp N hN c)∈_
    rw [filledAct_cusp]
    exact ⟨zeroPoint N hN _,rfl⟩
  · let p:Punctures N hN:=⟨c,⟨q.val,hq,q.property⟩⟩
    rw [show cuspChart N hN c q=original N hN (oldMap N hN p) from (original_oldMap N hN p).symm,
      filledAct_original]
    apply (original_mem_chart N hN _ _).mpr
    rw [matrixEnd_val]
    exact ⟨oldMap N hN p,oldMap_mem N hN p,rfl⟩

theorem matrixAct_j (N:ℕ) (H:Subgroup (ZMod N)ˣ) (g:gammaH N H) (b:Fine N) :
    QuotientJ318.jMap N (matrixAct N H g b)=QuotientJ318.jMap N b := by
  induction b using Quotient.inductionOn with
  | h tau =>
    change ActualQJ318.jInvariant (g.val•tau)=ActualQJ318.jInvariant tau
    rw [ModularGroup.sl_moeb]
    exact ActualJInvariant318.modular_invariant _ ⟨g.val,rfl⟩ tau

theorem filledAct_jInfinity (N:ℕ) (hN:5≤N) (H:Subgroup (ZMod N)ˣ)
    (g:gammaH N H) (z:Filled N hN) :
    jInfinity N hN (filledAct N hN H g z)=jInfinity N hN z := by
  rcases original_or_cusp N hN z with ⟨b,rfl⟩|⟨c,rfl⟩
  · rw [filledAct_original,jInfinity_original,jInfinity_original,matrixAct_j]
  · rw [filledAct_cusp,jInfinity_cusp,jInfinity_cusp]

theorem jInfinity_eq_infty_iff (N:ℕ) (hN:5≤N) (z:Filled N hN) :
    jInfinity N hN z=OnePoint.infty ↔ z∈Set.range (cusp N hN) := by
  rcases original_or_cusp N hN z with ⟨b,rfl⟩|⟨c,rfl⟩
  · rw [jInfinity_original]
    constructor
    · intro h;exact False.elim (OnePoint.coe_ne_infty _ h)
    · rintro ⟨c,hc⟩;exact False.elim (original_ne_cusp N hN b c hc.symm)
  · exact ⟨fun _=>⟨c,rfl⟩,fun _=>jInfinity_cusp N hN c⟩

/-- Compactness, genuine j-growth, and disjoint actual cusp charts prove
continuity across every added cusp. No extension premise is supplied. -/
theorem filledAct_continuousAt_cusp (N:ℕ) (hN:5≤N) (H:Subgroup (ZMod N)ˣ)
    (g:gammaH N H) (c:End N) : ContinuousAt (filledAct N hN H g) (cusp N hN c) := by
  letI:=AllCuspCompact318.filled_compactSpace N hN
  letI:=AllCuspHausdorff318.filled_t2 N hN
  change Tendsto (filledAct N hN H g) (𝓝 (cusp N hN c))
    (𝓝 (filledAct N hN H g (cusp N hN c)))
  rw [filledAct_cusp]
  apply tendsto_nhds_of_unique_mapClusterPt
  intro y hy
  have hcluster:=hy.continuousAt_comp (jInfinity_continuous N hN).continuousAt
  have ht : Tendsto (jInfinity N hN ∘ filledAct N hN H g) (𝓝 (cusp N hN c)) (𝓝 OnePoint.infty) := by
    have he : jInfinity N hN ∘ filledAct N hN H g=jInfinity N hN :=
      funext (filledAct_jInfinity N hN H g)
    rw [he]
    have ht':=(jInfinity_continuous N hN).continuousAt (x:=cusp N hN c)
    change Tendsto (jInfinity N hN) (𝓝 (cusp N hN c)) (𝓝 (jInfinity N hN (cusp N hN c))) at ht'
    rwa [jInfinity_cusp] at ht' 
  have hj:jInfinity N hN y=OnePoint.infty:=eq_of_nhds_neBot (hcluster.clusterPt.mono ht).neBot
  obtain ⟨d,rfl⟩:=(jInfinity_eq_infty_iff N hN y).mp hj
  by_cases hdc:d=matrixEnd N H g c
  · exact congrArg (cusp N hN) hdc
  · exfalso
    have hdmem : Set.range (cuspChart N hN d)∈𝓝 (cusp N hN d) :=
      (cuspChart_openEmbedding N hN d).isOpen_range.mem_nhds ⟨zeroPoint N hN d,rfl⟩
    have hcfrequent:=mapClusterPt_iff_frequently.mp hy _ hdmem
    have hsource : Set.range (cuspChart N hN c)∈𝓝 (cusp N hN c) :=
      (cuspChart_openEmbedding N hN c).isOpen_range.mem_nhds ⟨zeroPoint N hN c,rfl⟩
    have htarget : ∀ᶠz in 𝓝 (cusp N hN c),
        filledAct N hN H g z∈Set.range (cuspChart N hN (matrixEnd N H g c)) :=
      Filter.mem_of_superset hsource (filledAct_maps_chart N hN H g c)
    obtain ⟨z,hzd,hzc⟩:=(hcfrequent.and_eventually htarget).exists
    exact Set.disjoint_left.mp (cuspCharts_disjoint N hN d (matrixEnd N H g c) hdc) hzd hzc

theorem filledAct_continuous (N:ℕ) (hN:5≤N) (H:Subgroup (ZMod N)ˣ)
    (g:gammaH N H) : Continuous (filledAct N hN H g) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  rcases original_or_cusp N hN z with ⟨b,rfl⟩|⟨c,rfl⟩
  · apply (original_openEmbedding N hN).continuousAt_iff.mp
    have he : filledAct N hN H g ∘ original N hN=original N hN ∘ matrixAct N H g :=
      funext (filledAct_original N hN H g)
    rw [he]
    exact ((original_openEmbedding N hN).continuous.comp (matrixAct_continuous N H g)).continuousAt
  · exact filledAct_continuousAt_cusp N hN H g c

end GammaHFilledAction318
