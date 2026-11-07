module
public import GlobalLogRatios318
public import SourceAlternatePrecision318
public section
namespace SourceAlternateRatios318
open ConcreteG8Domain CircuitReplay Raw318FinalReplay CompressedGeneratorBridge318
open LocalGenerator318 GlobalGeneratorPoints318 WeierstrassCurve.Affine
open CompressedOrientation318 RawLucasOrientation318 CompressedGlobal318 SourceAlternateDomain318 SourceAlternateBase318 SourceAlternatePrecision318
open ActualLogHom318 AlternateSourceData318 AlternateRatioKernel318
open scoped QuadraticAlgebra
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
variable (p:ℕ) [Fact p.Prime]
local instance : DecidableEq ℚ_[p] := Classical.decEq _

@[expose] def globalMap (φ:K→+*ℚ_[p]) :
    LocalGenerator318.E.Point→+(ReciprocalDouble318.E (φ CompressedOrientation318.D)).Point :=
  (ShortCurveBaseChange318.pointMap φ CompressedOrientation318.D).comp
    (transport curve_eq).symm.toAddMonoidHom

theorem globalMap_V (φ:K→+*ℚ_[p]) (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w) :
    globalMap p φ (transport curve_eq (CompressedTranslation318.V S w source))=
      mappedV p φ S w source := by
  change ShortCurveBaseChange318.pointMap φ CompressedOrientation318.D
    ((transport curve_eq).symm ((transport curve_eq) (CompressedTranslation318.V S w source)))=_
  rw [AddEquiv.symm_apply_apply]
  rfl

theorem globalMap_alternate (φ:K→+*ℚ_[p]) (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) (j:Fin 4) (hy:RawRootDifference318.v w j≠0) :
    globalMap p φ (transport curve_eq (RawRootDifference318.V S w source j))=
      mappedAlternate p φ S w source j hy := by
  change ShortCurveBaseChange318.pointMap φ CompressedOrientation318.D
    ((transport curve_eq).symm ((transport curve_eq) (RawRootDifference318.V S w source j)))=_
  rw [AddEquiv.symm_apply_apply]
  rfl

/-- The literal alternate stored quotient approximates the rational ratio of
 the actual coherent global labels. Source formality, positive branch and the
 entire analytic estimate are discharged, not supplied as hypotheses. -/
theorem source_alternate_labeled_precision (hp:19≤p) (φ:K→+*ℚ_[p]) (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) (hshift:shift w≠0)
    (hD:Padic.addValuation (φ CompressedOrientation318.D)=0)
    (hf:(2:WithTop ℤ)≤Padic.addValuation (φ (fV w)))
    (hdelta:∀j,0<Padic.addValuation (φ (RawRootDifference318.v w j)-1))
    (vLabel:Fin 4→ℤ) (n:ℤ) (tau:LocalGenerator318.E.Point)
    (hlabels:∀j,vLabel j • P=transport curve_eq (RawRootDifference318.V S w source j))
    (hanchor:transport curve_eq (CompressedTranslation318.V S w source)=(n-1) • P+tau)
    (htau:tau=0 ∨ tau=T 0) :
    ∃s:ℤ,1≤s ∧ Padic.addValuation (φ (fV w))=(2*s:ℤ) ∧
      ∀j,∃r:ℤ,1≤r ∧
        (φ (RawRootDifference318.v w j)-1=0 ∨
          (φ (RawRootDifference318.v w j)-1).valuation=4*r) ∧
        Padic.addValuation (φ (RawRootDifference318.u w j)/φ (zV w))+
          ((min (rate (full j)*r) (16*s):ℤ):WithTop ℤ)≤
          Padic.addValuation ((((vLabel j:ℚ)/((n-1:ℤ):ℚ)):ℚ_[p])-φ (rawRatio w j)) := by
  obtain ⟨hDn,hV,s,hs,hfs,hlogV,hdata⟩:=source_alternate_precision p hp φ S w source hshift hD hf hdelta
  have hn:=GlobalLogRatios318.source_V_label_nonzero S w source hshift n tau htau hanchor
  have ht:(2:ℤ) • tau=0 := by
    rcases htau with hz|hz
    · rw [hz,two_zsmul]; exact zero_add _
    · rw [hz,two_zsmul]; exact double_T 0
  refine ⟨s,hs,hfs,?_⟩
  intro j
  obtain ⟨hy,hU,r,hr,hdr,herr⟩:=hdata j
  refine ⟨r,hr,hdr,?_⟩
  let SG:=formalSubgroup p hp (φ CompressedOrientation318.D) hDn
  let ell:=logHom p hp (φ CompressedOrientation318.D) hDn
  let psi:=globalMap p φ
  let V:=transport curve_eq (CompressedTranslation318.V S w source)
  let Q:=transport curve_eq (RawRootDifference318.V S w source j)
  have hmV:psi V∈SG := by rw [globalMap_V]; exact hV
  have hmQ:psi Q∈SG := by rw [globalMap_alternate p φ S w source j hy]; exact hU
  have hlog:ell ⟨psi V,hmV⟩≠0 := by
    apply (Padic.addValuation.ne_top_iff).mp
    have hv:Padic.addValuation (ell ⟨psi V,hmV⟩)=s := by
      change Padic.addValuation (logHom p hp (φ CompressedOrientation318.D) hDn ⟨_,_⟩)=s
      simpa only [psi,V,globalMap_V] using hlogV
    rw [hv]; simp
  have he:=GlobalLogRatios318.mapped_log_ratio psi SG ell P V Q tau (n-1) (vLabel j)
    hanchor (hlabels j).symm ht hmV hmQ hn hlog
  have he':logHom p hp (φ CompressedOrientation318.D) hDn ⟨mappedAlternate p φ S w source j hy,hU⟩ /
      logHom p hp (φ CompressedOrientation318.D) hDn ⟨mappedV p φ S w source,hV⟩=
      (((vLabel j:ℚ)/((n-1:ℤ):ℚ)):ℚ_[p]) := by
    simpa only [psi,V,Q,globalMap_V,globalMap_alternate p φ S w source j hy,ell,
      Rat.cast_div,Rat.cast_intCast] using he
  rw [he'] at herr
  exact herr


/-- The exact alternate analytic quotient and the stored Padé quotient have
 the same valuation as u/z, including a zero numerator. -/
theorem source_alternate_ratio_values (hp:19≤p) (φ:K→+*ℚ_[p]) (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) (hshift:shift w≠0)
    (hD:Padic.addValuation (φ CompressedOrientation318.D)=0)
    (hf:(2:WithTop ℤ)≤Padic.addValuation (φ (fV w)))
    (hdelta:∀j,0<Padic.addValuation (φ (RawRootDifference318.v w j)-1))
    (vLabel:Fin 4→ℤ) (n:ℤ) (tau:LocalGenerator318.E.Point)
    (hlabels:∀j,vLabel j • P=transport curve_eq (RawRootDifference318.V S w source j))
    (hanchor:transport curve_eq (CompressedTranslation318.V S w source)=(n-1) • P+tau)
    (htau:tau=0 ∨ tau=T 0) :
    ∀j,Padic.addValuation (φ (rawRatio w j))=
      Padic.addValuation ((((vLabel j:ℚ)/((n-1:ℤ):ℚ)):ℚ_[p])) ∧
      Padic.addValuation (φ (RawRootDifference318.u w j)/φ (zV w))=
      Padic.addValuation ((((vLabel j:ℚ)/((n-1:ℤ):ℚ)):ℚ_[p])) := by
  obtain ⟨hDn,hV,s,hs,hfs,hws,hzs,hlogV⟩:=source_V_domain p hp φ S w source hshift hD hf
  have hn:=GlobalLogRatios318.source_V_label_nonzero S w source hshift n tau htau hanchor
  have ht:(2:ℤ) • tau=0 := by
    rcases htau with hz|hz
    · rw [hz,two_zsmul]; exact zero_add _
    · rw [hz,two_zsmul]; exact double_T 0
  intro j
  obtain ⟨hy,hDn',hU,r,hr,hdr,hlogU⟩:=source_alternate_domain p hp φ S w source j hD (hdelta j)
  let SG:=formalSubgroup p hp (φ CompressedOrientation318.D) hDn
  let ell:=logHom p hp (φ CompressedOrientation318.D) hDn
  let psi:=globalMap p φ
  let V:=transport curve_eq (CompressedTranslation318.V S w source)
  let Q:=transport curve_eq (RawRootDifference318.V S w source j)
  have hmV:psi V∈SG := by rw [globalMap_V]; exact hV
  have hmQ:psi Q∈SG := by rw [globalMap_alternate p φ S w source j hy]; exact hU
  have hlog:ell ⟨psi V,hmV⟩≠0 := by
    apply (Padic.addValuation.ne_top_iff).mp
    have hv:Padic.addValuation (ell ⟨psi V,hmV⟩)=s := by
      change Padic.addValuation (logHom p hp (φ CompressedOrientation318.D) hDn ⟨_,_⟩)=s
      have hv' : Padic.addValuation (logHom p hp (φ CompressedOrientation318.D) hDn
          ⟨mappedV p φ S w source,hV⟩)=s := by
        rw [hlogV,Padic.addValuation.map_mul,
          CanonicalRoot318.factor_unit p hp _ s hs (Or.inr hws),add_zero,hzs]
      simpa only [psi,V,globalMap_V] using hv' 
    rw [hv]; simp
  have he:=GlobalLogRatios318.mapped_log_ratio psi SG ell P V Q tau (n-1) (vLabel j)
    hanchor (hlabels j).symm ht hmV hmQ hn hlog
  have he':logHom p hp (φ CompressedOrientation318.D) hDn ⟨mappedAlternate p φ S w source j hy,hU⟩ /
      logHom p hp (φ CompressedOrientation318.D) hDn ⟨mappedV p φ S w source,hV⟩=
      (((vLabel j:ℚ)/((n-1:ℤ):ℚ)):ℚ_[p]) := by
    simpa only [psi,V,Q,globalMap_V,globalMap_alternate p φ S w source j hy,ell,
      Rat.cast_div,Rat.cast_intCast] using he
  have hval:Padic.addValuation (φ (RawRootDifference318.u w j)/φ (zV w))=
      Padic.addValuation ((((vLabel j:ℚ)/((n-1:ℤ):ℚ)):ℚ_[p])) := by
    rw [←he',hlogU,hlogV]
    simp only [Padic.addValuation.map_div,Padic.addValuation.map_mul,Padic.addValuation.map_neg,
      J_unit p hp _ r hr hdr,CanonicalRoot318.factor_unit p hp _ s hs (Or.inr hws),add_zero]
  refine ⟨?_,hval⟩
  rw [mapped_ratio p φ S w source hshift j]
  rw [Padic.addValuation.map_div,Padic.addValuation.map_mul,Padic.addValuation.map_neg,
    approximation_unit p hp (full j) _ r hr hdr,add_zero,
    Padic.addValuation.map_mul,ActualLogRatio318.pade_factor_unit p hp _ s hs (Or.inr hws),add_zero]
  simpa only [Padic.addValuation.map_div] using hval

/-- After the separately established integrality bootstrap, the actual
 alternate source error is at least8 for index0 and at least16 for the
 three full Padé numerators. These exceed the literal target orders4/13. -/
theorem source_alternate_integral_precision (hp:19≤p) (φ:K→+*ℚ_[p]) (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) (hshift:shift w≠0)
    (hD:Padic.addValuation (φ CompressedOrientation318.D)=0)
    (hf:(2:WithTop ℤ)≤Padic.addValuation (φ (fV w)))
    (hdelta:∀j,0<Padic.addValuation (φ (RawRootDifference318.v w j)-1))
    (vLabel:Fin 4→ℤ) (n:ℤ) (tau:LocalGenerator318.E.Point)
    (hlabels:∀j,vLabel j • P=transport curve_eq (RawRootDifference318.V S w source j))
    (hanchor:transport curve_eq (CompressedTranslation318.V S w source)=(n-1) • P+tau)
    (htau:tau=0 ∨ tau=T 0)
    (hi:∀j,0≤Padic.addValuation ((((vLabel j:ℚ)/((n-1:ℤ):ℚ)):ℚ_[p]))) :
    ∀j,((rate (full j):ℤ):WithTop ℤ)≤
      Padic.addValuation ((((vLabel j:ℚ)/((n-1:ℤ):ℚ)):ℚ_[p])-φ (rawRatio w j)) := by
  obtain ⟨s,hs,hfs,hdata⟩:=source_alternate_labeled_precision p hp φ S w source hshift hD hf hdelta
    vLabel n tau hlabels hanchor htau
  have hvals:=source_alternate_ratio_values p hp φ S w source hshift hD hf hdelta
    vLabel n tau hlabels hanchor htau
  intro j
  obtain ⟨r,hr,hdr,herr⟩:=hdata j
  have hv:0≤Padic.addValuation (φ (RawRootDifference318.u w j)/φ (zV w)) := by
    rw [(hvals j).2]; exact hi j
  have hk:rate (full j)≤min (rate (full j)*r) (16*s) := by
    cases hfull:full j <;> simp only [hfull,rate,Bool.false_eq_true,ite_false,ite_true] <;> omega
  apply le_trans _ herr
  have hk' : ((min (rate (full j)*r) (16*s):ℤ):WithTop ℤ) ≤
      Padic.addValuation (φ (RawRootDifference318.u w j)/φ (zV w))+
        ((min (rate (full j)*r) (16*s):ℤ):WithTop ℤ) := by
    simpa only [zero_add] using add_le_add hv
      (le_refl ((min (rate (full j)*r) (16*s):ℤ):WithTop ℤ))
  exact (WithTop.coe_le_coe.mpr hk).trans hk' 

end
end SourceAlternateRatios318
#print axioms SourceAlternateRatios318.source_alternate_labeled_precision

#print axioms SourceAlternateRatios318.source_alternate_ratio_values
#print axioms SourceAlternateRatios318.source_alternate_integral_precision
