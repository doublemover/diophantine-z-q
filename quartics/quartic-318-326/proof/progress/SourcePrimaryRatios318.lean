module
public import GlobalLogRatios318
public import SourcePrimarySplitLog318
public section
namespace SourcePrimaryRatios318
open ConcreteG8Domain CircuitReplay Raw318FinalReplay CompressedGeneratorBridge318
open LocalGenerator318 GlobalGeneratorPoints318 WeierstrassCurve.Affine
open SourceSplitLog318 SourcePrimarySplitLog318 ActualLogHom318
open scoped QuadraticAlgebra
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
variable (p:ℕ) [Fact p.Prime]
local instance : DecidableEq ℚ_[p] := Classical.decEq _

@[expose] def globalMap (rho:ℚ_[p]) (hr:rho^2=2) :
    E.Point→+(ReciprocalDouble318.E (phi p rho hr CompressedOrientation318.D)).Point :=
  (ShortCurveBaseChange318.pointMap (phi p rho hr) CompressedOrientation318.D).comp
    (transport curve_eq).symm.toAddMonoidHom

theorem globalMap_H (rho:ℚ_[p]) (hr:rho^2=2) (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w) :
    globalMap p rho hr (transport curve_eq (CompressedTranslation318.H S w source))=
      mappedH p rho hr S w source := by
  change ShortCurveBaseChange318.pointMap (phi p rho hr) CompressedOrientation318.D
    ((transport curve_eq).symm ((transport curve_eq) (CompressedTranslation318.H S w source)))=_
  rw [AddEquiv.symm_apply_apply]
  rfl

theorem globalMap_primary (rho:ℚ_[p]) (hr:rho^2=2) (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) (j:Fin 4) (hy:PrimaryFormal318.y w j≠0) :
    globalMap p rho hr (transport curve_eq (RawRootDifference318.U S w source j))=
      mappedPrimary p rho hr S w source j hy := by
  change ShortCurveBaseChange318.pointMap (phi p rho hr) CompressedOrientation318.D
    ((transport curve_eq).symm ((transport curve_eq) (RawRootDifference318.U S w source j)))=_
  rw [AddEquiv.symm_apply_apply]
  rfl

/-- Source memberships and depths are proved, and the log ratios are the
 actual rational ratios of the coherent global integer labels. This is
 not merely a parameter-ratio assertion. All zero Ui branches are included. -/
theorem source_primary_exact_ratios (rho:ℚ_[p]) (hr:rho^2=2) (hp:19≤p)
    (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w)
    (hgood:¬p∣FiniteContact318.contactModulus) (hp41:¬p∣41)
    (hf:(8:WithTop ℤ)≤ConcretePadic318.place p rho hr (CompressedOrientation318.fH w))
    (hleaf:∀j,(2:WithTop ℤ)≤ConcretePadic318.place p rho hr (PrimaryFormal318.leaf S w j))
    (uLabel:Fin 4→ℤ) (n:ℤ) (tau:E.Point) (hn:n≠0)
    (hlabels:∀j,uLabel j • P=transport curve_eq (RawRootDifference318.U S w source j))
    (hanchor:transport curve_eq (CompressedTranslation318.H S w source)=n • P+tau)
    (htau:tau=0 ∨ tau=T 0) :
    ∃(hDn:‖phi p rho hr CompressedOrientation318.D‖≤1)
      (hH:mappedH p rho hr S w source∈formalSubgroup p hp (phi p rho hr CompressedOrientation318.D) hDn)
      (r:ℤ),4≤r ∧
      Padic.addValuation (logHom p hp (phi p rho hr CompressedOrientation318.D) hDn
        ⟨mappedH p rho hr S w source,hH⟩)=r ∧
      ∀j,∃(hy:PrimaryFormal318.y w j≠0)
        (hU:mappedPrimary p rho hr S w source j hy∈formalSubgroup p hp (phi p rho hr CompressedOrientation318.D) hDn),
        logHom p hp (phi p rho hr CompressedOrientation318.D) hDn ⟨mappedPrimary p rho hr S w source j hy,hU⟩ /
          logHom p hp (phi p rho hr CompressedOrientation318.D) hDn ⟨mappedH p rho hr S w source,hH⟩=
          (((uLabel j:ℚ)/(n:ℚ)):ℚ_[p]) := by
  obtain ⟨hDn,hH,r,hr4,hfr,hrlog,hdata⟩:=source_split_log_data p rho hr hp S w source hgood hp41 hf hleaf
  have ht:(2:ℤ) • tau=0 := by
    rcases htau with hz|hz
    · rw [hz,two_zsmul]; exact zero_add _
    · rw [hz,two_zsmul]; exact double_T 0
  refine ⟨hDn,hH,r,hr4,hrlog,?_⟩
  intro j
  obtain ⟨hy,hU,hzero,hparam,hval⟩:=hdata j
  refine ⟨hy,hU,?_⟩
  let SG:=formalSubgroup p hp (phi p rho hr CompressedOrientation318.D) hDn
  let ell:=logHom p hp (phi p rho hr CompressedOrientation318.D) hDn
  let psi:=globalMap p rho hr
  let H:=transport curve_eq (CompressedTranslation318.H S w source)
  let Q:=transport curve_eq (RawRootDifference318.U S w source j)
  have hmH:psi H∈SG := by rw [globalMap_H]; exact hH
  have hmQ:psi Q∈SG := by rw [globalMap_primary p rho hr S w source j hy]; exact hU
  have hlog:ell ⟨psi H,hmH⟩≠0 := by
    apply (Padic.addValuation.ne_top_iff).mp
    have hv:Padic.addValuation (ell ⟨psi H,hmH⟩)=r := by
      change Padic.addValuation (logHom p hp (phi p rho hr CompressedOrientation318.D) hDn ⟨_,_⟩)=r
      simpa only [psi,H,globalMap_H] using hrlog
    rw [hv]; simp
  have he:=GlobalLogRatios318.mapped_log_ratio psi SG ell P H Q tau n (uLabel j)
    hanchor (hlabels j).symm ht hmH hmQ hn hlog
  simpa only [psi,H,Q,globalMap_H,globalMap_primary p rho hr S w source j hy,ell, Rat.cast_div, Rat.cast_intCast] using he

end
end SourcePrimaryRatios318
#print axioms SourcePrimaryRatios318.source_primary_exact_ratios
