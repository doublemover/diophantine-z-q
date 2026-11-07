module
public import SplitReciprocalDepth318
public import ScalarPlaceBridge318
public import SourceSplitLog318
public import RawCompressedLabels318
public import RawOddAnchorPoints318
public import TorsionSafeIndex318
public section
namespace RawSplitScalar318
open ConcreteG8Domain (K)
open CircuitReplay Raw318FinalReplay CompressedGeneratorBridge318
open WeierstrassCurve.Affine ActualLogHom318
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
variable (p:ℕ) [Fact p.Prime] (rho:ℚ_[p]) (hr:rho^2=2)
local notation "φ" => SourceSplitLog318.phi p rho hr
local notation "d" => φ CompressedOrientation318.D
local instance : DecidableEq ℚ_[p] := Classical.decEq _
/-- Exact actual group base change from the global generator's curve to
 the actual normalized inert completion. -/
@[expose] def globalMap : LocalGenerator318.E.Point→+(ReciprocalDouble318.E d).Point :=
  (ShortCurveBaseChange318.pointMap φ CompressedOrientation318.D).comp
    (transport curve_eq).symm.toAddMonoidHom

theorem globalMap_some (x y:K) (h:LocalGenerator318.E.Nonsingular x y) :
    ∃hlocal:(ReciprocalDouble318.E d).Nonsingular (φ x) (φ y),
      globalMap p rho hr (Point.some x y h)=Point.some (φ x) (φ y) hlocal := by
  have hc:CompressedPoint318.E.Nonsingular x y := by simpa only [curve_eq] using h
  have hs:(transport curve_eq).symm (Point.some x y h)=Point.some x y hc := by
    apply (transport curve_eq).injective
    rw [AddEquiv.apply_symm_apply,transport_some]
  refine ⟨ShortCurveBaseChange318.nonsingular_map φ CompressedOrientation318.D x y hc,?_⟩
  change ShortCurveBaseChange318.pointMap φ CompressedOrientation318.D
    ((transport curve_eq).symm (Point.some x y h))=_
  rw [hs]
  exact ShortCurveBaseChange318.pointMap_some φ CompressedOrientation318.D x y hc

theorem globalMap_H (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w) :
    ∃hlocal:(ReciprocalDouble318.E d).Nonsingular (1/φ (CompressedOrientation318.fH w))
        (φ (CompressedPoint318.yH w)),
      globalMap p rho hr (transport curve_eq (CompressedTranslation318.H S w source))=
        Point.some _ _ hlocal := by
  rw [CompressedTranslation318.H,transport_some]
  obtain ⟨hl,he⟩:=globalMap_some p rho hr (CompressedPoint318.xH w) (CompressedPoint318.yH w)
    (by simpa only [←curve_eq] using (CompressedGlobal318.source_global_H S w source).2.2.1)
  have hx:φ (CompressedPoint318.xH w)=1/φ (CompressedOrientation318.fH w) := by
    simp only [CompressedPoint318.xH,map_div₀,map_one]
  have hl':(ReciprocalDouble318.E d).Nonsingular (1/φ (CompressedOrientation318.fH w))
      (φ (CompressedPoint318.yH w)) := by simpa only [hx] using hl
  refine ⟨hl',?_⟩
  simpa only [hx] using he

theorem globalMap_scalar (w:Assignment) (c:ℤ) (hlabel:RawOddAnchorPoints318.ScalarLabel w c) :
    ∃(y:ℚ_[p])(hlocal:(ReciprocalDouble318.E d).Nonsingular (1/φ (ScalarSource318.fR w)) y),
      globalMap p rho hr (c • LocalGenerator318.P)=Point.some _ y hlocal := by
  obtain ⟨y,h,hpt⟩:=hlabel
  obtain ⟨hl,he⟩:=globalMap_some p rho hr ((RawAnchorNorm318.scalarRoot w)^2) y h
  have hx:φ ((RawAnchorNorm318.scalarRoot w)^2)=1/φ (ScalarSource318.fR w) := by
    simp only [ScalarSource318.fR,map_pow,map_inv₀,one_div,inv_pow,inv_inv]
  have hl':(ReciprocalDouble318.E d).Nonsingular (1/φ (ScalarSource318.fR w)) (φ y) := by simpa only [hx] using hl
  refine ⟨φ y,hl',?_⟩
  rw [hpt,he]
  simp only [hx]

/-- The selected actual split place with reciprocal-abscissa gain16 forces
p^8 divisibility of the actual scalar index, via the constructed local log. -/
theorem source_at_place (hp:19≤p) (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w)
    (hD:ConcretePadic318.place p rho hr CompressedOrientation318.D=0)
    (hHpos:0<ConcretePadic318.place p rho hr (CompressedOrientation318.fH w))
    (hgain:(16:WithTop ℤ)≤ConcretePadic318.place p rho hr (ScalarSource318.fR w/CompressedOrientation318.fH w))
    (n c:ℤ) (tau:LocalGenerator318.E.Point)
    (hH:transport curve_eq (CompressedTranslation318.H S w source)=n • LocalGenerator318.P+tau)
    (htau:tau=0 ∨ tau=GlobalGeneratorPoints318.T 0)
    (hscalar:RawOddAnchorPoints318.ScalarLabel w c) : (p:ℤ)^8∣c := by
  let v:=ConcretePadic318.place p rho hr
  have hmap (x:K):Padic.addValuation (φ x)=v x := by
    exact SourceSplitLog318.valuation_embedding p rho hr x
  obtain ⟨a,ha,haeven⟩:=ScalarLocalValues318.source_fH_even S w source v hD
  obtain ⟨b,hb,hbeven⟩:=ScalarLocalValues318.source_fR_even S w source v
  obtain ⟨r,hrval⟩:=haeven
  obtain ⟨s,hsval⟩:=hbeven
  have hae:a=2*r := by omega
  have hbe:b=2*s := by omega
  have hr1:1≤r := by
    change 0<v (CompressedOrientation318.fH w) at hHpos
    rw [ha] at hHpos
    have hh:0<a:=WithTop.coe_lt_coe.mp hHpos
    omega
  have hrel:16≤b-a := by
    change (16:WithTop ℤ)≤v (ScalarSource318.fR w/CompressedOrientation318.fH w) at hgain
    rw [v.map_div,hb,ha,←WithTop.LinearOrderedAddCommGroup.coe_sub] at hgain
    exact WithTop.coe_le_coe.mp hgain
  have hs1:1≤s := by omega
  have hgap:8≤s-r := by omega
  obtain ⟨hlocalH,hcoordH⟩:=globalMap_H p rho hr S w source
  obtain ⟨yQ,hlocalQ,hcoordQ⟩:=globalMap_scalar p rho hr w c hscalar
  obtain ⟨hDn,hmemH,hlogH⟩:=SplitReciprocalDepth318.affine_depth p hp d
    (φ (CompressedOrientation318.fH w)) (φ (CompressedPoint318.yH w))
    (by rw [hmap]; exact hD) r hr1 (by rw [hmap,ha,hae]) hlocalH
  obtain ⟨hDn',hmemQ,hlogQ⟩:=SplitReciprocalDepth318.affine_depth p hp d
    (φ (ScalarSource318.fR w)) yQ (by rw [hmap]; exact hD) s hs1 (by rw [hmap,hb,hbe]) hlocalQ
  let H:=globalMap p rho hr (transport curve_eq (CompressedTranslation318.H S w source))
  let Q:=globalMap p rho hr (c • LocalGenerator318.P)
  have hmH:H∈formalSubgroup p hp d hDn := by dsimp [H]; rw [hcoordH]; exact hmemH
  have hmQ:Q∈formalSubgroup p hp d hDn := by dsimp [Q]; rw [hcoordQ]; exact hmemQ
  have hLH:Padic.addValuation (logHom p hp d hDn ⟨H,hmH⟩)=(r:ℤ) := by
    simpa only [H,hcoordH] using hlogH
  have hLQ:Padic.addValuation (logHom p hp d hDn ⟨Q,hmQ⟩)=(s:ℤ) := by
    simpa only [Q,hcoordQ] using hlogQ
  have ht:(2:ℤ) • tau=0 := by
    rcases htau with hz|hz
    · rw [hz,two_zsmul]; exact zero_add _
    · rw [hz,two_zsmul]; exact GlobalGeneratorPoints318.double_T 0
  apply TorsionSafeIndex318.torsion_safe_divisibility
    (formalSubgroup p hp d hDn) (logHom p hp d hDn) p Padic.addValuation
    (fun z hz=>by rw [Padic.addValuation.apply (Int.cast_ne_zero.mpr hz),Padic.valuation_intCast])
    (globalMap p rho hr LocalGenerator318.P) H Q (globalMap p rho hr tau) n c hmH hmQ
    _ _ _ r s hLH hLQ 8 hgap
  · dsimp [H]; rw [hH,map_add,map_zsmul]
  · dsimp [Q]; rw [map_zsmul]
  · rw [←map_zsmul,ht,map_zero]

end
end RawSplitScalar318
#print axioms RawSplitScalar318.source_at_place
