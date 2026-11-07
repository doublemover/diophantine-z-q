module
public import InertScalarIndex318
public import ShortCurveBaseChange318
public import RawCompressedLabels318
public import RawOddAnchorPoints318
public section
namespace RawInertScalar318
open ConcreteG8Domain CircuitReplay Raw318FinalReplay CompressedGeneratorBridge318
open WeierstrassCurve.Affine
open scoped QuadraticAlgebra
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
variable (p:ℕ) [Fact p.Prime] (ns:¬∃x:ZMod p,x^2=2)
local notation "L" => InertCompletion318.Field p ns
local notation "φ" => InertCompletion318.embedding p ns
local notation "D0" => ArbitraryInertSeries318.sourceD p ns
local notation "d" => InertIntegers318.embedding p ns D0
local instance : DecidableEq L := Classical.decEq _

/-- Exact actual group base change from the global generator's curve to
 the actual normalized inert completion. -/
@[expose] def globalMap : LocalGenerator318.E.Point→+(ReciprocalDouble318.E d).Point :=
  (ShortCurveBaseChange318.pointMap φ CompressedOrientation318.D).comp
    (transport curve_eq).symm.toAddMonoidHom

theorem globalMap_some (x y:K) (h:LocalGenerator318.E.Nonsingular x y) :
    ∃hlocal:(ReciprocalDouble318.E d).Nonsingular (φ x) (φ y),
      globalMap p ns (Point.some x y h)=Point.some (φ x) (φ y) hlocal := by
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
      globalMap p ns (transport curve_eq (CompressedTranslation318.H S w source))=
        Point.some _ _ hlocal := by
  rw [CompressedTranslation318.H,transport_some]
  obtain ⟨hl,he⟩:=globalMap_some p ns (CompressedPoint318.xH w) (CompressedPoint318.yH w)
    (by simpa only [←curve_eq] using (CompressedGlobal318.source_global_H S w source).2.2.1)
  have hx:φ (CompressedPoint318.xH w)=1/φ (CompressedOrientation318.fH w) := by
    simp only [CompressedPoint318.xH,map_div₀,map_one]
  have hl':(ReciprocalDouble318.E d).Nonsingular (1/φ (CompressedOrientation318.fH w))
      (φ (CompressedPoint318.yH w)) := by simpa only [hx] using hl
  refine ⟨hl',?_⟩
  simpa only [hx] using he

theorem globalMap_scalar (w:Assignment) (c:ℤ) (hlabel:RawOddAnchorPoints318.ScalarLabel w c) :
    ∃(y:L)(hlocal:(ReciprocalDouble318.E d).Nonsingular (1/φ (ScalarSource318.fR w)) y),
      globalMap p ns (c • LocalGenerator318.P)=Point.some _ y hlocal := by
  obtain ⟨y,h,hpt⟩:=hlabel
  obtain ⟨hl,he⟩:=globalMap_some p ns ((RawAnchorNorm318.scalarRoot w)^2) y h
  have hx:φ ((RawAnchorNorm318.scalarRoot w)^2)=1/φ (ScalarSource318.fR w) := by
    simp only [ScalarSource318.fR,map_pow,map_inv₀,one_div,inv_pow,inv_inv]
  have hl':(ReciprocalDouble318.E d).Nonsingular (1/φ (ScalarSource318.fR w)) (φ y) := by simpa only [hx] using hl
  refine ⟨φ y,hl',?_⟩
  rw [hpt,he]
  simp only [hx]

include ns

/-- Complete literal-source inert scalar conclusion with the same actual
 global labels already produced by the global arithmetic packet. The
 coordinate transport, log construction, formality, zero branches and
 depth gain are all discharged. -/
theorem source_scalar_index (hp:19≤p)
    (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w)
    (rval:ℤ) (hr:ConcretePadic318.rationalPlace p (ScalarSource318.r w)=rval)
    (hpos:0<rval) (hodd:Odd rval)
    (n c:ℤ) (tau:LocalGenerator318.E.Point)
    (hH:transport curve_eq (CompressedTranslation318.H S w source)=n • LocalGenerator318.P+tau)
    (htau:tau=0 ∨ tau=GlobalGeneratorPoints318.T 0)
    (hscalar:RawOddAnchorPoints318.ScalarLabel w c) : (p:ℤ)^8∣c := by
  obtain ⟨hlocalH,hcoordH⟩:=globalMap_H p ns S w source
  obtain ⟨yQ,hlocalQ,hcoordQ⟩:=globalMap_scalar p ns w c hscalar
  have ht:(2:ℤ) • tau=0 := by
    rcases htau with hz|hz
    · rw [hz]
      change (2:ℤ) • (0:LocalGenerator318.E.Point)=0
      rw [two_zsmul]; exact zero_add (0:LocalGenerator318.E.Point)
    · rw [hz]
      simpa only [two_zsmul] using GlobalGeneratorPoints318.double_T 0
  apply InertScalarIndex318.source_index_divisibility p ns hp S w source rval hr hpos hodd
    (globalMap p ns LocalGenerator318.P)
    (globalMap p ns (transport curve_eq (CompressedTranslation318.H S w source)))
    (globalMap p ns (c • LocalGenerator318.P)) (globalMap p ns tau) n c
    _ _ _ (φ (CompressedPoint318.yH w)) yQ hlocalH hlocalQ hcoordH hcoordQ
  · rw [hH,map_add,map_zsmul]
  · rw [map_zsmul]
  · rw [←map_zsmul,ht,map_zero]

end
end RawInertScalar318
#print axioms RawInertScalar318.globalMap
#print axioms RawInertScalar318.source_scalar_index
