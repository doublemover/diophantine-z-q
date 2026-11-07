module
public import SourceAlternateBase318
public section
namespace SourceAlternatePrecision318
open ConcreteG8Domain (K pair)
open scoped QuadraticAlgebra
open CircuitReplay Raw318FinalReplay CompressedOrientation318 CompressedGlobal318
open ActualLogHom318 ActualLogIdentification318 SourceAlternateBase318 SourceAlternateDomain318
open AlternateSourceData318 AlternateRatioKernel318
set_option maxHeartbeats 0
noncomputable section
variable (p:ℕ) [Fact p.Prime]
local instance : DecidableEq ℚ_[p] := Classical.decEq _

/-- The actual mapped source numerator and denominator logarithms approximate
all four stored alternate quotients, with their different literal rates.
Only source equations and local source-value tests are retained. -/
theorem source_alternate_precision (hp:19≤p) (φ:K→+*ℚ_[p]) (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) (hshift:shift w≠0)
    (hD:Padic.addValuation (φ D)=0) (hf:(2:WithTop ℤ)≤Padic.addValuation (φ (fV w)))
    (hdelta:∀j,0<Padic.addValuation (φ (RawRootDifference318.v w j)-1)) :
    ∃(hDn:‖φ D‖≤1)(hV:mappedV p φ S w source∈formalSubgroup p hp (φ D) hDn)(s:ℤ),
      1≤s ∧ Padic.addValuation (φ (fV w))=(2*s:ℤ) ∧
      Padic.addValuation (logHom p hp (φ D) hDn ⟨mappedV p φ S w source,hV⟩)=(s:ℤ) ∧
      ∀j,∃(hy:RawRootDifference318.v w j≠0)
        (hU:mappedAlternate p φ S w source j hy∈formalSubgroup p hp (φ D) hDn)(r:ℤ),
        1≤r ∧ (φ (RawRootDifference318.v w j)-1=0 ∨
          (φ (RawRootDifference318.v w j)-1).valuation=4*r) ∧
        Padic.addValuation (φ (RawRootDifference318.u w j)/φ (zV w))+
          ((min (rate (full j)*r) (16*s):ℤ):WithTop ℤ)≤
          Padic.addValuation (logHom p hp (φ D) hDn ⟨mappedAlternate p φ S w source j hy,hU⟩/
            logHom p hp (φ D) hDn ⟨mappedV p φ S w source,hV⟩-φ (rawRatio w j)) := by
  obtain ⟨hDn,hV,s,hs,hfs,hws,hzs,hlogV⟩:=source_V_domain p hp φ S w source hshift hD hf
  refine ⟨hDn,hV,s,hs,hfs,?_,?_⟩
  · rw [hlogV,Padic.addValuation.map_mul,
      CanonicalRoot318.factor_unit p hp _ s hs (Or.inr hws),add_zero,hzs]
  · intro j
    obtain ⟨hy,hDn',hU,r,hr,hdr,hlogU⟩:=source_alternate_domain p hp φ S w source j hD (hdelta j)
    refine ⟨hy,hU,r,hr,hdr,?_⟩
    rw [hlogU,hlogV,mapped_ratio p φ S w source hshift j]
    exact mixed_ratio_precision p hp (full j) _ _ _ _ r s hr hs hdr (Or.inr hws)

/-- The separate zero-denominator branch is represented by actual identity
points. It imposes no false constraint on the stored quotient variables. -/
theorem source_identity_points (φ:K→+*ℚ_[p]) (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) (hs:shift w=0) :
    mappedV p φ S w source=0 ∧
    ∀j (hy:RawRootDifference318.v w j≠0),mappedAlternate p φ S w source j hy=0 := by
  constructor
  · unfold mappedV CompressedTranslation318.V
    erw [dite_eq_left hs,ShortCurveBaseChange318.pointMap_zero]
  · intro j hy
    unfold mappedAlternate PrimaryFormal318.point
    erw [dite_eq_left (source_identity S w source hs j),ShortCurveBaseChange318.pointMap_zero]

end
end SourceAlternatePrecision318
#print axioms SourceAlternatePrecision318.source_alternate_precision

#print axioms SourceAlternatePrecision318.source_identity_points
