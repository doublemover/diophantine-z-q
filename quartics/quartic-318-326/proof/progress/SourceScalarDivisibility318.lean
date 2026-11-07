module
public import RawSplitScalar318
public import RawInertScalar318
public import SourceLabelData318
public section
namespace SourceScalarDivisibility318
open CircuitReplay Raw318FinalReplay CompressedGeneratorBridge318 ConcretePadic318
set_option maxHeartbeats 0
noncomputable section
variable (p:ℕ) [Fact p.Prime]

/-- The literal scalar source forces order-eight divisibility at every
p≥19. Split and genuinely inert completions are both realized, and both
actual logarithm homomorphisms are constructed rather than assumed. -/
theorem source_scalar_index (hp:19≤p)
    (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w)
    (rval:ℤ) (hr:rationalPlace p (ScalarSource318.r w)=rval)
    (hpos:0<rval) (hodd:Odd rval)
    (n c:ℤ) (tau:LocalGenerator318.E.Point)
    (hH:transport curve_eq (CompressedTranslation318.H S w source)=n • LocalGenerator318.P+tau)
    (htau:tau=0 ∨ tau=GlobalGeneratorPoints318.T 0)
    (hscalar:RawOddAnchorPoints318.ScalarLabel w c) : (p:ℤ)^8∣c := by
  by_cases hs:∃x:ZMod p,x^2=2
  · have hp2:=InertScalarSource318.not_dvd_small p 2 (by decide) (by omega)
    have hp3:=InertScalarSource318.not_dvd_small p 3 (by decide) (by omega)
    have hp7:=InertScalarSource318.not_dvd_small p 7 (by decide) (by omega)
    have hp11:=InertScalarSource318.not_dvd_small p 11 (by decide) (by omega)
    have hp17:=InertScalarSource318.not_dvd_small p 17 (by decide) (by omega)
    obtain ⟨rho,hrho⟩:=InertHensel318.square_root_lift p hp2 hs
    have hD (t:ℚ_[p]) (ht:t^2=2):place p t ht CompressedOrientation318.D=0 :=
      (SourcePadic318.discriminant_units _
        (SourcePadic318.place_nat_unit p t ht 2 hp2)
        (SourcePadic318.place_nat_unit p t ht 3 hp3)
        (SourcePadic318.place_nat_unit p t ht 7 hp7)).2
    obtain ⟨hleft,hright,hgain⟩:=ScalarPlaceBridge318.split_source p rho hrho S w source rval hr hpos hodd
      hp2 hp3 hp7 hp11 hp17
    rcases hgain with hgain|hgain
    · exact RawSplitScalar318.source_at_place p rho hrho hp S w source (hD rho hrho) hleft hgain
        n c tau hH htau hscalar
    · exact RawSplitScalar318.source_at_place p (-rho) (negative_root p rho hrho) hp S w source
        (hD _ _) hright hgain n c tau hH htau hscalar
  · exact RawInertScalar318.source_scalar_index p hs hp S w source rval hr hpos hodd n c tau hH htau hscalar

/-- One coherent global source witness supplies every global label used by
 the complete split/inert scalar argument. -/
theorem labeled_scalar_index (hp:19≤p)
    (w:Assignment) (source:Constraints (stage0 ((3:ℚ)^65536)) w)
    (labels:SourceLabelData318.Labels w source)
    (rval:ℤ) (hr:rationalPlace p (ScalarSource318.r w)=rval) (hpos:0<rval) (hodd:Odd rval) :
    (p:ℤ)^8∣labels.c :=
  source_scalar_index p hp _ w source rval hr hpos hodd labels.n labels.c labels.tau
    labels.H labels.torsion labels.scalar

end
end SourceScalarDivisibility318
#print axioms SourceScalarDivisibility318.source_scalar_index
#print axioms SourceScalarDivisibility318.labeled_scalar_index
