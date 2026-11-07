module
public import SourceSelectedCongruences318
public import BetaCongruence318
public section
namespace SourceContactDivisibility318
open CircuitReplay Raw318FinalReplay RawWeights318 RawLucasOrientation318
open ConcretePadic318 FiniteContact318 SourceSplitLog318 ContactLeafData318 SourceLabelData318
set_option maxHeartbeats 0
noncomputable section

@[expose] def rootLabel {w:Assignment} {source:Constraints (stage0 ((3:ℚ)^65536)) w}
    (labels:Labels w source) (j:Fin 4) : ℤ := labels.uLabel j-labels.vLabel j
@[expose] def highTarget {w:Assignment} {source:Constraints (stage0 ((3:ℚ)^65536)) w}
    (labels:Labels w source) : ℤ :=
  (rootLabel labels 2)^2-rootLabel labels 1*(rootLabel labels 1-2)*rootLabel labels 2*rootLabel labels 3+
    (rootLabel labels 1-2)^2*(rootLabel labels 3)^2-1
@[expose] def lowTarget (w:Assignment) {source:Constraints (stage0 ((3:ℚ)^65536)) w}
    (labels:Labels w source) : ℚ := beta w-(rootLabel labels 0:ℚ)

variable (p:ℕ) [Fact p.Prime]

/-- Actual selected source tests and the proved integer-label congruences
 give the two literal target divisibilities; no polynomial relation is assumed. -/
theorem selected_targets (rho:ℚ_[p]) (hr:rho^2=2)
    (w:Assignment) (source:Constraints (stage0 ((3:ℚ)^65536)) w) (labels:Labels w source)
    (hb:LeafBounds (place p rho hr) ((3:ℚ)^65536) w)
    (hcong:∀j,0≤Padic.addValuation (phi p rho hr (PrimaryFormal318.ratio w j)) ∧
      (comparisonDepth j:WithTop ℤ)≤Padic.addValuation
        (phi p rho hr (PrimaryFormal318.ratio w j)-((labels.uLabel j-labels.vLabel j:ℤ):ℚ_[p]))) :
    (p:ℤ)^13∣highTarget labels ∧ (p:ℤ)^4∣(lowTarget w labels).num := by
  have hc1:=hcong 1
  have hc2:=hcong 2
  have hc3:=hcong 3
  have hc0:=hcong 0
  simp only [PrimaryFormal318.ratio,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_succ,Matrix.head_cons,comparisonDepth,Fin.reduceEq,ite_false,ite_true] at hc0 hc1 hc2 hc3
  constructor
  · exact LucasCongruence318.integer_lucas_dvd p
      (phi p rho hr (L2 w)) (phi p rho hr (L3 w)) (phi p rho hr (L4 w))
      (rootLabel labels 1) (rootLabel labels 2) (rootLabel labels 3)
      hc1.1 hc2.1 hc3.1 hc1.2 hc2.2 hc3.2
      (ContactOppositeData318.source_mapped_lucas p rho hr _ w source hb)
  · exact BetaCongruence318.beta_numerator_dvd p (phi p rho hr (L1 w))
      (beta w) (rootLabel labels 0)
      (ContactOppositeData318.source_mapped_beta p rho hr _ w source hb) hc0.2

/-- Complete literal chain0 contact to both actual integer-target orders. -/
theorem source_contact0_divisibility (hp:19≤p)
    (w:Assignment) (source:Constraints (stage0 ((3:ℚ)^65536)) w) (labels:Labels w source)
    (f:ℤ) (j:Fin 5) (hgood:¬p∣contactModulus) (hp17:¬p∣17) (hp41:¬p∣41)
    (hf:rationalPlace p (t0 ((3:ℚ)^65536) w-root j)=f) (hpos:0<f) (hodd:Odd f) :
    (p:ℤ)^13∣highTarget labels ∧ (p:ℤ)^4∣(lowTarget w labels).num := by
  obtain ⟨rho,hr,hR,hb,hcong⟩:=SourceSelectedCongruences318.source_contact0_congruences p hp w source labels
    f j hgood hp17 hp41 hf hpos hodd
  exact selected_targets p rho hr w source labels hb hcong

/-- Complete literal chain1 contact to both actual integer-target orders. -/
theorem source_contact1_divisibility (hp:19≤p)
    (w:Assignment) (source:Constraints (stage0 ((3:ℚ)^65536)) w) (labels:Labels w source)
    (f:ℤ) (j:Fin 5) (hgood:¬p∣contactModulus) (hp17:¬p∣17) (hp41:¬p∣41)
    (hf:rationalPlace p (t1 ((3:ℚ)^65536) w-root j)=f) (hpos:0<f) (hodd:Odd f) :
    (p:ℤ)^13∣highTarget labels ∧ (p:ℤ)^4∣(lowTarget w labels).num := by
  obtain ⟨rho,hr,hR,hb,hcong⟩:=SourceSelectedCongruences318.source_contact1_congruences p hp w source labels
    f j hgood hp17 hp41 hf hpos hodd
  exact selected_targets p rho hr w source labels hb hcong

/-- Complete literal chain2 contact to both actual integer-target orders. -/
theorem source_contact2_divisibility (hp:19≤p)
    (w:Assignment) (source:Constraints (stage0 ((3:ℚ)^65536)) w) (labels:Labels w source)
    (f:ℤ) (j:Fin 5) (hgood:¬p∣contactModulus) (hp17:¬p∣17) (hp41:¬p∣41)
    (hf:rationalPlace p (t2 ((3:ℚ)^65536) w-root j)=f) (hpos:0<f) (hodd:Odd f) :
    (p:ℤ)^13∣highTarget labels ∧ (p:ℤ)^4∣(lowTarget w labels).num := by
  obtain ⟨rho,hr,hR,hb,hcong⟩:=SourceSelectedCongruences318.source_contact2_congruences p hp w source labels
    f j hgood hp17 hp41 hf hpos hodd
  exact selected_targets p rho hr w source labels hb hcong

end
end SourceContactDivisibility318
#print axioms SourceContactDivisibility318.source_contact0_divisibility
#print axioms SourceContactDivisibility318.source_contact1_divisibility
#print axioms SourceContactDivisibility318.source_contact2_divisibility
