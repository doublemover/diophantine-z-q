module
public import SourceLabelData318
public import SourceContactCongruences318
public import RawSelectedLeafData318
public section
namespace SourceSelectedCongruences318
open CircuitReplay Raw318FinalReplay RawWeights318
open ConcretePadic318 FiniteContact318 SourceSplitLog318 ContactLeafData318 SourceLabelData318
set_option maxHeartbeats 0
noncomputable section
variable (p:ℕ) [Fact p.Prime]

/-- Literal chain0 contact to coherent root-label congruences. All source
point labels can be fixed once using labels_exist, before choosing p. -/
theorem source_contact0_congruences (hp:19≤p)
    (w:Assignment) (source:Constraints (stage0 ((3:ℚ)^65536)) w) (labels:Labels w source)
    (f:ℤ) (j:Fin 5) (hgood:¬p∣contactModulus) (hp17:¬p∣17) (hp41:¬p∣41)
    (hf:rationalPlace p (t0 ((3:ℚ)^65536) w-root j)=f) (hpos:0<f) (hodd:Odd f) :
    ∃(rho:ℚ_[p])(hr:rho^2=2),0<f-5*padicValRat p (A0 ((3:ℚ)^65536) w) ∧
      LeafBounds (place p rho hr) ((3:ℚ)^65536) w ∧
      ∀k,0≤Padic.addValuation (phi p rho hr (PrimaryFormal318.ratio w k)) ∧
        (comparisonDepth k:WithTop ℤ)≤Padic.addValuation
          (phi p rho hr (PrimaryFormal318.ratio w k)-((labels.uLabel k-labels.vLabel k:ℤ):ℚ_[p])) := by
  obtain ⟨rho,hr,hR,hH,hb⟩:=RawSelectedLeafData318.source_selected0 p _ w source f j hgood hp17 hp41 hf hpos hodd
  exact ⟨rho,hr,hR,hb,SourceContactCongruences318.selected_label_congruences p rho hr hp _ w source
    hgood hp41 hH hb labels.uLabel labels.vLabel labels.n labels.tau labels.index_ne
    labels.primary labels.alternate labels.H labels.V labels.torsion⟩

/-- Literal chain1 contact to coherent root-label congruences. All source
point labels can be fixed once using labels_exist, before choosing p. -/
theorem source_contact1_congruences (hp:19≤p)
    (w:Assignment) (source:Constraints (stage0 ((3:ℚ)^65536)) w) (labels:Labels w source)
    (f:ℤ) (j:Fin 5) (hgood:¬p∣contactModulus) (hp17:¬p∣17) (hp41:¬p∣41)
    (hf:rationalPlace p (t1 ((3:ℚ)^65536) w-root j)=f) (hpos:0<f) (hodd:Odd f) :
    ∃(rho:ℚ_[p])(hr:rho^2=2),0<f-5*padicValRat p (A1 ((3:ℚ)^65536) w) ∧
      LeafBounds (place p rho hr) ((3:ℚ)^65536) w ∧
      ∀k,0≤Padic.addValuation (phi p rho hr (PrimaryFormal318.ratio w k)) ∧
        (comparisonDepth k:WithTop ℤ)≤Padic.addValuation
          (phi p rho hr (PrimaryFormal318.ratio w k)-((labels.uLabel k-labels.vLabel k:ℤ):ℚ_[p])) := by
  obtain ⟨rho,hr,hR,hH,hb⟩:=RawSelectedLeafData318.source_selected1 p _ w source f j hgood hp17 hp41 hf hpos hodd
  exact ⟨rho,hr,hR,hb,SourceContactCongruences318.selected_label_congruences p rho hr hp _ w source
    hgood hp41 hH hb labels.uLabel labels.vLabel labels.n labels.tau labels.index_ne
    labels.primary labels.alternate labels.H labels.V labels.torsion⟩

/-- Literal chain2 contact to coherent root-label congruences. All source
point labels can be fixed once using labels_exist, before choosing p. -/
theorem source_contact2_congruences (hp:19≤p)
    (w:Assignment) (source:Constraints (stage0 ((3:ℚ)^65536)) w) (labels:Labels w source)
    (f:ℤ) (j:Fin 5) (hgood:¬p∣contactModulus) (hp17:¬p∣17) (hp41:¬p∣41)
    (hf:rationalPlace p (t2 ((3:ℚ)^65536) w-root j)=f) (hpos:0<f) (hodd:Odd f) :
    ∃(rho:ℚ_[p])(hr:rho^2=2),0<f-5*padicValRat p (A2 ((3:ℚ)^65536) w) ∧
      LeafBounds (place p rho hr) ((3:ℚ)^65536) w ∧
      ∀k,0≤Padic.addValuation (phi p rho hr (PrimaryFormal318.ratio w k)) ∧
        (comparisonDepth k:WithTop ℤ)≤Padic.addValuation
          (phi p rho hr (PrimaryFormal318.ratio w k)-((labels.uLabel k-labels.vLabel k:ℤ):ℚ_[p])) := by
  obtain ⟨rho,hr,hR,hH,hb⟩:=RawSelectedLeafData318.source_selected2 p _ w source f j hgood hp17 hp41 hf hpos hodd
  exact ⟨rho,hr,hR,hb,SourceContactCongruences318.selected_label_congruences p rho hr hp _ w source
    hgood hp41 hH hb labels.uLabel labels.vLabel labels.n labels.tau labels.index_ne
    labels.primary labels.alternate labels.H labels.V labels.torsion⟩

end
end SourceSelectedCongruences318
#print axioms SourceSelectedCongruences318.source_contact0_congruences
#print axioms SourceSelectedCongruences318.source_contact1_congruences
#print axioms SourceSelectedCongruences318.source_contact2_congruences
