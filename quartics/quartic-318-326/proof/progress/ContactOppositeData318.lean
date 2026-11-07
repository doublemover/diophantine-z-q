module
public import ContactLeafData318
public import SourceAlternatePrecision318
public section
namespace ContactOppositeData318
open ConcreteG8Domain (K pair)
open scoped QuadraticAlgebra
open CircuitReplay Raw318FinalReplay RawDetector318 SourceContact318 RawLucasOrientation318
open CompressedOrientation318 ConcretePadic318 SourcePadic318 SourceSplitLog318
open ContactLeafData318 FiniteContact318
set_option maxHeartbeats 0
noncomputable section
variable (p:ℕ) [Fact p.Prime]

/-- Exact relation between the two actual split embeddings, on every element. -/
theorem opposite_embedding (rho:ℚ_[p]) (hr:rho^2=2) (x:K) :
    phi p (-rho) (negative_root p rho hr) x=phi p rho hr (conj x) := by
  obtain ⟨a,b⟩:=x
  change embedding p (-rho) (negative_root p rho hr) (pair a b)=embedding p rho hr (conj (pair a b))
  rw [conj_pair]
  exact conjugate_embedding p rho hr a b

/-- The opposite actual place is the finite V direction, with at least
 depth2. Neither an orientation nor even-depth premise is supplied. -/
theorem source_opposite_V (rho:ℚ_[p]) (hr:rho^2=2) (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) (hgood:¬p∣contactModulus) (hp41:¬p∣41)
    (hfH:(8:WithTop ℤ)≤place p rho hr (fH w)) (hb:LeafBounds (place p rho hr) S w) :
    shift w≠0 ∧ place p (-rho) (negative_root p rho hr) D=0 ∧
      (2:WithTop ℤ)≤place p (-rho) (negative_root p rho hr) (fV w) := by
  have hp2:=not_dvd_supported p hgood 2 (by norm_num [contactModulus])
  have hp3:=not_dvd_supported p hgood 3 (by norm_num [contactModulus])
  have hp7:=not_dvd_supported p hgood 7 (by norm_num [contactModulus])
  obtain ⟨hk,hD⟩:=source_constant_units p rho hr hgood hp41
  have hpos:0<place p rho hr (fH w):=lt_of_lt_of_le (by norm_num) hfH
  have hs:=RawAlternatePade318.source_shift_nonzero_at_contact S w source (place p rho hr) hk hpos
  obtain ⟨hnH,hnV⟩:=source_norm_tests S w source (place p rho hr) hb.1 hb.2.1
  rw [rational_place] at hnH hnV
  have hop:=source_opposite_at_split p rho hr S w source hp2 hp3 hp7 hp41 hnH hnV
  have ho:place p (-rho) (negative_root p rho hr) (fH w)=0 ∧
      0<place p (-rho) (negative_root p rho hr) (fV w) := by
    rcases hop with h|h
    · exact ⟨h.2.1,h.2.2.2⟩
    · rw [h.1] at hpos; exact (lt_irrefl _ hpos).elim
  have hDopp:place p (-rho) (negative_root p rho hr) D=0:=
    (source_constant_units p (-rho) (negative_root p rho hr) hgood hp41).2
  let v:=place p (-rho) (negative_root p rho hr)
  obtain ⟨s,hsv⟩:=WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr hs)
  have hfv:v (fV w)=((2*s:ℤ):WithTop ℤ) := by
    rw [(source_products S w source).2,v.map_mul,v.map_pow,ho.1,zero_add,←hsv]
    norm_cast
  have hs1:1≤s := by
    have h0:=ho.2
    change 0<v (fV w) at h0
    rw [hfv] at h0
    have hh:0<2*s:=WithTop.coe_lt_coe.mp h0
    omega
  refine ⟨hs,hDopp,?_⟩
  change (2:WithTop ℤ)≤v (fV w)
  rw [hfv]
  exact WithTop.coe_le_coe.mpr (show (2:ℤ)≤2*s by omega)

theorem source_opposite_deltas (rho:ℚ_[p]) (hr:rho^2=2) (S:ℚ) (w:Assignment)
    (hb:LeafBounds (place p rho hr) S w) :
    ∀j,(2:WithTop ℤ)≤Padic.addValuation
      (phi p (-rho) (negative_root p rho hr) (RawRootDifference318.v w j)-1) := by
  intro j
  have he:conj (RawRootDifference318.v w j-1)=AlternateFormal318.leaf S w j := by
    rw [map_sub,map_one,AlternateFormal318.source_leaves]
    rfl
  have hh:=hb.2.2.2.1 j
  rw [←he,conjugate_place] at hh
  have hm:phi p (-rho) (negative_root p rho hr) (RawRootDifference318.v w j)-1=
      phi p (-rho) (negative_root p rho hr) (RawRootDifference318.v w j-1) := by
    rw [map_sub,map_one]
  rw [hm,valuation_embedding]
  exact hh

/-- Every explicit local hypothesis of the actual alternate-log packet is
now supplied by the literal common selected detector leaves. -/
theorem source_alternate_inputs (rho:ℚ_[p]) (hr:rho^2=2) (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) (hgood:¬p∣contactModulus) (hp41:¬p∣41)
    (hfH:(8:WithTop ℤ)≤place p rho hr (fH w)) (hb:LeafBounds (place p rho hr) S w) :
    shift w≠0 ∧ Padic.addValuation (phi p (-rho) (negative_root p rho hr) D)=0 ∧
    (2:WithTop ℤ)≤Padic.addValuation (phi p (-rho) (negative_root p rho hr) (fV w)) ∧
    ∀j,0<Padic.addValuation (phi p (-rho) (negative_root p rho hr) (RawRootDifference318.v w j)-1) := by
  obtain ⟨hs,hD,hV⟩:=source_opposite_V p rho hr S w source hgood hp41 hfH hb
  refine ⟨hs,by rwa [valuation_embedding],by rwa [valuation_embedding],?_⟩
  intro j
  exact lt_of_lt_of_le (by norm_num) (source_opposite_deltas p rho hr S w hb j)

/-- Literal comparison rows compare primary values at the selected place
with alternate values at precisely its conjugate, not an unrelated place. -/
theorem source_mapped_comparisons (rho:ℚ_[p]) (hr:rho^2=2) (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) (hb:LeafBounds (place p rho hr) S w) :
    ∀j,(comparisonDepth j:WithTop ℤ)≤Padic.addValuation
      (phi p rho hr (PrimaryFormal318.ratio w j)-
       phi p (-rho) (negative_root p rho hr) (AlternateSourceData318.rawRatio w j)) := by
  intro j
  rw [opposite_embedding p rho hr (AlternateSourceData318.rawRatio w j),←map_sub,valuation_embedding]
  exact (source_tests S w source (place p rho hr) hb).1 j

theorem source_mapped_beta (rho:ℚ_[p]) (hr:rho^2=2) (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) (hb:LeafBounds (place p rho hr) S w) :
    (4:WithTop ℤ)≤Padic.addValuation (phi p rho hr (L1 w)-(beta w:ℚ_[p])) := by
  have he:phi p rho hr (pair (beta w) 0)=(beta w:ℚ_[p]) := by
    change embedding p rho hr (pair (beta w) 0)=_
    rw [embedding_pair]
    simp
  rw [←he,←map_sub,valuation_embedding]
  exact (source_tests S w source (place p rho hr) hb).2.1

theorem source_mapped_lucas (rho:ℚ_[p]) (hr:rho^2=2) (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) (hb:LeafBounds (place p rho hr) S w) :
    (13:WithTop ℤ)≤Padic.addValuation
      ((phi p rho hr (L3 w))^2-phi p rho hr (L2 w)*(phi p rho hr (L2 w)-2)*
        phi p rho hr (L3 w)*phi p rho hr (L4 w)+
        (phi p rho hr (L2 w)-2)^2*(phi p rho hr (L4 w))^2-1) := by
  have he:phi p rho hr (lucas w)=
      (phi p rho hr (L3 w))^2-phi p rho hr (L2 w)*(phi p rho hr (L2 w)-2)*
        phi p rho hr (L3 w)*phi p rho hr (L4 w)+
        (phi p rho hr (L2 w)-2)^2*(phi p rho hr (L4 w))^2-1 := by
    simp only [lucas,map_sub,map_add,map_pow,map_mul,map_one]
    erw [map_ofNat (phi p rho hr) 2]
  rw [←he,valuation_embedding]
  exact (source_tests S w source (place p rho hr) hb).2.2

end
end ContactOppositeData318
#print axioms ContactOppositeData318.source_alternate_inputs
#print axioms ContactOppositeData318.source_mapped_comparisons
