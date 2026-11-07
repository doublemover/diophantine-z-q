module
public import SourcePrimaryPrecision318
public import SourceAlternateRatios318
public import RatioIntegrality318
public import ContactOppositeData318
public section
namespace SourceContactCongruences318
open ConcreteG8Domain (K)
open CircuitReplay Raw318FinalReplay CompressedGeneratorBridge318
open LocalGenerator318 GlobalGeneratorPoints318
open SourceSplitLog318 ActualLogHom318 ActualLogIdentification318
open ContactLeafData318 ContactOppositeData318 ConcretePadic318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
variable (p:ℕ) [Fact p.Prime]
local instance : DecidableEq ℚ_[p] := Classical.decEq _

theorem depth_nonnegative (j:Fin 4) : (0:ℤ)≤comparisonDepth j := by
  simp only [comparisonDepth]; split <;> omega

theorem depth_le_sixteen (j:Fin 4) : comparisonDepth j≤16 := by
  simp only [comparisonDepth]; split <;> omega

theorem depth_le_alternate_rate (j:Fin 4) : comparisonDepth j≤AlternateRatioKernel318.rate (AlternateSourceData318.full j) := by
  by_cases hj:j=0 <;> simp [comparisonDepth,AlternateSourceData318.full,AlternateRatioKernel318.rate,hj]

/-- Literal common-place detector leaves force the actual coherent root
labels modulo p^4/p^13. The two analytic families are evaluated at the
correct opposite places, and integrality is proved from neighboring labels.
No formal-group, logarithm, analytic-error or integrality premise remains. -/
theorem selected_label_congruences (rho:ℚ_[p]) (hr:rho^2=2) (hp:19≤p)
    (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w)
    (hgood:¬p∣FiniteContact318.contactModulus) (hp41:¬p∣41)
    (hf:(8:WithTop ℤ)≤place p rho hr (CompressedOrientation318.fH w))
    (hb:LeafBounds (place p rho hr) S w)
    (uLabel vLabel:Fin 4→ℤ) (n:ℤ) (tau:E.Point) (hn:n≠0)
    (hu:∀j,uLabel j • P=transport curve_eq (RawRootDifference318.U S w source j))
    (hv:∀j,vLabel j • P=transport curve_eq (RawRootDifference318.V S w source j))
    (hH:transport curve_eq (CompressedTranslation318.H S w source)=n • P+tau)
    (hV:transport curve_eq (CompressedTranslation318.V S w source)=(n-1) • P+tau)
    (htau:tau=0 ∨ tau=T 0) :
    ∀j,0≤Padic.addValuation (phi p rho hr (PrimaryFormal318.ratio w j)) ∧
      (comparisonDepth j:WithTop ℤ)≤Padic.addValuation
        (phi p rho hr (PrimaryFormal318.ratio w j)-((uLabel j-vLabel j:ℤ):ℚ_[p])) := by
  obtain ⟨hshift,hD,hfV,hdelta⟩:=source_alternate_inputs p rho hr S w source hgood hp41 hf hb
  let φ:=phi p rho hr
  let ψ:=phi p (-rho) (negative_root p rho hr)
  have hleaf:=hb.2.2.1
  have hvalueU:=SourcePrimaryPrecision318.source_primary_ratio_value p rho hr hp S w source hgood hp41
    hf hleaf uLabel n tau hn hu hH htau
  have hvalueV:=SourceAlternateRatios318.source_alternate_ratio_values p hp ψ S w source hshift hD hfV hdelta
    vLabel n tau hv hV htau
  have hcross:=source_mapped_comparisons p rho hr S w source hb
  have hint:∀j,0≤Padic.addValuation (φ (PrimaryFormal318.ratio w j)) ∧
      0≤Padic.addValuation (ψ (AlternateSourceData318.rawRatio w j)) ∧
      0≤Padic.addValuation ((uLabel j:ℚ_[p])/(n:ℚ_[p])) ∧
      0≤Padic.addValuation ((vLabel j:ℚ_[p])/((n-1:ℤ):ℚ_[p])) := by
    intro j
    apply RatioIntegrality318.neighboring_ratios p n (uLabel j) (vLabel j)
    · simpa only [Rat.cast_div,Rat.cast_intCast] using hvalueU j
    · simpa only [Rat.cast_div,Rat.cast_intCast] using (hvalueV j).1
    · exact (WithTop.coe_le_coe.mpr (depth_nonnegative j)).trans (hcross j)
  have hprimary:=SourcePrimaryPrecision318.source_primary_integral_precision p rho hr hp S w source hgood hp41
    hf hleaf uLabel n tau hn hu hH htau (fun j=>by simpa only [Rat.cast_div,Rat.cast_intCast] using (hint j).2.2.1)
  have halt:=SourceAlternateRatios318.source_alternate_integral_precision p hp ψ S w source hshift hD hfV hdelta
    vLabel n tau hv hV htau (fun j=>by simpa only [Rat.cast_div,Rat.cast_intCast] using (hint j).2.2.2)
  have hn1:=GlobalLogRatios318.source_V_label_nonzero S w source hshift n tau htau hV
  intro j
  refine ⟨(hint j).1,?_⟩
  have hLr:(comparisonDepth j:WithTop ℤ)≤Padic.addValuation
      (φ (PrimaryFormal318.ratio w j)-(uLabel j:ℚ_[p])/(n:ℚ_[p])) := by
    rw [Padic.addValuation.map_sub_swap]
    exact (WithTop.coe_le_coe.mpr (depth_le_sixteen j)).trans (by
      simpa [φ] using hprimary j)
  have hMs:(comparisonDepth j:WithTop ℤ)≤Padic.addValuation
      (ψ (AlternateSourceData318.rawRatio w j)-(vLabel j:ℚ_[p])/((n-1:ℤ):ℚ_[p])) := by
    rw [Padic.addValuation.map_sub_swap]
    exact (WithTop.coe_le_coe.mpr (depth_le_alternate_rate j)).trans (by
      simpa only [Rat.cast_div,Rat.cast_intCast] using halt j)
  have hLs:(comparisonDepth j:WithTop ℤ)≤Padic.addValuation
      (φ (PrimaryFormal318.ratio w j)-(vLabel j:ℚ_[p])/((n-1:ℤ):ℚ_[p])) := by
    simpa only [φ,ψ,sub_add_sub_cancel] using Padic.addValuation.map_le_add (hcross j) hMs
  have hur:(n:ℚ_[p])*((uLabel j:ℚ_[p])/(n:ℚ_[p]))=(uLabel j:ℚ_[p]) := by
    field_simp [Int.cast_ne_zero.mpr hn]
  have hvs:((n:ℚ_[p])-1)*((vLabel j:ℚ_[p])/((n-1:ℤ):ℚ_[p]))=
      (uLabel j:ℚ_[p])-((uLabel j-vLabel j:ℤ):ℚ_[p]) := by
    rw [←Int.cast_one,←Int.cast_sub]
    field_simp [Int.cast_ne_zero.mpr hn1]
    push_cast
    ring
  exact LocalSoundness318.label_congruence Padic.addValuation
    (φ (PrimaryFormal318.ratio w j)) ((uLabel j:ℚ_[p])/(n:ℚ_[p]))
    ((vLabel j:ℚ_[p])/((n-1:ℤ):ℚ_[p])) (n:ℚ_[p]) (uLabel j:ℚ_[p])
    ((uLabel j-vLabel j:ℤ):ℚ_[p]) (comparisonDepth j) hur hvs
    (RatioIntegrality318.integer_nonnegative p n)
    (by simpa only [Int.cast_sub,Int.cast_one] using RatioIntegrality318.integer_nonnegative p (n-1)) hLr hLs

end
end SourceContactCongruences318
#print axioms SourceContactCongruences318.selected_label_congruences
