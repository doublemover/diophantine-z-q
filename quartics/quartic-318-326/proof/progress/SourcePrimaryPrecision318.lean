module
public import SourcePrimaryRatios318
public import FormalLogDepth318
public section
namespace SourcePrimaryPrecision318
open ConcreteG8Domain CircuitReplay Raw318FinalReplay CompressedGeneratorBridge318
open LocalGenerator318 GlobalGeneratorPoints318 WeierstrassCurve.Affine
open SourceSplitLog318 SourcePrimarySplitLog318 ActualLogHom318 ActualLogIdentification318
open CompressedOrientation318
open scoped QuadraticAlgebra
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
variable (p:ℕ) [Fact p.Prime]
local instance : DecidableEq ℚ_[p] := Classical.decEq _

theorem source_primary_integral_precision (rho:ℚ_[p]) (hr:rho^2=2) (hp:19≤p)
    (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w)
    (hgood:¬p∣FiniteContact318.contactModulus) (hp41:¬p∣41)
    (hf:(8:WithTop ℤ)≤ConcretePadic318.place p rho hr (fH w))
    (hleaf:∀j,(2:WithTop ℤ)≤ConcretePadic318.place p rho hr (PrimaryFormal318.leaf S w j))
    (uLabel:Fin 4→ℤ) (n:ℤ) (tau:E.Point) (hn:n≠0)
    (hlabels:∀j,uLabel j • P=transport curve_eq (RawRootDifference318.U S w source j))
    (hanchor:transport curve_eq (CompressedTranslation318.H S w source)=n • P+tau)
    (htau:tau=0 ∨ tau=T 0)
    (hi:∀j,0≤Padic.addValuation ((((uLabel j:ℚ)/(n:ℚ)):ℚ_[p]))) :
    ∀j,(16:WithTop ℤ)≤Padic.addValuation
      ((((uLabel j:ℚ)/(n:ℚ)):ℚ_[p])-phi p rho hr (PrimaryFormal318.ratio w j)) := by
  obtain ⟨hDn,hH,s,hs,hlogH,hdata⟩:=SourcePrimaryRatios318.source_primary_exact_ratios p rho hr hp S w source
    hgood hp41 hf hleaf uLabel n tau hn hlabels hanchor htau
  obtain ⟨hk,hDu⟩:=source_constant_units p rho hr hgood hp41
  have hDu':Padic.addValuation (phi p rho hr CompressedOrientation318.D)=0 := by rw [valuation_embedding,hDu]
  have hzH:zParameter p (phi p rho hr CompressedOrientation318.D) (mappedH p rho hr S w source)≠0 := by
    apply (Padic.addValuation.ne_top_iff).mp
    rw [←logHom_z_valuation p hp _ hDn ⟨_,hH⟩,hlogH]
    exact WithTop.coe_ne_top
  intro j
  obtain ⟨hy,hU,hratio⟩:=hdata j
  obtain ⟨hy',hDn',hU',hzero,hparam,hval⟩:=source_primary_log p rho hr hp S w source hgood hp41 hf j (hleaf j)
  have hpar:zParameter p (phi p rho hr CompressedOrientation318.D) (mappedPrimary p rho hr S w source j hy)/
      zParameter p (phi p rho hr CompressedOrientation318.D) (mappedH p rho hr S w source)=phi p rho hr (PrimaryFormal318.ratio w j) := by
    rw [hparam,mul_div_cancel_right₀ _ hzH]
  have he:=FormalLogDepth318.integral_first_order p hp (phi p rho hr CompressedOrientation318.D) hDn hDu'
    ⟨mappedPrimary p rho hr S w source j hy,hU⟩ ⟨mappedH p rho hr S w source,hH⟩ s (by omega) hlogH
    (by rw [hratio]; exact hi j)
  rw [hratio,hpar] at he
  exact (show (16:WithTop ℤ)≤((4*s:ℤ):WithTop ℤ) by exact WithTop.coe_le_coe.mpr (show (16:ℤ)≤4*s by omega)).trans he

/-- The literal primary parameter quotient and the rational global-label
 quotient have identical valuation, before any integrality bootstrap. -/
theorem source_primary_ratio_value (rho:ℚ_[p]) (hr:rho^2=2) (hp:19≤p)
    (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w)
    (hgood:¬p∣FiniteContact318.contactModulus) (hp41:¬p∣41)
    (hf:(8:WithTop ℤ)≤ConcretePadic318.place p rho hr (fH w))
    (hleaf:∀j,(2:WithTop ℤ)≤ConcretePadic318.place p rho hr (PrimaryFormal318.leaf S w j))
    (uLabel:Fin 4→ℤ) (n:ℤ) (tau:E.Point) (hn:n≠0)
    (hlabels:∀j,uLabel j • P=transport curve_eq (RawRootDifference318.U S w source j))
    (hanchor:transport curve_eq (CompressedTranslation318.H S w source)=n • P+tau)
    (htau:tau=0 ∨ tau=T 0) :
    ∀j,Padic.addValuation (phi p rho hr (PrimaryFormal318.ratio w j))=
      Padic.addValuation ((((uLabel j:ℚ)/(n:ℚ)):ℚ_[p])) := by
  obtain ⟨hDn,hH,s,hs,hlogH,hdata⟩:=SourcePrimaryRatios318.source_primary_exact_ratios p rho hr hp S w source
    hgood hp41 hf hleaf uLabel n tau hn hlabels hanchor htau
  have hzH:zParameter p (phi p rho hr CompressedOrientation318.D) (mappedH p rho hr S w source)≠0 := by
    apply (Padic.addValuation.ne_top_iff).mp
    rw [←logHom_z_valuation p hp _ hDn ⟨_,hH⟩,hlogH]
    exact WithTop.coe_ne_top
  intro j
  obtain ⟨hy,hU,hratio⟩:=hdata j
  obtain ⟨hy',hDn',hU',hzero,hparam,hval⟩:=source_primary_log p rho hr hp S w source hgood hp41 hf j (hleaf j)
  have he:=FormalLogDepth318.ratio_valuation p hp (phi p rho hr CompressedOrientation318.D) hDn
    ⟨mappedPrimary p rho hr S w source j hy,hU⟩ ⟨mappedH p rho hr S w source,hH⟩
  rw [hratio,hparam,mul_div_cancel_right₀ _ hzH] at he
  exact he.symm

end
end SourcePrimaryPrecision318
#print axioms SourcePrimaryPrecision318.source_primary_integral_precision
#print axioms SourcePrimaryPrecision318.source_primary_ratio_value
