module
public import SourceSplitLog318
public section
namespace SourcePrimarySplitLog318
open ConcreteG8Domain (K pair)
open scoped QuadraticAlgebra
open CircuitReplay Raw318FinalReplay CompressedOrientation318 RawLucasOrientation318
open ConcretePadic318 SourceSplitLog318 PrimaryFormal318
open WeierstrassCurve.Affine ActualLogHom318 ActualLogIdentification318
set_option maxHeartbeats 0
noncomputable section
variable (p:ℕ) [Fact p.Prime]
local instance : DecidableEq ℚ_[p] := Classical.decEq _

theorem primary_eq_reciprocal (u v:K) (hv:v≠0) (hc:v^2=1-D*u^4) :
    PrimaryFormal318.point u v hv hc=ReciprocalDouble318.point D u v hv hc := by
  by_cases hu:u=0
  · simp only [PrimaryFormal318.point,ReciprocalDouble318.point,dite_eq_left hu]
    rfl
  · simp only [PrimaryFormal318.point,ReciprocalDouble318.point,dite_eq_right hu]
    rfl

theorem primary_z (u v:K) (hv:v≠0) (hc:v^2=1-D*u^4) :
    ShortCurveBaseChange318.z D (PrimaryFormal318.point u v hv hc)= -u/v := by
  by_cases hu:u=0
  · subst u
    simp [PrimaryFormal318.point,ShortCurveBaseChange318.z]
  · simp only [PrimaryFormal318.point,dite_eq_right hu,ShortCurveBaseChange318.z]
    field_simp [hu,hv]

@[expose] def mappedPrimary (rho:ℚ_[p]) (hr:rho^2=2) (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) (j:Fin 4) (hy:y w j≠0) :
    (ReciprocalDouble318.E (phi p rho hr D)).Point :=
  ShortCurveBaseChange318.pointMap (phi p rho hr) D
    (PrimaryFormal318.point (u w j) (y w j) hy (source_curves S w source j))

theorem mappedPrimary_z (rho:ℚ_[p]) (hr:rho^2=2) (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) (j:Fin 4) (hy:y w j≠0) :
    zParameter p (phi p rho hr D) (mappedPrimary p rho hr S w source j hy)=phi p rho hr (z w j) := by
  have hz (P:(ReciprocalDouble318.E (phi p rho hr D)).Point) : zParameter p (phi p rho hr D) P = ShortCurveBaseChange318.z (phi p rho hr D) P := by
    cases P <;> rfl
  rw [hz]
  change ShortCurveBaseChange318.z (phi p rho hr D)
    (ShortCurveBaseChange318.pointMap (phi p rho hr) D
      (PrimaryFormal318.point (u w j) (y w j) hy (source_curves S w source j)))=_
  erw [ShortCurveBaseChange318.z_map,primary_z]
  rfl

/-- Literal primary points lie in the actual logarithm subgroup, for both
ordinate signs and the identity branch. The exact ratio here is a parameter
ratio; it is not asserted to be a logarithm ratio. -/
theorem source_primary_log (rho:ℚ_[p]) (hr:rho^2=2) (hp:19≤p)
    (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w)
    (hgood:¬p∣FiniteContact318.contactModulus) (hp41:¬p∣41)
    (hf:(8:WithTop ℤ)≤place p rho hr (fH w)) (j:Fin 4)
    (hleaf:(2:WithTop ℤ)≤place p rho hr (leaf S w j)) :
    ∃(hy:y w j≠0) (hDn:‖phi p rho hr D‖≤1)
      (hmem:mappedPrimary p rho hr S w source j hy∈formalSubgroup p hp (phi p rho hr D) hDn),
      (mappedPrimary p rho hr S w source j hy=0 ↔u w j=0) ∧
      zParameter p (phi p rho hr D) (mappedPrimary p rho hr S w source j hy)=
        phi p rho hr (ratio w j)*zParameter p (phi p rho hr D) (mappedH p rho hr S w source) ∧
      Padic.addValuation (logHom p hp (phi p rho hr D) hDn
        ⟨mappedPrimary p rho hr S w source j hy,hmem⟩)=place p rho hr (z w j) := by
  obtain ⟨hk,hD⟩:=source_constant_units p rho hr hgood hp41
  obtain ⟨hy,hzero,hyv,hzv,hzr,hfinite⟩:=source_primary S w source (place p rho hr) hk hD hf j hleaf
  have hu:(1:WithTop ℤ)≤place p rho hr (u w j) :=
    square_depth (place p rho hr) _ (by rwa [←source_leaves S w source j])
  let φ:=phi p rho hr
  have hD':Padic.addValuation (φ D)=0 := by rw [valuation_embedding,hD]
  have hy':Padic.addValuation (φ (y w j))=0 := by rw [valuation_embedding,hyv]
  have hu':(1:WithTop ℤ)≤Padic.addValuation (φ (u w j)) := by rwa [valuation_embedding]
  have hc:(φ (y w j))^2=1-φ D*(φ (u w j))^4 := by
    simpa only [map_pow,map_sub,map_one,map_mul] using congrArg φ (source_curves S w source j)
  obtain ⟨hDn,hy0,hm⟩:=SourceLogDomain318.reciprocal_mem_of_valuation p hp (φ D) (φ (u w j)) (φ (y w j)) hD' hy' hu' hc
  have hmem:mappedPrimary p rho hr S w source j hy∈formalSubgroup p hp (φ D) hDn := by
    unfold mappedPrimary
    erw [primary_eq_reciprocal,ShortCurveBaseChange318.pointMap_reciprocal]
    exact hm
  refine ⟨hy,hDn,hmem,?_,?_,?_⟩
  · change ShortCurveBaseChange318.pointMap φ D _=0 ↔_
    erw [←ShortCurveBaseChange318.pointMap_zero φ D,
      (ShortCurveBaseChange318.pointMap_injective φ D).eq_iff]
    exact hzero
  · rw [mappedPrimary_z,mappedH_z,hzr]
    exact map_mul φ _ _
  · rw [logHom_z_valuation,mappedPrimary_z,valuation_embedding]

/-- One actual logarithm subgroup simultaneously contains H and all four
literal primary points. All memberships share the very same D and norm proof. -/
theorem source_split_log_data (rho:ℚ_[p]) (hr:rho^2=2) (hp:19≤p)
    (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w)
    (hgood:¬p∣FiniteContact318.contactModulus) (hp41:¬p∣41)
    (hf:(8:WithTop ℤ)≤place p rho hr (fH w))
    (hleaf:∀j,(2:WithTop ℤ)≤place p rho hr (leaf S w j)) :
    ∃(hDn:‖phi p rho hr D‖≤1)
      (hH:mappedH p rho hr S w source∈formalSubgroup p hp (phi p rho hr D) hDn)
      (r:ℤ), 4≤r ∧ place p rho hr (fH w)=(2*r:ℤ) ∧
      Padic.addValuation (logHom p hp (phi p rho hr D) hDn
        ⟨mappedH p rho hr S w source,hH⟩)=r ∧
      ∀j,∃(hy:y w j≠0)
        (hU:mappedPrimary p rho hr S w source j hy∈formalSubgroup p hp (phi p rho hr D) hDn),
        (mappedPrimary p rho hr S w source j hy=0 ↔u w j=0) ∧
        zParameter p (phi p rho hr D) (mappedPrimary p rho hr S w source j hy)=
          phi p rho hr (ratio w j)*zParameter p (phi p rho hr D) (mappedH p rho hr S w source) ∧
        Padic.addValuation (logHom p hp (phi p rho hr D) hDn
          ⟨mappedPrimary p rho hr S w source j hy,hU⟩)=place p rho hr (z w j) := by
  obtain ⟨hDn,hH,r,hr4,hrlog⟩:=source_H_log p rho hr hp S w source hgood hp41 hf
  obtain ⟨hk,hD⟩:=source_constant_units p rho hr hgood hp41
  obtain ⟨hA,s,hs4,hfs,hsA,hsz,hsx,hsy⟩:=CompressedPoint318.source_formal_depth S w source
    (place p rho hr) hk (by rw [hD]) hf
  have hsr:s=r := by
    rw [logHom_z_valuation,mappedH_z,valuation_embedding,hsz] at hrlog
    exact WithTop.coe_inj.mp hrlog
  subst s
  refine ⟨hDn,hH,r,hr4,hfs,hrlog,?_⟩
  intro j
  obtain ⟨hy,hDn',hU,hzero,hz,hlog⟩:=source_primary_log p rho hr hp S w source hgood hp41 hf j (hleaf j)
  exact ⟨hy,hU,hzero,hz,hlog⟩

end
end SourcePrimarySplitLog318
#print axioms SourcePrimarySplitLog318.source_primary_log

#print axioms SourcePrimarySplitLog318.source_split_log_data
