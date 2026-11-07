module
public import SourceLogDomain318
public import ShortCurveBaseChange318
public import CompressedGlobal318
public import PrimaryFormal318
public section
namespace SourceSplitLog318
open ConcreteG8Domain (K pair)
open scoped QuadraticAlgebra
open CircuitReplay Raw318FinalReplay CompressedOrientation318 RawLucasOrientation318
open ConcretePadic318 SourcePadic318 FiniteContact318
open WeierstrassCurve.Affine ActualLogHom318 ActualLogIdentification318
set_option maxHeartbeats 0
noncomputable section
variable (p:ℕ) [Fact p.Prime]
local instance : DecidableEq ℚ_[p] := Classical.decEq _

abbrev phi (rho:ℚ_[p]) (hr:rho^2=2) : K →+* ℚ_[p] := (embedding p rho hr).toRingHom

theorem valuation_embedding (rho:ℚ_[p]) (hr:rho^2=2) (x:K) :
    Padic.addValuation (phi p rho hr x)=place p rho hr x := by
  obtain ⟨a,b⟩:=x
  change Padic.addValuation (embedding p rho hr (pair a b))=place p rho hr (pair a b)
  rw [place_pair,embedding_pair]

theorem source_constant_units (rho:ℚ_[p]) (hr:rho^2=2)
    (hgood:¬p∣contactModulus) (hp41:¬p∣41) :
    place p rho hr k=0 ∧ place p rho hr D=0 := by
  have h2:=place_nat_unit p rho hr 2 (not_dvd_supported p hgood 2 (by norm_num [contactModulus]))
  have h3:=place_nat_unit p rho hr 3 (not_dvd_supported p hgood 3 (by norm_num [contactModulus]))
  have h7:=place_nat_unit p rho hr 7 (not_dvd_supported p hgood 7 (by norm_num [contactModulus]))
  have h41:=place_nat_unit p rho hr 41 hp41
  exact ⟨(good_constants (place p rho hr) h2 h41).1,(discriminant_units (place p rho hr) h2 h3 h7).2⟩

@[expose] def sourceH (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w) : (ReciprocalDouble318.E D).Point :=
  .some (CompressedPoint318.xH w) (CompressedPoint318.yH w)
    (CompressedGlobal318.source_global_H S w source).2.2.1

@[expose] def mappedH (rho:ℚ_[p]) (hr:rho^2=2) (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) : (ReciprocalDouble318.E (phi p rho hr D)).Point :=
  ShortCurveBaseChange318.pointMap (phi p rho hr) D (sourceH S w source)

theorem mappedH_z (rho:ℚ_[p]) (hr:rho^2=2) (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) :
    zParameter p (phi p rho hr D) (mappedH p rho hr S w source)=phi p rho hr (CompressedPoint318.zH w) := by
  unfold mappedH sourceH
  erw [ShortCurveBaseChange318.pointMap_some]
  change -(phi p rho hr (CompressedPoint318.xH w))/phi p rho hr (CompressedPoint318.yH w)=_
  rw [(CompressedGlobal318.source_global_H S w source).2.2.2]
  exact ((map_div₀ (phi p rho hr) _ _).trans (congrArg (fun t => t / phi p rho hr (CompressedPoint318.yH w)) (map_neg (phi p rho hr) _))).symm

/-- The literal compressed H maps into the actual convergent-log subgroup.
Its actual logarithm has exactly the source depth r, with r at least 4. -/
theorem source_H_log (rho:ℚ_[p]) (hr:rho^2=2) (hp:19≤p)
    (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w)
    (hgood:¬p∣contactModulus) (hp41:¬p∣41)
    (hf:(8:WithTop ℤ)≤place p rho hr (fH w)) :
    ∃(hDn:‖phi p rho hr D‖≤1)
      (hmem:mappedH p rho hr S w source∈formalSubgroup p hp (phi p rho hr D) hDn)
      (r:ℤ),4≤r ∧
      Padic.addValuation (logHom p hp (phi p rho hr D) hDn ⟨mappedH p rho hr S w source,hmem⟩)=r := by
  obtain ⟨hk,hD⟩:=source_constant_units p rho hr hgood hp41
  obtain ⟨hA,r,hr4,hf',hA',hz,hx,hy⟩:=CompressedPoint318.source_formal_depth S w source
    (place p rho hr) hk (by rw [hD]) hf
  let φ:=phi p rho hr
  have hD':Padic.addValuation (φ D)=0 := by rw [valuation_embedding,hD]
  have hy0:φ (CompressedPoint318.yH w)≠0 :=
    fun hh=>(CompressedGlobal318.source_global_H S w source).2.1 (φ.injective (by simpa using hh))
  have he:(φ (CompressedPoint318.yH w))^2=(φ (CompressedPoint318.xH w))^3-φ D*φ (CompressedPoint318.xH w) := by
    simpa only [map_pow,map_sub,map_mul] using congrArg φ (CompressedPoint318.source_curve S w source)
  have hns:(ReciprocalDouble318.E (φ D)).Nonsingular (φ (CompressedPoint318.xH w)) (φ (CompressedPoint318.yH w)) :=
    ShortCurveBaseChange318.nonsingular_map φ D _ _ (CompressedGlobal318.source_global_H S w source).2.2.1
  have hx':Padic.addValuation (φ (CompressedPoint318.xH w))=(-2*r:ℤ) := by rw [valuation_embedding,hx]
  have hz':(1:WithTop ℤ)≤Padic.addValuation (-φ (CompressedPoint318.xH w)/φ (CompressedPoint318.yH w)) := by
    have hez : φ (CompressedPoint318.zH w) = -φ (CompressedPoint318.xH w) / φ (CompressedPoint318.yH w) := by
      calc
        φ (CompressedPoint318.zH w) = φ (-CompressedPoint318.xH w / CompressedPoint318.yH w) := congrArg φ (CompressedGlobal318.source_global_H S w source).2.2.2
        _ = φ (-CompressedPoint318.xH w) / φ (CompressedPoint318.yH w) := map_div₀ φ _ _
        _ = _ := congrArg (fun t => t / φ (CompressedPoint318.yH w)) (map_neg φ _)
    rw [←hez,valuation_embedding,hz]
    exact_mod_cast (show (1:ℤ)≤r by omega)
  obtain ⟨hDn,hm⟩:=SourceLogDomain318.affine_mem_of_valuation p hp (φ D) _ _ hD' hy0 he hns r (by omega) hx' hz'
  have hmem:mappedH p rho hr S w source∈formalSubgroup p hp (φ D) hDn := by
    unfold mappedH sourceH
    erw [ShortCurveBaseChange318.pointMap_some]
    exact hm
  refine ⟨hDn,hmem,r,hr4,?_⟩
  rw [logHom_z_valuation,mappedH_z,valuation_embedding,hz]

end
end SourceSplitLog318
#print axioms SourceSplitLog318.source_H_log
