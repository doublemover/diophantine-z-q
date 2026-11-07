module
public import AlternateSourceData318
public import SourcePrimarySplitLog318
public import ValuationAddition318
public section
namespace SourceAlternateDomain318
open ConcreteG8Domain (K pair)
open scoped QuadraticAlgebra
open CircuitReplay Raw318FinalReplay CompressedOrientation318 CompressedGlobal318
open ActualLogHom318 ActualLogIdentification318 WeierstrassCurve.Affine
open SourcePrimarySplitLog318
set_option maxHeartbeats 0
noncomputable section
variable (p:ℕ) [Fact p.Prime]
local instance : DecidableEq ℚ_[p] := Classical.decEq _

theorem positive_chart_data (hp:19≤p) (D u v:ℚ_[p])
    (hD:Padic.addValuation D=0) (hc:v^2=1-D*u^4)
    (hdpos:0<Padic.addValuation (v-1)) :
    ∃(_hv:v≠0)(r:ℤ),1≤r ∧ Padic.addValuation v=0 ∧
      (1:WithTop ℤ)≤Padic.addValuation u ∧
      (v-1=0 ∨ (v-1).valuation=4*r) ∧
      (D*u^4=0 ∨ (D*u^4).valuation=4*r) ∧ ‖v-1‖<1 ∧ ‖D*u^4‖<1 := by
  have h2:Padic.addValuation (2:ℚ_[p])=0 := by
    simpa using JTail318.nat_unit p 2 (by decide) (by omega)
  rcases AlternateFormal318.positive_delta Padic.addValuation D u v hD h2 hc hdpos with ⟨hu,hv⟩|⟨r,hr,hu,hd,hv⟩
  · subst u; subst v
    refine ⟨one_ne_zero,1,by norm_num,Padic.addValuation.map_one,?_,?_,?_,?_,?_⟩ <;> simp
  · have hv0:v≠0:=(Padic.addValuation.ne_top_iff).mp (by rw [hv]; simp)
    have hd0:v-1≠0:=(Padic.addValuation.ne_top_iff).mp (by rw [hd]; exact WithTop.coe_ne_top)
    have hdv:(v-1).valuation=4*r := by rw [Padic.addValuation.apply hd0] at hd; exact WithTop.coe_inj.mp hd
    have hw:Padic.addValuation (D*u^4)=((4*r:ℤ):WithTop ℤ) := by
      rw [Padic.addValuation.map_mul,Padic.addValuation.map_pow,hD,hu,zero_add]
      norm_cast
    have hw0:D*u^4≠0:=(Padic.addValuation.ne_top_iff).mp (by rw [hw]; exact WithTop.coe_ne_top)
    have hwv:(D*u^4).valuation=4*r := by rw [Padic.addValuation.apply hw0] at hw; exact WithTop.coe_inj.mp hw
    refine ⟨hv0,r,hr,hv,?_,Or.inr hdv,Or.inr hwv,
      CanonicalRoot318.argument_small p _ r hr hdv,CanonicalRoot318.argument_small p _ r hr hwv⟩
    rw [hu]; exact_mod_cast hr

@[expose] def mappedAlternate (φ:K→+*ℚ_[p]) (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) (j:Fin 4) (hy:RawRootDifference318.v w j≠0) :
    (ReciprocalDouble318.E (φ D)).Point :=
  ShortCurveBaseChange318.pointMap φ D (PrimaryFormal318.point
    (RawRootDifference318.u w j) (RawRootDifference318.v w j) hy (RawRootDifference318.source_curves S w source j))

theorem mappedAlternate_source_point (φ:K→+*ℚ_[p]) (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) (j:Fin 4) (hy:RawRootDifference318.v w j≠0) :
    mappedAlternate p φ S w source j hy=
      ShortCurveBaseChange318.pointMap φ D (RawRootDifference318.V S w source j) := by
  rfl


theorem mappedAlternate_eq (φ:K→+*ℚ_[p]) (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) (j:Fin 4) (hy:RawRootDifference318.v w j≠0) :
    mappedAlternate p φ S w source j hy=ReciprocalDouble318.point (φ D)
      (φ (RawRootDifference318.u w j)) (φ (RawRootDifference318.v w j))
      (fun h=>hy (φ.injective (h.trans φ.map_zero.symm)))
      (by simpa only [map_pow,map_sub,map_one,map_mul] using congrArg φ (RawRootDifference318.source_curves S w source j)) := by
  unfold mappedAlternate
  erw [primary_eq_reciprocal,ShortCurveBaseChange318.pointMap_reciprocal]

theorem source_alternate_domain (hp:19≤p) (φ:K→+*ℚ_[p]) (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) (j:Fin 4)
    (hD:Padic.addValuation (φ D)=0)
    (hdelta:0<Padic.addValuation (φ (RawRootDifference318.v w j)-1)) :
    ∃(hy:RawRootDifference318.v w j≠0)(hDn:‖φ D‖≤1)
      (hmem:mappedAlternate p φ S w source j hy∈formalSubgroup p hp (φ D) hDn)(r:ℤ),
      1≤r ∧ (φ (RawRootDifference318.v w j)-1=0 ∨
        (φ (RawRootDifference318.v w j)-1).valuation=4*r) ∧
      logHom p hp (φ D) hDn ⟨mappedAlternate p φ S w source j hy,hmem⟩=
        -φ (RawRootDifference318.u w j)*JTail318.J p (φ (RawRootDifference318.v w j)-1) := by
  have hc:(φ (RawRootDifference318.v w j))^2=1-φ D*(φ (RawRootDifference318.u w j))^4 := by
    simpa only [map_pow,map_sub,map_one,map_mul] using congrArg φ (RawRootDifference318.source_curves S w source j)
  obtain ⟨hy0,r,hr,hyv,hu,hd,hw,hnear,hsmall⟩:=positive_chart_data p hp _ _ _ hD hc hdelta
  have hy:RawRootDifference318.v w j≠0:=fun h=>hy0 (by rw [h,map_zero])
  obtain ⟨hDn,hy0',hm⟩:=SourceLogDomain318.reciprocal_mem_of_valuation p hp _ _ _ hD hyv hu hc
  have hmem:mappedAlternate p φ S w source j hy∈formalSubgroup p hp (φ D) hDn := by
    rw [mappedAlternate_eq]; exact hm
  refine ⟨hy,hDn,hmem,r,hr,hd,?_⟩
  change logarithm p hp (φ D) (mappedAlternate p φ S w source j hy)=_
  rw [mappedAlternate_eq]
  exact ActualJLog318.logarithm_J p hp _ _ _ _ _ hsmall hnear

end
end SourceAlternateDomain318
#print axioms SourceAlternateDomain318.source_alternate_domain
