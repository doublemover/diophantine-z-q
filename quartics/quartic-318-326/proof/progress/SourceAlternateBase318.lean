module
public import SourceAlternateDomain318
public import CompressedTranslation318
public section
namespace SourceAlternateBase318
open ConcreteG8Domain (K pair)
open scoped QuadraticAlgebra
open CircuitReplay Raw318FinalReplay CompressedOrientation318 CompressedGlobal318 RawLucasOrientation318
open ActualLogHom318 ActualLogIdentification318 WeierstrassCurve.Affine
set_option maxHeartbeats 0
noncomputable section
variable (p:ℕ) [Fact p.Prime]
local instance : DecidableEq ℚ_[p] := Classical.decEq _

@[expose] def mappedV (φ:K→+*ℚ_[p]) (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) : (ReciprocalDouble318.E (φ D)).Point :=
  ShortCurveBaseChange318.pointMap φ D (CompressedTranslation318.V S w source)

theorem source_xV (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w) :
    xV w=1/fV w := by rw [xV,←(source_products S w source).2]

theorem mappedV_some (φ:K→+*ℚ_[p]) (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) (hs:shift w≠0) :
    mappedV p φ S w source=Point.some (φ (xV w)) (φ (yV w))
      (ShortCurveBaseChange318.nonsingular_map φ D _ _ (source_global_V S w source hs).2.1) := by
  unfold mappedV CompressedTranslation318.V
  rw [dite_eq_right hs]
  erw [ShortCurveBaseChange318.pointMap_some]

theorem mappedV_parameters (φ:K→+*ℚ_[p]) (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) (hs:shift w≠0) :
    zParameter p (φ D) (mappedV p φ S w source)=φ (zV w) ∧
    wParameter p (φ D) (mappedV p φ S w source)=φ (D*(fV w)^2) := by
  rw [mappedV_some p φ S w source hs]
  constructor
  · change -φ (xV w)/φ (yV w)=φ (zV w)
    calc
      _ = φ (-xV w/yV w) := ((map_div₀ φ _ _).trans (congrArg (fun t=>t/φ (yV w)) (map_neg φ _))).symm
      _ = _ := congrArg φ (source_global_V S w source hs).2.2.symm
  · change φ D/(φ (xV w))^2=φ (D*(fV w)^2)
    rw [source_xV S w source]
    erw [map_div₀,map_one,map_mul,map_pow]
    field_simp

/-- The finite literal compressed V acquires its actual log domain and
integral depth from the source curve itself. No depth-parity premise remains. -/
theorem source_V_domain (hp:19≤p) (φ:K→+*ℚ_[p]) (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) (hshift:shift w≠0)
    (hD:Padic.addValuation (φ D)=0) (hf:(2:WithTop ℤ)≤Padic.addValuation (φ (fV w))) :
    ∃(hDn:‖φ D‖≤1)(hmem:mappedV p φ S w source∈formalSubgroup p hp (φ D) hDn)(s:ℤ),
      1≤s ∧ Padic.addValuation (φ (fV w))=(2*s:ℤ) ∧
      (φ (D*(fV w)^2)).valuation=4*s ∧ Padic.addValuation (φ (zV w))=(s:ℤ) ∧
      logHom p hp (φ D) hDn ⟨mappedV p φ S w source,hmem⟩=
        φ (zV w)*CanonicalRoot318.factor p hp (φ (D*(fV w)^2)) := by
  have hf0:fV w≠0 := by
    rw [(source_products S w source).2]
    exact mul_ne_zero (CompressedPoint318.source_fH_ne S w source) (pow_ne_zero 2 hshift)
  have hfφ:φ (fV w)≠0:=fun h=>hf0 (φ.injective (h.trans φ.map_zero.symm))
  have hy0:φ (yV w)≠0:=fun h=>(source_global_V S w source hshift).1 (φ.injective (h.trans φ.map_zero.symm))
  obtain ⟨a,ha⟩:=WithTop.ne_top_iff_exists.mp ((Padic.addValuation.ne_top_iff).mpr hfφ)
  obtain ⟨b,hb⟩:=WithTop.ne_top_iff_exists.mp ((Padic.addValuation.ne_top_iff).mpr hy0)
  have ha2:2≤a := by rw [←ha] at hf; exact WithTop.coe_le_coe.mp hf
  have hx:Padic.addValuation (φ (xV w))=(-a:ℤ) := by
    rw [source_xV S w source]
    erw [map_div₀,map_one,Padic.addValuation.map_div,Padic.addValuation.map_one,←ha]
    norm_cast
    ring
  have hns:=ShortCurveBaseChange318.nonsingular_map φ D _ _ (source_global_V S w source hshift).2.1
  have hc:(φ (yV w))^2=(φ (xV w))^3-φ D*φ (xV w) := by
    have he:=hns.1
    rw [equation_iff] at he
    simpa [ReciprocalDouble318.E,sub_eq_add_neg] using he
  have hab:=ValuationAddition318.ordinate_value Padic.addValuation (φ D) _ _ (-a) b hD hx hb.symm hc (by omega)
  let s:ℤ:= -a-b
  have hs:1≤s := by dsimp [s]; omega
  have has:a=2*s := by dsimp [s]; omega
  have hbs:b= -3*s := by dsimp [s]; omega
  have hz:Padic.addValuation (-φ (xV w)/φ (yV w))=(s:ℤ) := by
    rw [Padic.addValuation.map_div,Padic.addValuation.map_neg,hx,←hb]
    norm_cast
  obtain ⟨hDn,hm⟩:=SourceLogDomain318.affine_mem_of_valuation p hp (φ D) _ _ hD hy0 hc hns s hs
    (by rw [hx]; congr 1; omega) (by rw [hz]; exact_mod_cast hs)
  have hmem:mappedV p φ S w source∈formalSubgroup p hp (φ D) hDn := by
    rw [mappedV_some p φ S w source hshift]; exact hm
  have hw:Padic.addValuation (φ (D*(fV w)^2))=((4*s:ℤ):WithTop ℤ) := by
    erw [map_mul,map_pow,Padic.addValuation.map_mul,Padic.addValuation.map_pow,hD,←ha,has,zero_add]
    norm_cast
    ring
  have hw0:φ (D*(fV w)^2)≠0:=(Padic.addValuation.ne_top_iff).mp (by rw [hw]; exact WithTop.coe_ne_top)
  refine ⟨hDn,hmem,s,hs,by rw [←ha,has],?_,?_,?_⟩
  · rw [Padic.addValuation.apply hw0] at hw
    exact WithTop.coe_inj.mp hw
  · rw [←(mappedV_parameters p φ S w source hshift).1,mappedV_some p φ S w source hshift]
    exact hz
  · rw [logHom_eq_primitive,CanonicalRoot318.primitive,
      (mappedV_parameters p φ S w source hshift).1,(mappedV_parameters p φ S w source hshift).2]

end
end SourceAlternateBase318
#print axioms SourceAlternateBase318.source_V_domain
