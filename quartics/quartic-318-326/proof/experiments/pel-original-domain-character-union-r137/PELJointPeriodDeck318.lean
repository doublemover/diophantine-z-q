module
public import PELJointPeriodFamily318
public section
noncomputable section
namespace PELJointPeriodDeck318
open QuaternionicRealPeriod318 QuaternionicJointPeriodTopology318 PELJointPeriodFamily318
open PELQuaternionRealRepresentation318 PELPrincipalOrderCoordinates318
open Filter Topology
set_option maxHeartbeats 1200000
abbrev Ambient := ℂ × ComplexVectors
@[expose] def ambient (p : Cover) : Ambient := (p.1,p.2)
@[expose] def deck (a : order) (p : Cover) : Cover :=
  (p.1,p.2+period p.1 (representation a))

@[expose] def deckLinear (M : RealMatrices) : Ambient →ₗ[ℂ] Ambient where
  toFun p := (p.1,fun i => p.2 i+(M i 0:ℂ)*p.1)
  map_add' p q := by
    apply Prod.ext
    · rfl
    · funext i
      change (p.2 i+q.2 i)+(M i 0:ℂ)*(p.1+q.1)=
        (p.2 i+(M i 0:ℂ)*p.1)+(q.2 i+(M i 0:ℂ)*q.1)
      ring
  map_smul' r p := by
    apply Prod.ext
    · rfl
    · funext i
      change r*p.2 i+(M i 0:ℂ)*(r*p.1)=r*(p.2 i+(M i 0:ℂ)*p.1)
      ring
@[expose] def ambientDeck (a : order) (p : Ambient) : Ambient :=
  deckLinear (representation a) p+(0,fun i => (representation a i 1:ℂ))

theorem deck_ambient (a : order) (p : Cover) : ambient (deck a p)=ambientDeck a (ambient p) := by
  apply Prod.ext
  · simp only [ambient,deck,ambientDeck,deckLinear,LinearMap.coe_mk,AddHom.coe_mk,
      Prod.fst_add,add_zero]
  · funext i
    simp only [ambient,deck,ambientDeck,deckLinear,LinearMap.coe_mk,AddHom.coe_mk,
      Prod.snd_add,Pi.add_apply,period,row]
    ring

theorem ambientDeck_analytic (a : order) (p : Ambient) : AnalyticAt ℂ (ambientDeck a) p :=
  ((deckLinear (representation a)).toContinuousLinearMap.analyticAt p).add analyticAt_const

theorem deck_continuous (a : order) : Continuous (deck a) := by
  apply continuous_fst.prodMk
  exact continuous_snd.add (QuaternionicJointPeriodTopology318.continuous_period.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_const))

theorem projection_deck (a : order) (p : Cover) : familyProjection (deck a p)=familyProjection p := by
  apply (projection_eq_iff p.1 (p.2+period p.1 (representation a)) p.2).mpr
  rw [add_sub_cancel_left]
  exact ⟨(a:PELQuaternionAlgebra318.B),a.property,rfl⟩

@[expose] def inverseChart (b : Cover) : OpenPartialHomeomorph Total Cover :=
  familyProjection_localHomeomorph.localInverseAt b

theorem inverseChart_symm (b p : Cover) : (inverseChart b).symm p=familyProjection p := by
  rw [inverseChart,familyProjection_localHomeomorph.localInverseAt_symm]

/-- Every transition is locally translation by one FIXED original order
label, although its period varies holomorphically with the base parameter. -/
theorem inverseChart_deck (b w : Cover) (hw : familyProjection w∈(inverseChart b).source) :
    ∃ a : order, (fun p => inverseChart b (familyProjection p))=ᶠ[𝓝 w] deck a := by
  let v := inverseChart b (familyProjection w)
  have hv : familyProjection v=familyProjection w := by
    have h := (inverseChart b).left_inv hw
    rw [inverseChart_symm] at h
    exact h
  have ht : v.1=w.1 := congrArg baseProjection hv
  have hsame : familyProjection (w.1,v.2)=familyProjection (w.1,w.2) := by
    calc
      familyProjection (w.1,v.2)=familyProjection v := by
        congr 1
        exact Prod.ext ht.symm rfl
      _ = familyProjection (w.1,w.2) := hv
  obtain ⟨a,ha,he⟩ := (projection_eq_iff w.1 v.2 w.2).mp hsame
  let aO : order := ⟨a,ha⟩
  have hcenter : deck aO w=v := by
    apply Prod.ext
    · change w.1=v.1
      exact ht.symm
    · change w.2+period w.1 (representation a)=v.2
      change period w.1 (representation a)=v.2-w.2 at he
      rw [he]
      abel
  have hin : deck aO w∈(inverseChart b).target := by
    rw [hcenter]
    exact (inverseChart b).map_source hw
  refine ⟨aO,?_⟩
  filter_upwards [(deck_continuous aO).continuousAt.eventually
    ((inverseChart b).open_target.mem_nhds hin)] with p hp
  have h := (inverseChart b).right_inv hp
  rw [inverseChart_symm,projection_deck] at h
  exact h
end PELJointPeriodDeck318
