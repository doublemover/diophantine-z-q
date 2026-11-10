module
public import PELOriginalEdgeStrata318
public import CompactSingletonRegion318
public section
noncomputable section
namespace PELOriginalEdgeCharacteristic318
open Set Topology
open PELOriginalEdgeStrata318 PELOriginalVertexStratum318 PELOriginalActualVertexGluing318
open PELDirichletSidePairingData318 PELUnlevelledComplexBase318
open PELActualOriginalSideGluing318 PELActualPolygonHomeomorph318
open PELRealKleinSideTransport318 PELOriginalProjectiveTangents318
set_option maxHeartbeats 1800000
abbrev ClosedInterval := Set.Icc (-1:ℝ) 1
abbrev OpenInterval := Set.Ioo (-1:ℝ) 1

@[expose] def parameter (x : ℝ) : ℝ := (x+1)/2

theorem parameter_bounds (x : ClosedInterval) : 0≤parameter x.val ∧ parameter x.val≤1 := by
  obtain ⟨hl,hr⟩ := x.property
  dsimp [parameter]
  constructor <;> linarith

theorem parameter_strict (x : OpenInterval) : 0<parameter x.val ∧ parameter x.val<1 := by
  obtain ⟨hl,hr⟩ := x.property
  dsimp [parameter]
  constructor <;> linarith

@[expose] def characteristic (e : Fin 28) (x : ClosedInterval) : UnlevelledBase :=
  projection (segmentPoint (start e) (finish e) (parameter x.val)
    (parameter_bounds x).1 (parameter_bounds x).2).val

theorem characteristic_continuous (e : Fin 28) : Continuous (characteristic e) := by
  have hp : Continuous (fun x : ClosedInterval => parameter x.val) :=
    (continuous_subtype_val.add continuous_const).div_const 2
  have hm : Continuous (fun x : ClosedInterval =>
      realMix (realPoint (vertex (start e))) (realPoint (vertex (finish e)))
        (parameter x.val)) := by
    apply Continuous.prodMk
    · exact ((continuous_const.sub hp).mul continuous_const).add (hp.mul continuous_const)
    · exact ((continuous_const.sub hp).mul continuous_const).add (hp.mul continuous_const)
  exact projection_holomorphic.continuous.comp
    (continuous_subtype_val.comp (continuous_polygonInverse.comp (hm.subtype_mk _)))

theorem characteristic_left (e : Fin 28) :
    characteristic e ⟨-1,by constructor <;> norm_num⟩=projection (vertexPoint (start e)).val := by
  simp only [characteristic,parameter,neg_add_cancel,zero_div,segment_zero]

theorem characteristic_right (e : Fin 28) :
    characteristic e ⟨1,by constructor <;> norm_num⟩=projection (vertexPoint (finish e)).val := by
  norm_num only [characteristic,parameter] 
  rw [segment_one]

@[expose] def intervalInterior : Set ClosedInterval := {x | -1<x.val ∧ x.val<1}

theorem interior_open : IsOpen intervalInterior :=
  isOpen_Ioo.preimage continuous_subtype_val

theorem interior_image (e : Fin 28) : characteristic e '' intervalInterior=EdgeImage e := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    have hp := parameter_strict ⟨x.val,hx⟩
    exact ⟨parameter x.val,hp.1,hp.2,rfl⟩
  · rintro ⟨s,hs,hs1,hsy⟩
    have hl : -1<2*s-1 := by linarith
    have hr : 2*s-1<1 := by linarith
    let x : ClosedInterval := ⟨2*s-1,hl.le,hr.le⟩
    refine ⟨x,⟨hl,hr⟩,?_⟩
    have hp : parameter x.val=s := by dsimp [parameter,x]; ring
    simpa only [characteristic,hp] using hsy

/-- Every boundary parameter lands on an actual original vertex, with no
assumption that the two endpoint vertices remain different in the quotient. -/
theorem boundary_vertex (e : Fin 28) (x : ClosedInterval)
    (hx : x.val=-1 ∨ x.val=1) : characteristic e x∈VertexImage := by
  rcases hx with hl | hr
  · have hxx : x=⟨-1,by constructor <;> norm_num⟩ := Subtype.ext hl
    rw [hxx,characteristic_left]
    exact ⟨start e,rfl⟩
  · have hxx : x=⟨1,by constructor <;> norm_num⟩ := Subtype.ext hr
    rw [hxx,characteristic_right]
    exact ⟨finish e,rfl⟩

theorem interior_singleton (e : Fin 28) (x : ClosedInterval) (hx : x∈intervalInterior)
    (y : ClosedInterval) (h : characteristic e x=characteristic e y) : x=y := by
  have hy : -1<y.val ∧ y.val<1 := by
    by_contra hn
    have hb : y.val=-1 ∨ y.val=1 := by
      obtain ⟨hl,hr⟩ := y.property
      simp only [not_and_or,not_lt] at hn
      rcases hn with hn | hn
      · exact Or.inl (le_antisymm hn hl)
      · exact Or.inr (le_antisymm hr hn)
    have hxE : characteristic e x∈EdgeImage e := by
      rw [←interior_image]
      exact ⟨x,hx,rfl⟩
    have hyV := boundary_vertex e y hb
    rw [←h] at hyV
    exact (Set.disjoint_left.mp (edge_vertex_disjoint e)) hxE hyV
  have hpx := parameter_strict ⟨x.val,hx⟩
  have hpy := parameter_strict ⟨y.val,hy⟩
  have hp := open_parameter_injective e (parameter x.val) (parameter y.val)
    hpx.1 hpx.2 hpy.1 hpy.2 h
  apply Subtype.ext
  dsimp [parameter] at hp
  linarith

/-- The open-side parametrization has inverse continuity in the ACTUAL
arithmetic curve, not just in an abstract interval or finite side graph. -/
theorem interior_embedding (e : Fin 28) :
    IsEmbedding (fun x : intervalInterior => characteristic e x.val) :=
  CompactSingletonRegion318.restriction (characteristic e) (characteristic_continuous e)
    intervalInterior interior_open (interior_singleton e)

@[expose] def intervalInteriorHomeomorph : OpenInterval ≃ₜ intervalInterior where
  toFun x := ⟨⟨x.val,x.property.1.le,x.property.2.le⟩,x.property⟩
  invFun x := ⟨x.val.val,x.property⟩
  left_inv x := rfl
  right_inv x := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

theorem interior_range (e : Fin 28) :
    Set.range (fun x : intervalInterior => characteristic e x.val)=EdgeImage e := by
  rw [←interior_image]
  ext y
  constructor
  · rintro ⟨x,hx⟩; exact ⟨x.val,x.property,hx⟩
  · rintro ⟨x,hx,hxy⟩; exact ⟨⟨x,hx⟩,hxy⟩

@[expose] def originalOpenEdge (e : Fin 28) : OpenInterval ≃ₜ EdgeImage e :=
  intervalInteriorHomeomorph.trans ((interior_embedding e).toHomeomorph.trans
    (Homeomorph.setCongr (interior_range e)))

theorem originalOpenEdge_agrees (e : Fin 28) (x : OpenInterval) :
    (originalOpenEdge e x).val=characteristic e ⟨x.val,x.property.1.le,x.property.2.le⟩ := rfl

/-- The closed interval is exactly the open side together with its two
actual endpoint images. Repeated endpoint images are allowed. -/
theorem characteristic_range (e : Fin 28) :
    Set.range (characteristic e)=EdgeImage e ∪
      {projection (vertexPoint (start e)).val,projection (vertexPoint (finish e)).val} := by
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    by_cases hx : x∈intervalInterior
    · left; rw [←interior_image]; exact ⟨x,hx,rfl⟩
    · right
      have hb : x.val=-1 ∨ x.val=1 := by
        obtain ⟨hl,hr⟩ := x.property
        simp only [intervalInterior,Set.mem_setOf_eq,not_and_or,not_lt] at hx
        rcases hx with hx | hx
        · exact Or.inl (le_antisymm hx hl)
        · exact Or.inr (le_antisymm hr hx)
      rcases hb with hl | hr
      · have hxx : x=⟨-1,by constructor <;> norm_num⟩ := Subtype.ext hl
        rw [hxx,characteristic_left]; simp
      · have hxx : x=⟨1,by constructor <;> norm_num⟩ := Subtype.ext hr
        rw [hxx,characteristic_right]; simp
  · rintro (he | hv)
    · rw [←interior_image] at he
      obtain ⟨x,hx,hxy⟩ := he
      exact ⟨x,hxy⟩
    · simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl
      · exact ⟨_,characteristic_left e⟩
      · exact ⟨_,characteristic_right e⟩
end PELOriginalEdgeCharacteristic318
