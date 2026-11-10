module
public import PELOriginalVertexStratum318
public import PELOriginalOpenEdgeDisjoint318
public section
noncomputable section
namespace PELOriginalEdgeStrata318
open QuaternionicJointPeriodTopology318 PELDirichletHeight318 PELJointNormOneAction318
open PELDirichletSidePairingData318 PELUnlevelledComplexBase318 PELOriginalBaseCompact318
open PELOriginalDirichletPolygon318 PELActualOriginalSideGluing318
open PELOriginalBoundaryAction318 PELOriginalOrbitRelation318 PELOriginalVertexStratum318
open PELOriginalOpenEdgeDisjoint318 PELRealKleinSideTransport318 PELOriginalProjectiveTangents318
set_option maxHeartbeats 2000000

/-- The exact endpoint order of every paired original side, including the
orientation reversals. This is not inferred from an unordered pair equality. -/
theorem paired_endpoint_order : ∀ e : Fin 28,
    (imageStart e=start (partner e) ∧ imageFinish e=finish (partner e)) ∨
    (imageStart e=finish (partner e) ∧ imageFinish e=start (partner e)) := by decide

theorem paired_open_segment (e : Fin 28) (s : ℝ) (hs : 0<s) (hs1 : s<1) :
    ∃ (t : ℝ) (ht : 0<t) (ht1 : t<1),
      segmentPoint (imageStart e) (imageFinish e) s hs.le hs1.le=
        segmentPoint (start (partner e)) (finish (partner e)) t ht.le ht1.le := by
  rcases paired_endpoint_order e with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · refine ⟨s,hs,hs1,?_⟩
    rw [ha,hb]
  · refine ⟨1-s,by linarith,by linarith,?_⟩
    apply Subtype.ext
    apply scaled_injective
    rw [segment_coordinates,segment_coordinates,ha,hb]
    apply Prod.ext <;> simp only [realMix] <;> ring

/-- Complete orbit criterion for points in original open sides. The two
sides must be identical or the LITERAL original partner pair. -/
theorem open_edge_orbit_labels (e f : Fin 28) (s t : ℝ)
    (hs : 0<s) (hs1 : s<1) (ht : 0<t) (ht1 : t<1)
    (h : projection (segmentPoint (start e) (finish e) s hs.le hs1.le).val=
      projection (segmentPoint (start f) (finish f) t ht.le ht1.le).val) :
    e=f ∨ partner e=f := by
  obtain ⟨u,hu⟩ := (projection_eq_iff_unit _ _).mp h.symm
  have hd := orbit_multiplier_one
    (segmentPoint (start e) (finish e) s hs.le hs1.le)
    (segmentPoint (start f) (finish f) t ht.le ht1.le) u hu
  rw [segment_coordinates] at hd
  rcases original_edge_action u e s hs hs1 hd
    (segmentPoint (start e) (finish e) s hs.le hs1.le).val with hi | he
  · left
    have hp := hi.symm.trans hu
    have hc := congrArg (fun τ : HalfPlane => (scaledFirst τ,scaledSecond τ)) hp
    rw [segment_coordinates,segment_coordinates] at hc
    exact open_sides_disjoint e f s t hs hs1 ht ht1 hc
  · right
    obtain ⟨r,hr,hr1,hpair⟩ := paired_open_segment e s hs hs1
    have hp : (segmentPoint (imageStart e) (imageFinish e) s hs.le hs1.le).val=
        (segmentPoint (start f) (finish f) t ht.le ht1.le).val :=
      (actual_unit_side e s hs.le hs1.le).symm.trans (he.symm.trans hu)
    rw [hpair] at hp
    have hc := congrArg (fun τ : HalfPlane => (scaledFirst τ,scaledSecond τ)) hp
    rw [segment_coordinates,segment_coordinates] at hc
    exact open_sides_disjoint (partner e) f r t hr hr1 ht ht1 hc

/-- The entire actual one-dimensional open stratum, not a midpoint sample. -/
@[expose] def EdgeImage (e : Fin 28) : Set UnlevelledBase :=
  {q | ∃ (s : ℝ) (hs : 0<s) (hs1 : s<1),
    projection (segmentPoint (start e) (finish e) s hs.le hs1.le).val=q}

theorem edgeImage_nonempty (e : Fin 28) : (EdgeImage e).Nonempty :=
  ⟨_,1/2,by norm_num,by norm_num,rfl⟩

theorem mem_partner {e : Fin 28} {q : UnlevelledBase} (h : q∈EdgeImage e) :
    q∈EdgeImage (partner e) := by
  obtain ⟨s,hs,hs1,hq⟩ := h
  obtain ⟨t,ht,ht1,hpair⟩ := paired_open_segment e s hs hs1
  have hp : projection (segmentPoint (imageStart e) (imageFinish e) s hs.le hs1.le).val=
      projection (segmentPoint (start e) (finish e) s hs.le hs1.le).val :=
    (congrArg projection (actual_unit_side e s hs.le hs1.le).symm).trans
      (projection_unit (edgeUnit e) _)
  rw [hpair] at hp
  exact ⟨t,ht,ht1,hp.trans hq⟩

theorem edgeImage_partner (e : Fin 28) : EdgeImage e=EdgeImage (partner e) := by
  ext q
  constructor
  · exact mem_partner
  · intro h
    have hh := mem_partner h
    rwa [(partner_involution e).1] at hh

theorem intersecting_edges {e f : Fin 28} {q : UnlevelledBase}
    (he : q∈EdgeImage e) (hf : q∈EdgeImage f) : e=f ∨ partner e=f := by
  obtain ⟨s,hs,hs1,he⟩ := he
  obtain ⟨t,ht,ht1,hf⟩ := hf
  exact open_edge_orbit_labels e f s t hs hs1 ht ht1 (he.trans hf.symm)

@[expose] def edgeClass : Fin 28 → Fin 14 :=
  ![0,0,1,1,2,2,3,3,4,4,5,5,6,6,7,7,8,8,9,9,10,10,11,11,12,12,13,13]
@[expose] def edgeRepresentative : Fin 14 → Fin 28 :=
  ![0,2,4,6,8,10,12,14,16,18,20,22,24,26]

theorem edgeClass_iff : ∀ e f : Fin 28, edgeClass e=edgeClass f ↔ e=f ∨ partner e=f := by decide

theorem edgeRepresentative_class (i : Fin 14) : edgeClass (edgeRepresentative i)=i := by
  fin_cases i <;> rfl

/-- Equality of actual open-stratum subsets is exactly the original paired
edge classification. Nonemptiness is used, so empty sets cannot collapse it. -/
theorem edgeImage_eq_iff (e f : Fin 28) : EdgeImage e=EdgeImage f ↔ edgeClass e=edgeClass f := by
  constructor
  · intro h
    obtain ⟨q,hq⟩ := edgeImage_nonempty e
    exact (edgeClass_iff e f).mpr (intersecting_edges hq (h ▸ hq))
  · intro h
    rcases (edgeClass_iff e f).mp h with rfl | hpair
    · rfl
    · rw [←hpair]
      exact edgeImage_partner e

/-- The range consists of actual subsets of the original arithmetic curve. -/
@[expose] def OpenEdgeStrata : Set (Set UnlevelledBase) := Set.range EdgeImage

@[expose] def edgeEnumeration : Fin 14 ≃ OpenEdgeStrata :=
  Equiv.ofBijective
    (fun i => ⟨EdgeImage (edgeRepresentative i),⟨edgeRepresentative i,rfl⟩⟩)
    ⟨by
      intro i j h
      have he := (edgeImage_eq_iff _ _).mp (congrArg Subtype.val h)
      simpa only [edgeRepresentative_class] using he,
    by
      intro S
      obtain ⟨e,he⟩ := S.property
      refine ⟨edgeClass e,?_⟩
      apply Subtype.ext
      exact ((edgeImage_eq_iff _ _).mpr (edgeRepresentative_class _)).trans he⟩

theorem actual_open_edge_count : Nat.card OpenEdgeStrata=14 := by
  rw [← Nat.card_congr edgeEnumeration]
  simp

theorem distinct_edge_strata_disjoint (i j : Fin 14) (hij : i≠j) :
    Disjoint (EdgeImage (edgeRepresentative i)) (EdgeImage (edgeRepresentative j)) := by
  apply Set.disjoint_left.mpr
  intro q hi hj
  have h := (edgeClass_iff _ _).mpr (intersecting_edges hi hj)
  exact hij (by simpa only [edgeRepresentative_class] using h)
/-- Distinct parameter values on one open side remain distinct in the
ACTUAL arithmetic curve. The paired-edge case is excluded by partner≠self. -/
theorem open_parameter_injective (e : Fin 28) (s t : ℝ)
    (hs : 0<s) (hs1 : s<1) (ht : 0<t) (ht1 : t<1)
    (h : projection (segmentPoint (start e) (finish e) s hs.le hs1.le).val=
      projection (segmentPoint (start e) (finish e) t ht.le ht1.le).val) : s=t := by
  obtain ⟨u,hu⟩ := (projection_eq_iff_unit _ _).mp h.symm
  have hd := orbit_multiplier_one
    (segmentPoint (start e) (finish e) s hs.le hs1.le)
    (segmentPoint (start e) (finish e) t ht.le ht1.le) u hu
  rw [segment_coordinates] at hd
  rcases original_edge_action u e s hs hs1 hd
    (segmentPoint (start e) (finish e) s hs.le hs1.le).val with hi | he
  · have hc := congrArg (fun τ : HalfPlane => (scaledFirst τ,scaledSecond τ)) (hi.symm.trans hu)
    rw [segment_coordinates,segment_coordinates] at hc
    have hp := congrArg (PELOriginalPolygonBoundary318.edgeParameter e) hc
    simpa only [edgeParameter_mix] using hp
  · obtain ⟨r,hr,hr1,hpair⟩ := paired_open_segment e s hs hs1
    have hp := (actual_unit_side e s hs.le hs1.le).symm.trans (he.symm.trans hu)
    rw [hpair] at hp
    have hc := congrArg (fun τ : HalfPlane => (scaledFirst τ,scaledSecond τ)) hp
    rw [segment_coordinates,segment_coordinates] at hc
    exact False.elim ((partner_involution e).2
      (open_sides_disjoint (partner e) e r t hr hr1 ht ht1 hc))

/-- No actual open edge stratum contains an actual vertex image. Thus the
zero- and one-strata are genuinely disjoint on the arithmetic surface. -/
theorem edge_vertex_disjoint (e : Fin 28) : Disjoint (EdgeImage e) VertexImage := by
  apply Set.disjoint_left.mpr
  intro q he hv
  obtain ⟨s,hs,hs1,he⟩ := he
  obtain ⟨v,hv⟩ := hv
  obtain ⟨u,hu⟩ := (projection_eq_iff_unit _ _).mp (hv.trans he.symm)
  have hd := orbit_multiplier_one
    (segmentPoint (start e) (finish e) s hs.le hs1.le)
    (PELOriginalActualVertexGluing318.vertexPoint v) u hu
  rw [segment_coordinates] at hd
  rcases original_edge_action u e s hs hs1 hd
    (segmentPoint (start e) (finish e) s hs.le hs1.le).val with hi | ha
  · have hc := congrArg (fun τ : HalfPlane => (scaledFirst τ,scaledSecond τ)) (hi.symm.trans hu)
    rw [segment_coordinates,PELOriginalActualVertexGluing318.vertexPoint_coordinates] at hc
    exact open_side_not_vertex e v s hs hs1 hc
  · obtain ⟨t,ht,ht1,hpair⟩ := paired_open_segment e s hs hs1
    have hp := (actual_unit_side e s hs.le hs1.le).symm.trans (ha.symm.trans hu)
    rw [hpair] at hp
    have hc := congrArg (fun τ : HalfPlane => (scaledFirst τ,scaledSecond τ)) hp
    rw [segment_coordinates,PELOriginalActualVertexGluing318.vertexPoint_coordinates] at hc
    exact open_side_not_vertex (partner e) v t ht ht1 hc
end PELOriginalEdgeStrata318
