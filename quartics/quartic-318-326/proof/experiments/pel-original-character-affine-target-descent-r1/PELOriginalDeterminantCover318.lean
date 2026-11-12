module
public import CoveringLiftLocalAction318
public import PELUnlevelledComplexBase318
public section
noncomputable section
namespace PELOriginalDeterminantCover318
open QuaternionicJointPeriodTopology318 PELEffectiveNormOneAction318
open PELUnlevelledComplexBase318 Filter
open scoped Topology
@[expose] def chart (a : HalfPlane) : OpenPartialHomeomorph UnlevelledBase HalfPlane :=
  covering.isLocalHomeomorph.localInverseAt a
@[expose] def baseSet (a : HalfPlane) : Set UnlevelledBase := (chart a).source
lemma section_projection (a : HalfPlane) (q : UnlevelledBase) (hq : q∈baseSet a) :
    projection (chart a q)=q :=
  covering.isLocalHomeomorph.apply_localInverseAt_of_mem hq
lemma exists_shift (a b : HalfPlane) (q : UnlevelledBase)
    (ha : q∈baseSet a) (hb : q∈baseSet b) :
    ∃ g : effectiveGroup,g • chart a q=chart b q := by
  apply covering.apply_eq_iff_mem_orbit.mp
  rw [section_projection a q ha,section_projection b q hb]

/-- The actual unique effective deck transformation on the full overlap. -/
@[expose] def shift (a b : HalfPlane) (q : UnlevelledBase) : effectiveGroup :=
  if h : q∈baseSet a∧q∈baseSet b then (exists_shift a b q h.1 h.2).choose else 1
lemma shift_spec (a b : HalfPlane) (q : UnlevelledBase)
    (ha : q∈baseSet a) (hb : q∈baseSet b) :
    shift a b q • chart a q=chart b q := by
  simp only [shift,dif_pos ⟨ha,hb⟩]
  exact (exists_shift a b q ha hb).choose_spec
lemma shift_self (a : HalfPlane) (q : UnlevelledBase) : shift a a q=1 := by
  by_cases h : q∈baseSet a
  · apply IsCancelSMul.right_cancel _ _ (chart a q)
    rw [shift_spec a a q h h,one_smul]
  · simp [shift,h]
lemma shift_comp (a b c : HalfPlane) (q : UnlevelledBase)
    (ha : q∈baseSet a) (hb : q∈baseSet b) (hc : q∈baseSet c) :
    shift b c q*shift a b q=shift a c q := by
  apply IsCancelSMul.right_cancel _ _ (chart a q)
  rw [mul_smul,shift_spec a b q ha hb,shift_spec b c q hb hc,shift_spec a c q ha hc]

/-- The transition group element is locally constant by genuine covering
lift uniqueness and freeness, not a chosen continuous family of lifts. -/
lemma shift_locally_constant (a b : HalfPlane) (q : UnlevelledBase)
    (ha : q∈baseSet a) (hb : q∈baseSet b) :
    ∀ᶠ r in 𝓝 q,shift a b r=shift a b q := by
  have he : (fun r=>projection (chart a r)) =ᶠ[𝓝 q]
      (fun r=>projection (chart b r)) := by
    filter_upwards [(chart a).open_source.mem_nhds ha,(chart b).open_source.mem_nhds hb]
      with r hra hrb
    rw [section_projection a r hra,section_projection b r hrb]
  obtain ⟨u,hu⟩ := CoveringLiftLocalAction318.exists_action projection covering
    (chart a) (chart b) q ((chart a).continuousAt ha) ((chart b).continuousAt hb) he
  have huq : u=shift a b q := by
    apply IsCancelSMul.right_cancel _ _ (chart a q)
    rw [shift_spec a b q ha hb]
    exact hu.self_of_nhds.symm
  filter_upwards [hu,(chart a).open_source.mem_nhds ha,
    (chart b).open_source.mem_nhds hb] with r hr hra hrb
  rw [←huq]
  apply IsCancelSMul.right_cancel _ _ (chart a r)
  rw [shift_spec a b r hra hrb]
  exact hr
end PELOriginalDeterminantCover318
