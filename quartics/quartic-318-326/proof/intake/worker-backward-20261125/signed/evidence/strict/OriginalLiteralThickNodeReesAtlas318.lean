module
public import OriginalThickCentralReesIso318
public import OriginalThickOuterReesIso318
public import OriginalReesDegreeOneCover318
public section
noncomputable section

namespace OriginalLiteralThickNodeReesAtlas318
open OriginalSplitNodeCoordinates318
open OriginalAffineReesGrading318 OriginalAffineReesBlowup318
open OriginalThickCentralReesChart318 (O I w x y hw oldToNew)
open OriginalThickOuterReesChart318 (a a_mem oldToOuter)
open OriginalReesDegreeOneCover318 (gens span_covers)
open AlgebraicGeometry CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

variable {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
variable (q : R) (d : ℕ) (hq : q ≠ 0)

local instance : Algebra R (OriginalThickCentralReesChart318.B q d) :=
  ((OriginalThickCentralReesChart318.bas q d).comp (algebraMap R (O q d))).toAlgebra
local instance (b : Bool) : Algebra R (OriginalThickOuterReesChart318.C q d b) :=
  ((OriginalThickOuterReesChart318.u q d b).comp (algebraMap R (O q d))).toAlgebra

omit [IsDomain R] [UniqueFactorizationMonoid R] in
@[expose] def select : Option Bool → I q d
  | none => ⟨w q d,hw q d⟩
  | some b => ⟨a q d b,a_mem q d b⟩

omit [IsDomain R] [UniqueFactorizationMonoid R] in
theorem selected : Ideal.span (Set.range (fun b : Option Bool => (select q d b).val)) = I q d := by
  congr 1
  ext z
  constructor
  · rintro ⟨b,rfl⟩
    cases b with
    | none => exact Or.inr (Or.inr rfl)
    | some b =>
      cases b
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
  · intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with rfl | rfl | rfl
    · exact ⟨some true,rfl⟩
    · exact ⟨some false,rfl⟩
    · exact ⟨none,rfl⟩

omit [IsDomain R] [UniqueFactorizationMonoid R] in
/-- This is the genuine three-open projective cover, not pointwise
substitutions on an independently supplied split-node model. -/
@[expose] def atlas : (blowup (I q d)).AffineOpenCover :=
  Proj.affineOpenCoverOfIrrelevantLESpan (grade (I q d))
    (gens (I q d) (Option Bool) (select q d))
    (m:=fun _ => 1) (fun i => generator_grade _ _ (select q d i).property)
    (fun _ => by decide) (span_covers (I q d) (select q d) (selected q d))

include hq in
@[expose] def central :
    Spec (CommRingCat.of (Node (q^d))) ⟶ blowup (I q d) :=
  Spec.map (CommRingCat.ofHom (OriginalThickCentralReesIso318.chartIso q d hq).symm.toRingHom) ≫
    chartMap (I q d) (w q d) (hw q d)

include hq in
@[expose] def outer (b : Bool) :
    Spec (CommRingCat.of (Node q)) ⟶ blowup (I q d) :=
  Spec.map (CommRingCat.ofHom (OriginalThickOuterReesIso318.chartIso q d b hq).symm.toRingHom) ≫
    chartMap (I q d) (a q d b) (a_mem q d b)

include hq in
theorem central_over :
    central q d hq ≫ projection (I q d) = Spec.map (CommRingCat.ofHom (oldToNew q d).toRingHom) := by
  unfold central
  rw [Category.assoc, chart_over, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  change (OriginalThickCentralReesIso318.chartIso q d hq).symm
    (OriginalThickCentralReesChart318.bas q d z) = oldToNew q d z
  rw [← OriginalThickCentralReesIso318.old_reads q d hq z,AlgEquiv.symm_apply_apply]

include hq in
theorem outer_over (b : Bool) :
    outer q d hq b ≫ projection (I q d) = Spec.map (CommRingCat.ofHom (oldToOuter q d b).toRingHom) := by
  unfold outer
  rw [Category.assoc, chart_over, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  change (OriginalThickOuterReesIso318.chartIso q d b hq).symm
    (OriginalThickOuterReesChart318.u q d b z) = oldToOuter q d b z
  rw [← OriginalThickOuterReesIso318.old_reads q d b hq z,AlgEquiv.symm_apply_apply]

include hq in
theorem covers (p : blowup (I q d)) :
    p ∈ Set.range (central q d hq) ∨ ∃ b : Bool, p ∈ Set.range (outer q d hq b) := by
  obtain ⟨b,z,hz⟩ := (atlas q d).openCover.exists_eq p
  cases b with
  | none =>
    left
    let e := (OriginalThickCentralReesIso318.chartIso q d hq).toRingEquiv.toCommRingCatIso
    refine ⟨Spec.map e.hom z,?_⟩
    change (chartMap (I q d) (w q d) (hw q d)) z = p at hz
    change chartMap (I q d) (w q d) (hw q d) ((Spec.map e.hom ≫ Spec.map e.inv) z) = p
    rw [← Spec.map_comp, e.inv_hom_id, Spec.map_id]
    exact hz
  | some b =>
    right
    let e := (OriginalThickOuterReesIso318.chartIso q d b hq).toRingEquiv.toCommRingCatIso
    refine ⟨b, Spec.map e.hom z, ?_⟩
    change (chartMap (I q d) (a q d b) (a_mem q d b)) z = p at hz
    change chartMap (I q d) (a q d b) (a_mem q d b) ((Spec.map e.hom ≫ Spec.map e.inv) z) = p
    rw [← Spec.map_comp, e.inv_hom_id, Spec.map_id]
    exact hz

end OriginalLiteralThickNodeReesAtlas318

#print axioms OriginalLiteralThickNodeReesAtlas318.atlas
#print axioms OriginalLiteralThickNodeReesAtlas318.central_over
#print axioms OriginalLiteralThickNodeReesAtlas318.outer_over
#print axioms OriginalLiteralThickNodeReesAtlas318.covers
