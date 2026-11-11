module
public import ContactOriginalCohomologyCoordinates318
public section
noncomputable section
namespace ContactOriginalLaurentBoundary318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalLineBothCharts318 ContactOriginalWholeRestriction318
open ContactWholeOpenSectionRestriction318 ContactOriginalRestrictionCoordinates318
open ContactOriginalLaurentCoordinates318 ContactOriginalCohomologyCoordinates318
open LaurentVectorFiltration318
set_option maxHeartbeats 750000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Equality reindexing preserves the actual negative exponent filtration. -/
lemma reindex_negative {m n : ℕ} (h : m = n) (v : V ℚ m) :
    OriginalFiniteBasisBaseChange318.reindex (A:=LaurentPolynomial ℚ) h v ∈ negative ↔
      v ∈ negative := by
  subst n
  rfl

variable (c : Fin 4 → ℚˣ) (L : Line (ContactProjectiveModel318.model c))

/-- The square transition's negative image is exactly the old rectangular
comparison's image. Its rank equality is proved, not newly assumed. -/
lemma negative_image :
    (negative.map (LaurentTransitionBounds318.underlying (transition c L))) =
    negative.map ((rawTransition c L).toLinearMap.restrictScalars ℚ) := by
  ext v
  constructor
  · rintro ⟨w,hw,hv⟩
    refine ⟨(OriginalFiniteBasisBaseChange318.reindex (A:=A) (rank_eq c L)).symm w,?_,hv⟩
    have h := reindex_negative (rank_eq c L)
      ((OriginalFiniteBasisBaseChange318.reindex (A:=A) (rank_eq c L)).symm w)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.mp hw
  · rintro ⟨w,hw,hv⟩
    refine ⟨OriginalFiniteBasisBaseChange318.reindex (A:=A) (rank_eq c L) w,
      (reindex_negative (rank_eq c L) w).mpr hw,?_⟩
    change rawTransition c L
      ((OriginalFiniteBasisBaseChange318.reindex (A:=A) (rank_eq c L)).symm
        (OriginalFiniteBasisBaseChange318.reindex (A:=A) (rank_eq c L) w)) = v
    rw [LinearEquiv.symm_apply_apply]
    exact hv

/-- The old actual derived boundary vanishes exactly on a difference of
the SAME old finite and infinity restrictions, in their proved coordinates. -/
lemma zero_iff (v : V ℚ (finiteRank c L)) :
    boundaryLinear c L v = 0 ↔
      ∃ (a : finiteSections c L) (b : infinitySections c L),
        coordinates c L (finiteRestriction c L a) -
          coordinates c L (infinityRestriction c L b) = v := by
  have hk := MayerVietorisSectionKernel318.sectionBoundary_kernel
    (OriginalLineRestrictionAdditive318.additive L)
    (finiteOpen c) (infinityOpen c) (cover c) ((overlapCoordinates c L).symm v)
  change boundaryLinear c L v = 0 ↔
    ∃ (a : Γ(L.object,finiteOpen c)) (b : Γ(L.object,infinityOpen c)),
      L.object.presheaf.map (homOfLE inf_le_left :
        finiteOpen c ⊓ infinityOpen c ⟶ finiteOpen c).op a -
      L.object.presheaf.map (homOfLE inf_le_right :
        finiteOpen c ⊓ infinityOpen c ⟶ infinityOpen c).op b =
          (overlapCoordinates c L).symm v at hk
  rw [hk]
  constructor
  · rintro ⟨a,b,hab⟩
    refine ⟨(finiteSectionsEquiv c L).symm a,(infinitySectionsEquiv c L).symm b,?_⟩
    have he := congrArg (overlapCoordinates c L) hab
    simpa only [map_sub,finite_res,infinity_res,AddEquiv.apply_symm_apply] using he
  · rintro ⟨a,b,hab⟩
    refine ⟨finiteSectionsEquiv c L a,infinitySectionsEquiv c L b,?_⟩
    apply (overlapCoordinates c L).injective
    simpa only [map_sub,finite_res,infinity_res,AddEquiv.symm_apply_apply,
      AddEquiv.apply_symm_apply] using hab

/-- Exact geometric-to-Laurent kernel comparison, including the original
minus sign of Mayer-Vietoris and the actual whole infinity-chart image. -/
lemma kernel_eq_boundary : (boundaryLinear c L).ker = LaurentCechFinite318.boundary (transition c L) := by
  ext v
  change boundaryLinear c L v = 0 ↔ v ∈ LaurentCechFinite318.boundary (transition c L)
  rw [zero_iff]
  change (∃ (a : finiteSections c L) (b : infinitySections c L),
    coordinates c L (finiteRestriction c L a) - coordinates c L (infinityRestriction c L b) = v) ↔
      v ∈ positive ⊔ negative.map (LaurentTransitionBounds318.underlying (transition c L))
  rw [negative_image]
  constructor
  · rintro ⟨a,b,rfl⟩
    apply Submodule.sub_mem
    · apply (le_sup_left : positive ≤ positive ⊔ _)
      rw [← finite_image c L]
      exact ⟨a,rfl⟩
    · apply (le_sup_right : negative.map ((rawTransition c L).toLinearMap.restrictScalars ℚ) ≤ _)
      rw [← infinity_image c L]
      exact ⟨b,rfl⟩
  · intro hv
    obtain ⟨x,hx,y,hy,hxy⟩ := Submodule.mem_sup.mp hv
    have hny : -y ∈ negative.map ((rawTransition c L).toLinearMap.restrictScalars ℚ) :=
      Submodule.neg_mem _ hy
    rw [← finite_image c L] at hx
    rw [← infinity_image c L] at hny
    obtain ⟨a,ha⟩ := hx
    obtain ⟨b,hb⟩ := hny
    refine ⟨a,b,?_⟩
    rw [ha,hb,sub_neg_eq_add]
    exact hxy
end ContactOriginalLaurentBoundary318
