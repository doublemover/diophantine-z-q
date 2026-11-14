module
public import all ContactOriginalCohomologyCoordinates318
public import all OriginalFiniteBasisBaseChange318
public import all ContactOriginalLaurentCoordinates318
public import all OriginalLineMayerVietorisQuotient318
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
  simp only [OriginalFiniteBasisBaseChange318.reindex,LinearEquiv.refl_apply]

/-- Typed range membership transports Set equalities without rewriting a
Submodule membership as a hidden coercion. This retains the original minus. -/
private lemma range_sub_iff_sup {M X Y : Type*} [AddCommGroup M] [Module ℚ M]
    (f : X → M) (g : Y → M) (P Q : Submodule ℚ M)
    (hf : Set.range f = (P : Set M)) (hg : Set.range g = (Q : Set M)) (v : M) :
    (∃ a b, f a - g b = v) ↔ v ∈ P ⊔ Q := by
  have hfm (x : M) : (∃ a, f a = x) ↔ x ∈ P := Set.ext_iff.mp hf x
  have hgm (x : M) : (∃ b, g b = x) ↔ x ∈ Q := Set.ext_iff.mp hg x
  constructor
  · rintro ⟨a,b,rfl⟩
    exact Submodule.sub_mem (P ⊔ Q)
      ((show P ≤ P ⊔ Q from le_sup_left) ((hfm (f a)).mp ⟨a,rfl⟩))
      ((show Q ≤ P ⊔ Q from le_sup_right) ((hgm (g b)).mp ⟨b,rfl⟩))
  · intro hv
    obtain ⟨x,hx,y,hy,hxy⟩ := Submodule.mem_sup.mp hv
    obtain ⟨a,ha⟩ := (hfm x).mpr hx
    obtain ⟨b,hb⟩ := (hgm (-y)).mpr (Submodule.neg_mem Q hy)
    refine ⟨a,b,?_⟩
    rw [ha,hb,sub_neg_eq_add]
    exact hxy

variable (c : Fin 4 → ℚˣ) (L : Line (ContactProjectiveModel318.model c))

/-- Evaluate the exact equality-reindexed transition before transporting
its negative-filtration image. No geometric transition is replaced. -/
private lemma transition_apply (v : V ℚ (finiteRank c L)) :
    LaurentTransitionBounds318.underlying (transition c L) v =
      rawTransition c L
        ((OriginalFiniteBasisBaseChange318.reindex (A:=A) (rank_eq c L)).symm v) := by
  simp only [LaurentTransitionBounds318.underlying_apply,transition,LinearEquiv.trans_apply]

/-- The square transition's negative image is exactly the old rectangular
comparison's image. Its rank equality is proved, not newly assumed. -/
lemma negative_image :
    (negative.map (LaurentTransitionBounds318.underlying (transition c L))) =
    negative.map ((rawTransition c L).toLinearMap.restrictScalars ℚ) := by
  ext v
  constructor
  · rintro ⟨w,hw,hv⟩
    rw [transition_apply] at hv
    refine ⟨(OriginalFiniteBasisBaseChange318.reindex (A:=A) (rank_eq c L)).symm w,?_,hv⟩
    have h := reindex_negative (rank_eq c L)
      ((OriginalFiniteBasisBaseChange318.reindex (A:=A) (rank_eq c L)).symm w)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.mp hw
  · rintro ⟨w,hw,hv⟩
    refine ⟨OriginalFiniteBasisBaseChange318.reindex (A:=A) (rank_eq c L) w,
      (reindex_negative (rank_eq c L) w).mpr hw,?_⟩
    rw [transition_apply,LinearEquiv.symm_apply_apply]
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
  exact range_sub_iff_sup
    (fun a : finiteSections c L => coordinates c L (finiteRestriction c L a))
    (fun b : infinitySections c L => coordinates c L (infinityRestriction c L b))
    (positive (k:=ℚ) (n:=finiteRank c L))
    (negative.map ((rawTransition c L).toLinearMap.restrictScalars ℚ))
    (finite_image c L) (infinity_image c L) v
end ContactOriginalLaurentBoundary318
