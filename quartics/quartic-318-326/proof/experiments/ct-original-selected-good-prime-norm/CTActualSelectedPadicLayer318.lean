module
public import CTOriginalClosureFieldEmbedding318
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public section
noncomputable section

namespace CTActualSelectedPadicLayer318

open Polynomial
open scoped Polynomial
open ActualTwoDescentClosureFieldEmbedding318

abbrev Qbar := AlgebraicClosure ℚ
abbrev GlobalLayer := FiniteGaloisIntermediateField ℚ Qbar
abbrev Pbar (p : ℕ) [Fact p.Prime] := AlgebraicClosure ℚ_[p]

variable (p : ℕ) [Fact p.Prime]

/-- The exact closure embedding used in the actual local restriction,
not a separately chosen embedding of the finite field. -/
@[expose] def closureEmbedding : Qbar →ₐ[ℚ] Pbar p where
  toRingHom := closureMap (algebraMap ℚ ℚ_[p])
  commutes' x :=
    (actual_closure_map_base (algebraMap ℚ ℚ_[p]) x).trans
      (IsScalarTower.algebraMap_apply ℚ ℚ_[p] (Pbar p) x).symm

/-- The compositum with the base inside the same chosen local closure. -/
@[expose] def localField (M : GlobalLayer) : IntermediateField ℚ_[p] (Pbar p) :=
  IntermediateField.adjoin ℚ_[p]
    (closureEmbedding p '' (M.toIntermediateField : Set Qbar))

theorem closure_mem_localField (M : GlobalLayer) {x : Qbar}
    (hx : x ∈ M.toIntermediateField) : closureEmbedding p x ∈ localField p M :=
  IntermediateField.subset_adjoin _ _ ⟨x,hx,rfl⟩

/-- The original global layer lands in the selected local field.
The left scalar is rational (not p-adic). -/
@[expose] def layerEmbedding (M : GlobalLayer) : M.toIntermediateField →ₐ[ℚ] localField p M :=
  { toFun := fun x => ⟨closureEmbedding p x,closure_mem_localField p M x.property⟩
    map_one' := Subtype.ext (map_one (closureEmbedding p))
    map_mul' := fun x y => Subtype.ext (map_mul (closureEmbedding p) (x : Qbar) (y : Qbar))
    map_zero' := Subtype.ext (map_zero (closureEmbedding p))
    map_add' := fun x y => Subtype.ext (map_add (closureEmbedding p) (x : Qbar) (y : Qbar))
    commutes' := fun x => Subtype.ext <| by
      change closureEmbedding p (algebraMap M.toIntermediateField Qbar
        (algebraMap ℚ M.toIntermediateField x)) =
        algebraMap (localField p M) (Pbar p) (algebraMap ℚ (localField p M) x)
      rw [← IsScalarTower.algebraMap_apply ℚ M.toIntermediateField Qbar,
        ← IsScalarTower.algebraMap_apply ℚ (localField p M) (Pbar p)]
      exact (closureEmbedding p).commutes x }

/-- The compositum is the splitting field of the same polynomial after
p-adic scalar extension. No linear disjointness assumption. -/
theorem localField_isSplittingField (M : GlobalLayer) (f : ℚ[X])
    (_h : IsSplittingField ℚ M.toIntermediateField f) :
    IsSplittingField ℚ_[p] (localField p M) (f.map (algebraMap ℚ ℚ_[p])) := by
  letI : IsSplittingField ℚ M.toIntermediateField f := _h
  let j : M.toIntermediateField →ₐ[ℚ] Pbar p :=
    (closureEmbedding p).comp M.toIntermediateField.val
  let q := f.map (algebraMap ℚ ℚ_[p])
  have hg : (f.map (algebraMap ℚ M.toIntermediateField)).Splits :=
    IsSplittingField.splits _ f
  have hs : (q.map (algebraMap ℚ_[p] (Pbar p))).Splits := by
    dsimp only [q]
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq,
      ← j.comp_algebraMap, ← Polynomial.map_map]
    exact hg.map (j : M.toIntermediateField →+* Pbar p)
  have hr : q.rootSet (Pbar p) = f.rootSet (Pbar p) :=
    Polynomial.rootSet_map ℚ_[p] (Pbar p) f
  have himage : j '' f.rootSet M.toIntermediateField = f.rootSet (Pbar p) :=
    hg.image_rootSet j
  have hadj : Algebra.adjoin ℚ (f.rootSet (Pbar p)) = j.range :=
    IsSplittingField.adjoin_rootSet_eq_range _ f j
  let L' := IntermediateField.adjoin ℚ_[p] (q.rootSet (Pbar p))
  have he : localField p M = L' := by
    apply le_antisymm
    · apply IntermediateField.adjoin_le_iff.2
      rintro _ ⟨x,hx,rfl⟩
      let x' : M.toIntermediateField := ⟨x,hx⟩
      have hsub : j.range ≤ L'.toSubalgebra.restrictScalars ℚ := by
        rw [← hadj,Algebra.adjoin_le_iff,← hr]
        exact IntermediateField.subset_adjoin ℚ_[p] _
      exact hsub (show j x' ∈ j.range from ⟨x',rfl⟩)
    · apply IntermediateField.adjoin_le_iff.2
      rw [hr,← himage]
      rintro _ ⟨x,_,rfl⟩
      exact closure_mem_localField p M x.property
  exact (IntermediateField.isSplittingField_iff).2
    ⟨IntermediateField.splits_of_splits hs (fun x hx => he.symm ▸
      IntermediateField.subset_adjoin ℚ_[p] _ hx),he⟩

instance finite_localField (M : GlobalLayer) : FiniteDimensional ℚ_[p] (localField p M) := by
  obtain ⟨f,hf⟩ := Normal.exists_isSplittingField ℚ M.toIntermediateField
  letI := localField_isSplittingField p M f hf
  exact IsSplittingField.finiteDimensional _ (f.map (algebraMap ℚ ℚ_[p]))

instance galois_localField (M : GlobalLayer) : IsGalois ℚ_[p] (localField p M) := by
  obtain ⟨f,hf⟩ := Normal.exists_isSplittingField ℚ M.toIntermediateField
  letI := localField_isSplittingField p M f hf
  exact (isGalois_iff _ _).2 ⟨inferInstance, Normal.of_isSplittingField
    (f.map (algebraMap ℚ ℚ_[p]))⟩

/-- Both maps use the same actual absolute-Galois restriction. -/
abbrev localRestriction (M : GlobalLayer) :
    Field.absoluteGaloisGroup ℚ_[p] →* (localField p M ≃ₐ[ℚ_[p]] localField p M) :=
  AlgEquiv.restrictNormalHom (localField p M)

abbrev globalPulledRestriction (M : GlobalLayer) :
    Field.absoluteGaloisGroup ℚ_[p] →* (M.toIntermediateField ≃ₐ[ℚ] M.toIntermediateField) :=
  (AlgEquiv.restrictNormalHom M.toIntermediateField).comp
    (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[p])).toMonoidHom

theorem localRestriction_surjective (M : GlobalLayer) :
    Function.Surjective (localRestriction p M) :=
  AlgEquiv.restrictNormalHom_surjective

/-- Literal equivariance of the embedded old global coefficient field. -/
theorem layerEmbedding_equivariant (M : GlobalLayer)
    (σ : Field.absoluteGaloisGroup ℚ_[p]) (x : M.toIntermediateField) :
    localRestriction p M σ (layerEmbedding p M x) =
      layerEmbedding p M (globalPulledRestriction p M σ x) := by
  apply Subtype.ext
  let s : Pbar p ≃ₐ[ℚ_[p]] Pbar p := σ
  let t : Qbar ≃ₐ[ℚ] Qbar := Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[p]) σ
  change (↑(AlgEquiv.restrictNormalHom (localField p M) s (layerEmbedding p M x)) : Pbar p) =
    closureEmbedding p (↑(AlgEquiv.restrictNormalHom M.toIntermediateField t x) : Qbar)
  rw [AlgEquiv.restrictNormalHom_apply,AlgEquiv.restrictNormalHom_apply]
  exact (actual_closure_map_galois (algebraMap ℚ ℚ_[p]) σ (x : Qbar)).symm

/-- Candidate actual finite quotient is exactly the kernel needed to
retain epsilon's old finite restriction, not the full global Galois group. -/
theorem same_restriction_kernel (M : GlobalLayer) :
    (localRestriction p M).ker = (globalPulledRestriction p M).ker := by
  ext σ
  change localRestriction p M σ = 1 ↔ globalPulledRestriction p M σ = 1
  constructor
  · intro hs
    apply AlgEquiv.ext
    intro x
    apply (layerEmbedding p M).injective
    rw [← layerEmbedding_equivariant,hs]
    rfl
  · intro hs
    let s : Pbar p ≃ₐ[ℚ_[p]] Pbar p := σ
    change s.restrictNormal (localField p M) = 1
    apply (AlgEquiv.restrictNormal_eq_one_iff _ s).2
    intro y hy
    refine IntermediateField.adjoin_induction (motive := fun z _ => s z = z) ?_
      s.commutes ?_ ?_ ?_ hy
    · rintro _ ⟨x,hx,rfl⟩
      let x' : M.toIntermediateField := ⟨x,hx⟩
      have he := congrArg Subtype.val (layerEmbedding_equivariant p M σ x')
      rw [hs] at he
      change (↑(AlgEquiv.restrictNormalHom (localField p M) s
          (layerEmbedding p M x')) : Pbar p) = closureEmbedding p x at he
      rw [AlgEquiv.restrictNormalHom_apply] at he
      exact he
    · intro a b _ _ ha hb
      rw [map_add,ha,hb]
    · intro a _ ha
      rw [map_inv₀,ha]
    · intro a b _ _ ha hb
      rw [map_mul,ha,hb]

/-- Exact local field Galois group as the image of its restriction into
the old global finite layer. This identifies the group actions without
replacing the degree by the global degree. -/
def localGalEquivGlobalImage (M : GlobalLayer) :
    (localField p M ≃ₐ[ℚ_[p]] localField p M) ≃* (globalPulledRestriction p M).range :=
  (QuotientGroup.quotientKerEquivOfSurjective (localRestriction p M)
    (localRestriction_surjective p M)).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq (same_restriction_kernel p M)).trans
        (QuotientGroup.quotientKerEquivRange (globalPulledRestriction p M)))

theorem localGalEquivGlobalImage_on_restriction (M : GlobalLayer)
    (σ : Field.absoluteGaloisGroup ℚ_[p]) :
    (localGalEquivGlobalImage p M (localRestriction p M σ)).val =
      globalPulledRestriction p M σ := by
  let e := QuotientGroup.quotientKerEquivOfSurjective (localRestriction p M)
    (localRestriction_surjective p M)
  have h : e (QuotientGroup.mk σ) = localRestriction p M σ :=
    QuotientGroup.kerLift_mk (localRestriction p M) σ
  have hh : e.symm (localRestriction p M σ) = QuotientGroup.mk σ :=
    (congrArg e.symm h.symm).trans (e.symm_apply_apply _)
  change ((QuotientGroup.quotientKerEquivRange (globalPulledRestriction p M))
    (QuotientGroup.quotientMulEquivOfEq (same_restriction_kernel p M)
      (e.symm (localRestriction p M σ)))).val = globalPulledRestriction p M σ
  rw [hh,QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

end CTActualSelectedPadicLayer318
