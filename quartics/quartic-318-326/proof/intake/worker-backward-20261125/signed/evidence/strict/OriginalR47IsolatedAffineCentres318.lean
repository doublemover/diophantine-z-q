module
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.AffineScheme
public section
noncomputable section

namespace OriginalR47IsolatedCentreCover318

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Set TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {X : Scheme.{u}} (Z : Set X) (hZ : Z.Finite)
variable (hClosed : ∀ x ∈ Z, IsClosed ({x} : Set X))

include hZ hClosed in
theorem closed : IsClosed Z := by
  classical
  have h : (⋃ x ∈ hZ.toFinset, ({x} : Set X)) = Z := by
    ext x
    simp [hZ.mem_toFinset]
  rw [← h]
  exact isClosed_biUnion_finset fun x hx => hClosed x (hZ.mem_toFinset.mp hx)

def off : X.Opens :=
  ⟨Zᶜ, (closed Z hZ hClosed).isOpen_compl⟩

/-- An actual affine open of the old scheme isolating this exact closed
centre and containing no other centre in the prescribed finite set. -/
structure Centre (z : Z) where
  U : X.Opens
  affine : IsAffineOpen U
  here : z.val ∈ U
  alone : ∀ w : Z, w.val ∈ U → w = z

include hZ hClosed in
theorem centre_exists (z : Z) : Nonempty (Centre Z z) := by
  classical
  let Z' := Z \ ({z.val} : Set X)
  have hZ' : Z'.Finite := hZ.subset Set.sdiff_subset
  have hC' : IsClosed Z' := closed Z' hZ' fun x hx => hClosed x hx.1
  let D : X.Opens := ⟨Z'ᶜ, hC'.isOpen_compl⟩
  have hx : z.val ∈ D := by
    change z.val ∈ Z'ᶜ
    simp [Z']
  obtain ⟨U,hU,hhere,hsub⟩ := exists_isAffineOpen_mem_and_subset hx
  refine ⟨⟨U,hU,hhere,?_⟩⟩
  intro w hw
  apply Subtype.ext
  by_contra hne
  exact (hsub hw) ⟨w.property, fun he => hne (Set.mem_singleton_iff.mp he)⟩

variable (pick : ∀ z : Z, Centre Z z)

inductive Idx (P : ∀ z : Z, Centre Z z) where
  | outside (V : X.Opens) (hV : V ≤ off Z hZ hClosed)
  | hit (z : Z)

abbrev idxOpen : Idx Z hZ hClosed pick → X.Opens
  | .outside V _ => V
  | .hit z => (pick z).U

instance : Preorder (Idx Z hZ hClosed pick) :=
  Preorder.lift (idxOpen Z hZ hClosed pick)

@[expose] def oldCover : X.OpenCover where
  I₀ := Idx Z hZ hClosed pick
  X i := (idxOpen Z hZ hClosed pick i).toScheme
  f i := (idxOpen Z hZ hClosed pick i).ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_,fun i => inferInstance⟩
    intro x
    by_cases hx : x ∈ Z
    · refine ⟨.hit ⟨x,hx⟩,?_⟩
      rw [Scheme.Opens.range_ι]
      exact (pick ⟨x,hx⟩).here
    · refine ⟨.outside (off Z hZ hClosed) le_rfl,?_⟩
      rw [Scheme.Opens.range_ι]
      exact hx

theorem hit_le_hit (z w : Z)
    (h : (Idx.hit z : Idx Z hZ hClosed pick) ≤ Idx.hit w) : z = w :=
  (pick w).alone z (h (pick z).here)

theorem not_hit_le_outside (z : Z) (V : X.Opens) (hV : V ≤ off Z hZ hClosed) :
    ¬ (Idx.hit z : Idx Z hZ hClosed pick) ≤ Idx.outside V hV := by
  intro h
  exact (hV (h (pick z).here)) z.property

/-- Distinct affine-centre pieces only overlap inside the genuine
complement. If the same centre occurs on both sides, reuse its old open. -/
theorem common_below (i j : Idx Z hZ hClosed pick) :
    ∃ k : Idx Z hZ hClosed pick, k ≤ i ∧ k ≤ j ∧
      idxOpen Z hZ hClosed pick i ⊓ idxOpen Z hZ hClosed pick j ≤
        idxOpen Z hZ hClosed pick k := by
  let U := idxOpen Z hZ hClosed pick
  have le_of {i j : Idx Z hZ hClosed pick} (h : U i ≤ U j) : i ≤ j := h
  cases i with
  | outside V hV =>
    let k : Idx Z hZ hClosed pick := .outside (V ⊓ U j) (inf_le_left.trans hV)
    refine ⟨k, le_of (i := k) (j := .outside V hV) ?_, le_of (i := k) (j := j) ?_, le_rfl⟩
    · exact (inf_le_left : V ⊓ U j ≤ V)
    · exact (inf_le_right : V ⊓ U j ≤ U j)
  | hit z =>
    cases j with
    | outside V hV =>
      let k : Idx Z hZ hClosed pick := .outside ((pick z).U ⊓ V) (inf_le_right.trans hV)
      refine ⟨k, le_of (i := k) (j := .hit z) ?_, le_of (i := k) (j := .outside V hV) ?_, le_rfl⟩
      · exact (inf_le_left : (pick z).U ⊓ V ≤ (pick z).U)
      · exact (inf_le_right : (pick z).U ⊓ V ≤ V)
    | hit w =>
      classical
      by_cases e : z = w
      · subst w
        exact ⟨.hit z,le_rfl,le_rfl,inf_le_left⟩
      · have h : (pick z).U ⊓ (pick w).U ≤ off Z hZ hClosed := by
          intro x hx hz
          exact e (((pick z).alone ⟨x,hz⟩ hx.1).symm.trans ((pick w).alone ⟨x,hz⟩ hx.2))
        let k : Idx Z hZ hClosed pick := .outside ((pick z).U ⊓ (pick w).U) h
        refine ⟨k, le_of (i := k) (j := .hit z) ?_, le_of (i := k) (j := .hit w) ?_, le_rfl⟩
        · exact (inf_le_left : (pick z).U ⊓ (pick w).U ≤ (pick z).U)
        · exact (inf_le_right : (pick z).U ⊓ (pick w).U ≤ (pick w).U)


end OriginalR47IsolatedCentreCover318

#print axioms OriginalR47IsolatedCentreCover318.centre_exists
#print axioms OriginalR47IsolatedCentreCover318.oldCover
#print axioms OriginalR47IsolatedCentreCover318.common_below
