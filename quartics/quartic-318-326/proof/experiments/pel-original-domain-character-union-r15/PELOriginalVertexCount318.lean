module
public import PELOriginalFiniteRamification318
public import FiniteCellEulerCount318
public section
noncomputable section
open scoped BigOperators
namespace PELOriginalVertexCount318
open PELUnlevelledComplexBase318 PELOriginalMaximalQuotient318
open PELOriginalFiniteRamification318 PELStabilizerLocusInvariant318
variable {V : Type*} [Fintype V] (vertex : V → MaximalBase)

/-- The actual FULL inverse image of the original target vertex set. -/
abbrev LiftedVertices := Σ v : V,
  {x : UnlevelledBase // PELOriginalMaximalQuotient318.projection x = vertex v}

instance vertexFiberFintype (v : V) : Fintype
    {x : UnlevelledBase // PELOriginalMaximalQuotient318.projection x = vertex v} :=
  (PELMaximalQuotientProper318.fiber_finite (vertex v)).fintype

/-- A target cellulation must contain EVERY original branch value. Under
that precise coverage and injective original vertex map, its branch vertices
are equivalent to the SAME whole branch image. -/
@[expose] def branchVertexEquiv (hi : Function.Injective vertex)
    (hcover : ∀ q : BranchValues, ∃ v : V, vertex v = q.val) :
    {v : V // vertex v ∈ branchImage} ≃ BranchValues :=
  Equiv.ofBijective (fun v => ⟨vertex v.val, v.property⟩) ⟨by
    intro a b h
    exact Subtype.ext (hi (congrArg Subtype.val h)), by
    intro q
    obtain ⟨v, hv⟩ := hcover q
    exact ⟨⟨v, hv.symm ▸ q.property⟩, Subtype.ext hv⟩⟩

/-- The original projection's concrete16/8 fibers compute its lifted
vertex correction, with no branch multiplicities supplied separately. -/
theorem lifted_vertices (hi : Function.Injective vertex)
    (hcover : ∀ q : BranchValues, ∃ v : V, vertex v = q.val) :
    (Fintype.card (LiftedVertices vertex) : ℤ) =
      16 * Fintype.card V - 8 * Fintype.card BranchValues := by
  classical
  let P : V → Prop := fun v => vertex v ∈ branchImage
  have hc : Fintype.card {v : V // P v} = Fintype.card BranchValues :=
    Fintype.card_congr (branchVertexEquiv vertex hi hcover)
  have hsplit : Fintype.card V = Fintype.card {v : V // P v} +
      Fintype.card {v : V // ¬ P v} := by
    have h := FiniteCellEulerCount318.sum_partition P (fun _ _ => (1 : ℕ)) (fun _ _ => (1 : ℕ))
    simpa using h
  have htotal : Fintype.card (LiftedVertices vertex) =
      Fintype.card {v : V // P v} * 8 + Fintype.card {v : V // ¬ P v} * 16 := by
    rw [Fintype.card_sigma]
    calc
      _ = ∑ v : V, if _ : P v then (8 : ℕ) else 16 := by
        apply Finset.sum_congr rfl
        intro v _
        have h := PELMaximalFiberCardinality318.original_fiber_card (vertex v)
        simpa only [Nat.card_eq_fintype_card] using h
      _ = _ := by
        have h := FiniteCellEulerCount318.sum_partition P (fun _ _ => (8 : ℕ)) (fun _ _ => (16 : ℕ))
        simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul] using h
  rw [htotal]
  have hs : (Fintype.card V : ℤ) = (Fintype.card {v : V // P v} : ℤ) +
      Fintype.card {v : V // ¬ P v} := by exact_mod_cast hsplit
  have hb : (Fintype.card {v : V // P v} : ℤ) = Fintype.card BranchValues := by exact_mod_cast hc
  push_cast
  linarith
end PELOriginalVertexCount318
