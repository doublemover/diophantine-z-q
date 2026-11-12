module
public import PELOriginalVertexCount318
public import PELOriginalGenusBranchSqueeze318
public section
noncomputable section
namespace PELOriginalCellRiemannHurwitz318
open PELOriginalMaximalQuotient318 PELOriginalFiniteRamification318
open PELOriginalVertexCount318 PELOriginalGenusBranchSqueeze318
variable {V EX EY FX FY : Type*} [Fintype V] [Fintype EX] [Fintype EY]
  [Fintype FX] [Fintype FY]

/-- The actual projection supplies the entire vertex correction itself.
Given a compatible cellulation's original edge/face maps and Euler/genus
identities, this derives the SAME RH equation used by the original branch
squeeze. No separate supplied ramification count or RH premise remains. -/
theorem original_riemann_hurwitz (vertex : V → MaximalBase)
    (hi : Function.Injective vertex)
    (hcover : ∀ q : BranchValues, ∃ v : V, vertex v = q.val)
    (edge : EX → EY) (face : FX → FY)
    (hedge : ∀ e, Nat.card {x : EX // edge x = e} = 16)
    (hface : ∀ f, Nat.card {x : FX // face x = f} = 16)
    (sourceGenus quotientGenus : ℕ)
    (hsource : (Fintype.card (LiftedVertices vertex) : ℤ) - Fintype.card EX +
      Fintype.card FX = 2 - 2 * sourceGenus)
    (htarget : (Fintype.card V : ℤ) - Fintype.card EY +
      Fintype.card FY = 2 - 2 * quotientGenus) :
    2 * (sourceGenus : ℤ) - 2 = 16 * (2 * (quotientGenus : ℤ) - 2) +
      (Fintype.card Ramification : ℤ) := by
  have h := FiniteCellEulerCount318.riemann_hurwitz edge face
    (Fintype.card BranchValues) sourceGenus quotientGenus
    (lifted_vertices vertex hi hcover) hedge hface hsource htarget
  rw [total_ramification]
  push_cast
  simpa only [mul_comm] using h

/-- End-to-end cell-count consumer for the original quotient: every OLD
labeled fixed locus is one OLD displayed orbit. Actual compatible surface
cellulations, regular edge/face lift laws and the genus upper bound remain
geometric inputs, not conclusions of finite arithmetic. -/
theorem original_five_branch_orbits (vertex : V → MaximalBase)
    (hi : Function.Injective vertex)
    (hcover : ∀ q : BranchValues, ∃ v : V, vertex v = q.val)
    (edge : EX → EY) (face : FX → FY)
    (hedge : ∀ e, Nat.card {x : EX // edge x = e} = 16)
    (hface : ∀ f, Nat.card {x : FX // face x = f} = 16)
    (sourceGenus quotientGenus : ℕ) (hupper : sourceGenus ≤ 5)
    (hsource : (Fintype.card (LiftedVertices vertex) : ℤ) - Fintype.card EX +
      Fintype.card FX = 2 - 2 * sourceGenus)
    (htarget : (Fintype.card V : ℤ) - Fintype.card EY +
      Fintype.card FY = 2 - 2 * quotientGenus) :
    sourceGenus = 5 ∧ quotientGenus = 0 ∧ Fintype.card Ramification = 40 ∧
      Fintype.card BranchValues = 5 ∧ Function.Bijective displayed := by
  have hRH := original_riemann_hurwitz vertex hi hcover edge face hedge hface
    sourceGenus quotientGenus hsource htarget
  have hg := original_genus_and_branches sourceGenus quotientGenus hupper hRH
  exact ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2,
    original_displayed_bijective sourceGenus quotientGenus hupper hRH⟩
end PELOriginalCellRiemannHurwitz318
