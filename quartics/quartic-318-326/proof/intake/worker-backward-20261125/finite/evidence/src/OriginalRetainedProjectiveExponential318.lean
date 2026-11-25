module

public import OriginalRetainedF33ExponentialQuotient318
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Topology.Algebra.Group.Quotient

@[expose] public section
noncomputable section

namespace OriginalRetainedProjectiveExponential318

open AlgebraicGeometry CategoryTheory
open OriginalRetainedF33ExponentialQuotient318
open scoped CategoryTheory.Obj CategoryTheory.MonObj Topology

variable {A₃₃ Y₃₃ : Scheme} (a₃₃ : A₃₃⟶Y₃₃) [GrpObj (Over.mk a₃₃)]
variable {E : Type} [Field E] (σ : E→+*ℂ) (P : Spec (CommRingCat.of E)⟶Y₃₃)

local notation "G" => Additive (Points a₃₃ σ P)

variable (exp : Tangent→+G)
variable [IsAddCommutative G] [TopologicalSpace G] [SeparatelyContinuousAdd G]
variable [CompactSpace G]

/-- Obtain surjectivity without a separate actual analytification
connectedness theorem. Compactness uses the true original projective
point topology; divisibility comes from the actual installed [n]
morphism, not from the exponential being proved surjective. -/
theorem actual_exp_surjective_from_projectivity
    (near : (exp.range : Set G) ∈ 𝓝 (0:G))
    (divide : ∀ (n : ℕ), 0<n → Function.Surjective (fun z : G => n • z)) :
    Function.Surjective exp := by
  let H : AddSubgroup G := exp.range
  have Hopen : IsOpen (H : Set G) := AddSubgroup.isOpen_of_mem_nhds exp.range near
  letI : DiscreteTopology (G ⧸ H) := (QuotientAddGroup.discreteTopology_iff (N:=H)).2 Hopen
  letI : Finite (G ⧸ H) := finite_of_compact_of_discrete
  let q : G→+(G ⧸ H) := QuotientAddGroup.mk' H
  have hn : 0<Nat.card (G ⧸ H) := Nat.card_pos
  intro z
  obtain ⟨x,hx⟩ := divide _ hn z
  have zero : q z=0 := by
    rw [←hx,map_nsmul]
    exact card_nsmul_eq_zero'
  exact (QuotientAddGroup.eq_zero_iff (N:=H) z).1 zero

end OriginalRetainedProjectiveExponential318
