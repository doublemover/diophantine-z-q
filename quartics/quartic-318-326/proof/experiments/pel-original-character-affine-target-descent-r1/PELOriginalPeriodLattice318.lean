module
public import QuaternionicMatrixCoordinates318
public import QuaternionicOrderPeriodQuotient318
public import PELPrincipalOrderCoordinates318
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Topology.Algebra.Group.Quotient
public section
noncomputable section
namespace PELOriginalPeriodLattice318
open QuaternionicRealPeriod318 QuaternionicOrderPeriodQuotient318
open PELQuaternionAlgebra318 PELQuaternionRealRepresentation318
open PELPrincipalOrderCoordinates318 QuaternionicMatrixCoordinates318
set_option maxHeartbeats 1200000
variable (τ : ℂ) (hτ : 0<τ.im)
@[expose] def coordinates : (Fin 4 → ℝ) ≃ₗ[ℝ] ComplexVectors :=
  orderPeriodEquiv alpha beta alpha_pos.ne' beta_pos.ne' τ hτ
@[expose] def basis : Module.Basis (Fin 4) ℝ ComplexVectors :=
  (Pi.basisFun ℝ (Fin 4)).map (coordinates τ hτ)
@[expose] def lattice : Submodule ℤ ComplexVectors := Submodule.span ℤ (Set.range (basis τ hτ))

/-- The real coordinates are exactly the original embedded order coordinates,
including the nontrivial denominators2 and10. -/
theorem original_coordinates (x : PELPrincipalOrderCoordinates318.Coordinates) :
    periodHom representation τ (embed x)=coordinates τ hτ (fun i => (x i:ℝ)) := by
  have hm : representation (embed x)=
      orderMatrixEquiv alpha beta alpha_pos.ne' beta_pos.ne' (fun i => (x i:ℝ)) := by
    ext i j
    fin_cases i <;> fin_cases j
    · change (((x 0:ℚ)+(x 2:ℚ)/2:ℚ):ℝ)+beta*(((x 2:ℚ)/2:ℚ):ℝ)=
        (x 0:ℝ)+(x 2:ℝ)/2+beta*((x 2:ℝ)/2)
      push_cast <;> ring
    · change -alpha*(((x 1:ℚ)+(x 3:ℚ)/2:ℚ):ℝ)+alpha*beta*(((x 3:ℚ)/10:ℚ):ℝ)=
        -alpha*((x 1:ℝ)+(x 3:ℝ)/2)+alpha*beta*((x 3:ℝ)/10)
      push_cast <;> ring
    · change alpha*(((x 1:ℚ)+(x 3:ℚ)/2:ℚ):ℝ)+alpha*beta*(((x 3:ℚ)/10:ℚ):ℝ)=
        alpha*((x 1:ℝ)+(x 3:ℝ)/2)+alpha*beta*((x 3:ℝ)/10)
      push_cast <;> ring
    · change (((x 0:ℚ)+(x 2:ℚ)/2:ℚ):ℝ)-beta*(((x 2:ℚ)/2:ℚ):ℝ)=
        (x 0:ℝ)+(x 2:ℝ)/2-beta*((x 2:ℝ)/2)
      push_cast <;> ring
  change period τ (representation (embed x))=
    period τ (orderMatrixEquiv alpha beta alpha_pos.ne' beta_pos.ne' (fun i => (x i:ℝ)))
  exact congrArg (period τ) hm

theorem basis_original (i : Fin 4) :
    basis τ hτ i=periodHom representation τ (embed (Pi.single i 1)) := by
  rw [original_coordinates τ hτ (Pi.single i 1)]
  change coordinates τ hτ ((Pi.basisFun ℝ (Fin 4)) i)=coordinates τ hτ _
  congr 1
  funext j
  by_cases h : i=j
  · subst j
    simp
  · simp [h,Ne.symm h]

theorem original_mem_lattice (x : PELPrincipalOrderCoordinates318.Coordinates) :
    periodHom representation τ (embed x)∈lattice τ hτ := by
  rw [original_coordinates τ hτ x]
  have hs : coordinates τ hτ (fun i => (x i:ℝ))=
      ∑i:Fin 4,(x i:ℝ) • basis τ hτ i := by
    have h := congrArg (coordinates τ hτ)
      ((Pi.basisFun ℝ (Fin 4)).sum_repr (fun i => (x i:ℝ)))
    simpa [basis,map_sum,Pi.basisFun_repr] using h.symm
  rw [hs]
  apply Submodule.sum_mem
  intro i _
  rw [Int.cast_smul_eq_zsmul ℝ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩)

/-- Equality of entire period subgroups, not merely their real span or rank. -/
theorem exact_period_subgroup : periodSubgroup representation order τ=(lattice τ hτ).toAddSubgroup := by
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨a,rfl⟩ := hx
    exact original_mem_lattice τ hτ a
  · intro hz
    change z∈Submodule.span ℤ (Set.range (basis τ hτ)) at hz
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨i,rfl⟩
      rw [basis_original τ hτ i]
      exact ⟨embed (Pi.single i 1),⟨Pi.single i 1,rfl⟩,rfl⟩
    · exact (periodSubgroup representation order τ).zero_mem
    · intro x y hx hy ihx ihy
      exact (periodSubgroup representation order τ).add_mem ihx ihy
    · intro n x hx ih
      exact (periodSubgroup representation order τ).zsmul_mem ih n

include hτ in
/-- The specified original order gives a discrete full period lattice. -/
theorem original_discrete : DiscreteTopology (periodSubgroup representation order τ) := by
  rw [exact_period_subgroup τ hτ]
  change DiscreteTopology (lattice τ hτ)
  exact inferInstanceAs (DiscreteTopology (Submodule.span ℤ (Set.range (basis τ hτ))))

include hτ in
/-- Compactness of the SAME quotient by the original order is derived from
its computed full real basis, not supplied as a torus hypothesis. -/
theorem original_compact : CompactSpace (PeriodQuotient representation order τ) := by
  let q : ComplexVectors → PeriodQuotient representation order τ :=
    QuotientAddGroup.mk' (periodSubgroup representation order τ)
  have hc : Continuous q := QuotientAddGroup.continuous_mk
  have hp : ∀ z w, w∈lattice τ hτ → q (z+w)=q z := by
    intro z w hw
    have hw' : w∈periodSubgroup representation order τ := by
      rw [exact_period_subgroup τ hτ]
      exact hw
    have hq : q w=0 := (QuotientAddGroup.eq_zero_iff _).mpr hw'
    change (QuotientAddGroup.mk' (periodSubgroup representation order τ)) (z+w)=
      (QuotientAddGroup.mk' (periodSubgroup representation order τ)) z
    rw [map_add,show (QuotientAddGroup.mk' (periodSubgroup representation order τ)) w=0 from hq,
      add_zero]
  letI : DiscreteTopology (lattice τ hτ) := by
    have hd := original_discrete τ hτ
    rw [exact_period_subgroup τ hτ] at hd
    exact hd
  letI : IsZLattice ℝ (lattice τ hτ) := by dsimp [lattice]; infer_instance
  have hk := IsZLattice.isCompact_range_of_periodic (lattice τ hτ) q hc hp
  have hs : Set.range q=Set.univ := Set.range_eq_univ.mpr (QuotientAddGroup.mk'_surjective _)
  rw [hs] at hk
  exact ⟨hk⟩
end PELOriginalPeriodLattice318
