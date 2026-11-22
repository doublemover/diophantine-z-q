module

public import SelectedActualAbelExponentialNullTransfer318
public import SelectedActualAbelPeriodFromIdentityDifferential318
public import SelectedActualAbelFrozenCoordinateSard318
import all SelectedActualAbelFrozenCoordinateSard318
import all SelectedActualOrdinaryAbelPeriodMap318
import all SelectedActualAbelPeriodAgreement318

public section
noncomputable section

open MeasureTheory Set Function UpperHalfPlane
open GammaOneAtlas318 GammaOneFiber318 PeterssonQuotient318
open SelectedWeightTwoPetersson318
open SelectedActualAbelExponentialNullTransfer318
open SelectedActualAbelFrozenCoordinateSard318 (maskedTerm maskedSum masked_sum_image_null)
open SelectedActualAbelIdentityChartLifts318 SelectedActualAbelPeriodFromIdentityDifferential318
open SelectedActualOrdinaryAbelPeriodMap318 SelectedActualAbelPeriodAgreement318
open SelectedActualAbelTargetLatticeHaar318
open scoped BigOperators

namespace SelectedActualAbelDiscardedTargetNullWithoutCuspJets318

variable {g M : ℕ} {J X ι : Type*}
variable [AddCommGroup J] [TopologicalSpace J] [IsTopologicalAddGroup J]
variable [MeasurableSpace J] [BorelSpace J] [Finite ι]

/-- The actual discarded image in the same Jacobian is Haar-null
without any differentiability or analytic coordinates at the discarded
points. A countable family of point pins suffices. On every ordered
stratum with at least one pinned slot, all remaining slots are actual
ordinary periods and their full ambient lift is singular. -/
theorem discarded_abel_target_null
    (hM : 5 ≤ M) (f : Fin g → Form M)
    (L : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Module.Basis ι ℤ L) (q : (Fin g → ℂ) →+ J) (hq : Continuous q) (hqS : Surjective q)
    (hker : ∀ v : (Fin g → ℂ), q v = 0 ↔ v ∈ L) (C : IdentityChart q)
    (i : Base (image M) → X) (a : X → J) (ha : Continuous (a ∘ i))
    (hread : InvariantDifferentialEquation f C (a ∘ i))
    (D : Set X) (hD : D.Countable)
    (hCover : ∀ x : X, x ∉ D → ∃ t : UpperHalfPlane, i (quotientMap M t) = x) :
    targetVolume L b (volume : Measure (Fin g → ℂ)) q
      ((fun z : Fin g → X => ∑ j : Fin g, a (z j)) ''
        (⋃ j : Fin g, (fun z : Fin g → X => z j) ⁻¹' D)) = 0 := by
  classical
  let ν := targetVolume L b (volume : Measure (Fin g → ℂ)) q
  let P := {x : X // x ∈ D}
  let I := {s : Fin g → Option P // ∃ j : Fin g, ∃ d : P, s j = some d}
  letI : Countable P := hD.to_subtype
  letI : Countable I := inferInstance
  have hLocal := actual_local_original_lifts hM f q hq hqS C (a ∘ i) ha hread
  obtain ⟨c,hc⟩ := hqS (a (i (quotientMap M UpperHalfPlane.I)))
  choose lift hLift using (fun d : P => hqS (a d.val))
  let l (k : Fin g) (z : ℂ) : ℂ := primitive (f k) z + c k
  let d (k : Fin g) (z : ℂ) : ℂ := f k (UpperHalfPlane.ofComplex z)
  have hliftVal (t : UpperHalfPlane) : q (fun k => l k (t : ℂ)) = a (i (quotientMap M t)) := by
    have he : (fun k => l k (t : ℂ)) = primitiveVector f t + c := by
      funext k
      rfl
    rw [he,map_add,hc]
    exact (original_value_from_local_lifts f q (a ∘ i) hLocal t).symm
  have hder (k : Fin g) (z : ℂ) (hz : z ∈ upperHalfPlaneSet) :
      HasDerivAt (l k) (d k z) z := by
    let t : UpperHalfPlane := ⟨z,hz⟩
    have h := (primitive_hasDerivAt (f k) t).add_const (c k)
    change HasDerivAt (fun w => primitive (f k) w + c k) (f k t) z at h
    have hd : d k z = f k t := by
      unfold d
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
    exact hd.symm ▸ h
  let H (s : I) : Set J := q '' (maskedSum s.val lift l '' (Set.univ.pi fun _ => upperHalfPlaneSet))
  have hH (s : I) : ν (H s) = 0 := by
    obtain ⟨j,a₀,hs⟩ := s.property
    have hn := masked_sum_image_null s.val j a₀ hs lift l d upperHalfPlaneSet hder
    exact image_null_through_actual_exponential L b q hq hker C _ hn
  have hsub : ((fun z : Fin g → X => ∑ j : Fin g, a (z j)) ''
      (⋃ j : Fin g, (fun z : Fin g → X => z j) ⁻¹' D)) ⊆ ⋃ s : I, H s := by
    rintro _ ⟨z,hz,rfl⟩
    obtain ⟨j₀,hj₀⟩ := Set.mem_iUnion.mp hz
    have hpin (j : Fin g) : ∃ s : Option P, ∃ t : UpperHalfPlane,
        (s.elim (i (quotientMap M t)) (fun u => u.val) = z j) ∧
          (z j ∈ D → ∃ a₀ : P, s = some a₀) := by
      by_cases hj : z j ∈ D
      · exact ⟨some ⟨z j,hj⟩, UpperHalfPlane.I, rfl, fun _ => ⟨⟨z j,hj⟩,rfl⟩⟩
      · obtain ⟨t,ht⟩ := hCover (z j) hj
        exact ⟨none,t,ht,fun h => (hj h).elim⟩
    choose s t hst hpinned using hpin
    have hs : ∃ j : Fin g, ∃ a₀ : P, s j = some a₀ := ⟨j₀,hpinned j₀ hj₀⟩
    let pat : I := ⟨s,hs⟩
    let x : (Fin g → ℂ) := fun j => (t j : ℂ)
    have hx : x ∈ Set.univ.pi (fun _ => upperHalfPlaneSet) := fun j _ => (t j).im_pos
    apply Set.mem_iUnion.mpr
    refine ⟨pat,maskedSum s lift l x,⟨x,hx,rfl⟩,?_⟩
    have he : maskedSum s lift l x =
        ∑ j : Fin g, (s j).elim (fun k => l k (x j)) lift := by
      funext k
      simp only [maskedSum,_root_.sum_apply]
      apply Finset.sum_congr rfl
      intro j _
      cases h : s j <;> simp only [maskedTerm,h,Option.elim_none,Option.elim_some]
    rw [he,map_sum]
    apply Finset.sum_congr rfl
    intro j _
    cases h : s j with
    | none =>
      have hj : i (quotientMap M (t j)) = z j := by simpa only [h,Option.elim_none] using hst j
      exact (hliftVal (t j)).trans (congrArg a hj)
    | some a₀ =>
      have hj : a₀.val = z j := by simpa only [h,Option.elim_some] using hst j
      exact (hLift a₀).trans (congrArg a hj)
  exact measure_mono_null hsub (measure_iUnion_null hH)

end SelectedActualAbelDiscardedTargetNullWithoutCuspJets318

#print axioms SelectedActualAbelDiscardedTargetNullWithoutCuspJets318.discarded_abel_target_null
