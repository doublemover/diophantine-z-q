module
public import OriginalActualNodeDomain318
public import Mathlib.AlgebraicGeometry.Fiber
public section
noncomputable section

namespace OriginalUpperR40SplitCentralField318

open AlgebraicGeometry OriginalSplitNodeCoordinates318 OriginalNodeRingMaps318
open CategoryTheory Set Polynomial
variable (k : Type) [Field k]

/-- The two actual zero-product axes in the R40 central residue ring. -/
@[expose] def axis : Bool → Node (0 : k) →ₐ[k] k[X]
  | false => eval 0 0 X (by simp)
  | true => eval 0 X 0 (by simp)

@[expose] def back : Bool → k[X] →ₐ[k] Node (0 : k)
  | false => aeval (yAxis 0)
  | true => aeval (xAxis 0)

@[expose] def line (b : Bool) : Spec (CommRingCat.of k[X]) ⟶ Spec (CommRingCat.of (Node (0 : k))) :=
  Spec.map (CommRingCat.ofHom (axis k b).toRingHom)

theorem factors (p : Spec (CommRingCat.of (Node (0 : k)))) (b : Bool)
    (hz : (if b then yAxis (0 : k) else xAxis (0 : k)) ∈ p.asIdeal) : p ∈ Set.range (line k b) := by
  let Q := Ideal.Quotient.mkₐ k p.asIdeal
  have hQ : Q (if b then yAxis (0 : k) else xAxis (0 : k)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hz
  have he : ((Q.comp (back k b)).comp (axis k b)) = Q := by
    apply OriginalNodeRingMaps318.ext
    · cases b
      · change Q (back k false (axis k false (xAxis (0 : k)))) = _
        rw [axis, eval_x, map_zero, map_zero]
        exact hQ.symm
      · change Q (back k true (axis k true (xAxis (0 : k)))) = _
        rw [axis, eval_x, back, aeval_X]
    · cases b
      · change Q (back k false (axis k false (yAxis (0 : k)))) = _
        rw [axis, eval_y, back, aeval_X]
      · change Q (back k true (axis k true (yAxis (0 : k)))) = _
        rw [axis, eval_y, map_zero, map_zero]
        exact hQ.symm
  refine ⟨PrimeSpectrum.comap (back k b).toRingHom p, ?_⟩
  apply PrimeSpectrum.ext
  ext r
  change (back k b) (axis k b r) ∈ p.asIdeal ↔ r ∈ p.asIdeal
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.eq_zero_iff_mem]
  change Q (back k b (axis k b r)) = 0 ↔ Q r = 0
  rw [show Q (back k b (axis k b r)) = Q r from DFunLike.congr_fun he r]

theorem axes_cover : Set.range (line k true) ∪ Set.range (line k false) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  have h : yAxis (0 : k) * xAxis (0 : k) ∈ p.asIdeal := by
    rw [node_relation, map_zero]
    exact p.asIdeal.zero_mem
  rcases p.isPrime.mem_or_mem h with hy | hx
  · exact Or.inl (factors k p true hy)
  · exact Or.inr (factors k p false hx)

theorem at_origin : ∃ p, p ∈ Set.range (line k true) ∧ p ∈ Set.range (line k false) := by
  let r : Node (0 : k) →ₐ[k] k := eval 0 0 0 (by simp)
  let p : Spec (CommRingCat.of (Node (0 : k))) :=
    PrimeSpectrum.comap r.toRingHom (IsLocalRing.closedPoint k)
  have hx : xAxis (0 : k) ∈ p.asIdeal := by
    change r (xAxis (0 : k)) ∈ (IsLocalRing.closedPoint k).asIdeal
    rw [show r (xAxis (0 : k)) = 0 from eval_x ..]
    exact Ideal.zero_mem _
  have hy : yAxis (0 : k) ∈ p.asIdeal := by
    change r (yAxis (0 : k)) ∈ (IsLocalRing.closedPoint k).asIdeal
    rw [show r (yAxis (0 : k)) = 0 from eval_y ..]
    exact Ideal.zero_mem _
  exact ⟨p, factors k p true hy, factors k p false hx⟩

/-- The literal split central XY=0 chart is connected over every field,
including residue characteristic two. Both axes are retained. -/
theorem zero_connected : ConnectedSpace (Spec (CommRingCat.of (Node (0 : k)))) := by
  obtain ⟨p, hp, hp'⟩ := at_origin k
  let : PreconnectedSpace (Spec (CommRingCat.of (Polynomial k))) := by
    change PreconnectedSpace (PrimeSpectrum (Polynomial k))
    infer_instance
  have hpre := (isPreconnected_range (line k true).continuous).union p hp hp'
    (isPreconnected_range (line k false).continuous)
  rw [axes_cover] at hpre
  exact connectedSpace_iff_univ.mpr ⟨⟨p, Set.mem_univ _⟩, hpre⟩

/-- The literal split central XY=1 chart is a nonempty domain. -/
theorem one_connected : ConnectedSpace (Spec (CommRingCat.of (Node (1 : k)))) := by
  let : IsDomain (Node (1 : k)) := OriginalActualNodeDomain318.domain _ one_ne_zero
  change ConnectedSpace (PrimeSpectrum (Node (1 : k)))
  infer_instance

end OriginalUpperR40SplitCentralField318

#print axioms OriginalUpperR40SplitCentralField318.axes_cover
#print axioms OriginalUpperR40SplitCentralField318.zero_connected
#print axioms OriginalUpperR40SplitCentralField318.one_connected
