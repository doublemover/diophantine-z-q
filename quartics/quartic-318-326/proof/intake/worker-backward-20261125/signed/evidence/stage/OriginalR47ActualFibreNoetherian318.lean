module
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.Topology.NoetherianSpace
public section
noncomputable section

namespace OriginalR47ActualFibreNoetherian318

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {X S : Scheme.{u}} (s : X ⟶ S) [IsProper s]

/-- The actual old fibre of a proper arithmetic scheme is topologically
Noetherian. Its canonical residue-field map supplies all finite type
coordinate maps on one finite subcover. No absolute scheme
Noetherian API, fake geometric-fibre model or separate given finite
atlas is needed. -/
theorem actual (t : S) : NoetherianSpace (s.fiber t) := by
  let Y := s.fiber t
  let κ := S.residueField t
  let p : Y ⟶ Spec κ := s.fiberToSpecResidueField t
  let : LocallyOfFiniteType p := MorphismProperty.pullback_snd _ _
    (inferInstance : LocallyOfFiniteType s)
  let W := Y.affineOpenCover
  let U := W.openCover
  let V := U.finiteSubcover
  have hNoeth (i : V.I₀) : NoetherianSpace (Set.range (V.f i)) := by
    let A := W.X (U.idx i.val)
    let a : Spec A ⟶ Y := V.f i
    let g := a ≫ p
    let α : κ ⟶ A := Spec.preimage g
    have hα : Spec.map α = g := Spec.map_preimage _
    let : IsOpenImmersion a := V.map_prop i
    have hfinite : LocallyOfFiniteType (Spec.map α) :=
      hα.symm ▸ (inferInstance : LocallyOfFiniteType (a ≫ p))
    let : Algebra κ A := α.hom.toAlgebra
    let : Algebra.FiniteType κ A := RingHom.finiteType_algebraMap.mp
      ((HasRingHomProperty.Spec_iff (P:=@LocallyOfFiniteType)).mp hfinite)
    let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing κ A
    exact NoetherianSpace.range a a.continuous
  rw [← noetherian_univ_iff,← V.iUnion_range]
  let : ∀ i : V.I₀, NoetherianSpace (Set.range (V.f i)) := hNoeth
  exact NoetherianSpace.iUnion (fun i : V.I₀ => Set.range (V.f i))

end OriginalR47ActualFibreNoetherian318

#print axioms OriginalR47ActualFibreNoetherian318.actual
