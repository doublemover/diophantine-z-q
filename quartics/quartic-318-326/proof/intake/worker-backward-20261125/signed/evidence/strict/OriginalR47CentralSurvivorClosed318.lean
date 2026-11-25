module
public import OriginalR47CentralSurvivorFibre318
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public section
noncomputable section

namespace OriginalR47CentralSurvivorClosed318

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set
open OriginalSplitNodeCoordinates318
open OriginalR47CentralSurvivorFibre318 (atAxes)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Closedness is transported inside the actual old field fibre. Its
target is Jacobson since it is locally finite type over the actual
centre's residue field; no surjectivity or residue-field equality is
assumed for the upper affine chart. -/
theorem closed_in_old_chart {V T Y B : Scheme}
    (p : V ⟶ T) (s : Y ⟶ B) (f : V ⟶ Y) (k : T ⟶ B)
    (h : f ≫ s = p ≫ k)
    [LocallyOfFiniteType f] [LocallyOfFiniteType s]
    (t : T) (ht : IsClosed ({t} : Set T)) (hk : IsClosed ({k t} : Set B))
    (v : p.fiber t) (hv : IsClosed ({v} : Set (p.fiber t))) :
    IsClosed ({f (p.fiberι t v)} : Set Y) := by
  let : IsClosedImmersion (T.fromSpecResidueField t) :=
    isClosed_singleton_iff_isClosedImmersion.mp ht
  let : IsClosedImmersion (B.fromSpecResidueField (k t)) :=
    isClosed_singleton_iff_isClosedImmersion.mp hk
  let : IsClosedImmersion (p.fiberι t) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  let : IsClosedImmersion (s.fiberι (k t)) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  let g : p.fiber t ⟶ s.fiber (k t) := pullback.map p (T.fromSpecResidueField t)
    s (B.fromSpecResidueField (k t)) f (Spec.map (k.residueFieldMap t)) k h.symm (by simp)
  have hg : g ≫ s.fiberι (k t) = p.fiberι t ≫ f := by
    dsimp only [g, Scheme.Hom.fiberι, pullback.map]
    exact pullback.lift_fst _ _ _
  let : LocallyOfFiniteType (g ≫ s.fiberι (k t)) := hg.symm ▸
    (inferInstance : LocallyOfFiniteType (p.fiberι t ≫ f))
  let : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g (s.fiberι (k t))
  have hv' : IsClosed ({g v} : Set (s.fiber (k t))) :=
    g.closedPoints_subset_preimage_closedPoints hv
  have hcl := (s.fiberι (k t)).isClosedMap ({g v} : Set (s.fiber (k t))) hv'
  have hr : s.fiberι (k t) (g v) = f (p.fiberι t v) := by
    have he := congrArg (fun g' : p.fiber t ⟶ Y => g' v) hg
    simpa only [Scheme.Hom.comp_apply] using he
  simpa only [Set.image_singleton,hr] using hcl

/-- On the literal two-axis central chart, the unique point of the
chosen fibre is closed in that fibre because it is the inverse image
of the closed two-axis locus. -/
theorem isolate_in_fibre {R : Type} [CommRing R] (q : R) (d : ℕ)
    {V T : Scheme} (p : V ⟶ T) (l : V ⟶ Spec (CommRingCat.of (Node (q^d))))
    (t : T) (z : V) (ht : p z = t) (hz : atAxes q d (l z))
    (hunique : ∀ v, p v = t ∧ atAxes q d (l v) → v = z) :
    ∃ u : p.fiber t, p.fiberι t u = z ∧ IsClosed ({u} : Set (p.fiber t)) := by
  let u := (p.fiberHomeo t).symm ⟨z,ht⟩
  have hu : p.fiberι t u = z := p.fiberι_fiberHomeo_symm t ⟨z,ht⟩
  refine ⟨u,hu,?_⟩
  let Z := PrimeSpectrum.zeroLocus
    ({xAxis (q^d), yAxis (q^d)} : Set (Node (q^d)))
  have hZ : IsClosed Z := PrimeSpectrum.isClosed_zeroLocus _
  have read (v : V) : l v ∈ Z ↔ atAxes q d (l v) := by
    let y : PrimeSpectrum (Node (q^d)) := l v
    change y ∈ PrimeSpectrum.zeroLocus ({xAxis (q^d),yAxis (q^d)} : Set (Node (q^d))) ↔
      xAxis (q^d) ∈ y.asIdeal ∧ yAxis (q^d) ∈ y.asIdeal
    refine (PrimeSpectrum.mem_zeroLocus y _).trans ?_
    constructor
    · intro h
      exact ⟨h (by simp),h (by simp)⟩
    · rintro ⟨hx,hy⟩ a ha
      rcases Set.mem_insert_iff.mp ha with h | h
      · exact h.symm ▸ hx
      · exact (Set.mem_singleton_iff.mp h).symm ▸ hy
  have hL : ((p.fiberι t ≫ l) ⁻¹' Z) = ({u} : Set (p.fiber t)) := by
    ext a
    constructor
    · intro ha
      change l (p.fiberι t a) ∈ Z at ha
      have hp : p (p.fiberι t a) = t := (p.fiberHomeo t a).property
      have he := hunique (p.fiberι t a) ⟨hp,(read _).mp ha⟩
      apply Set.mem_singleton_iff.mpr
      exact (p.fiberι t).isEmbedding.injective (he.trans hu.symm)
    · rintro ha
      obtain rfl := Set.mem_singleton_iff.mp ha
      change l (p.fiberι t u) ∈ Z
      rw [hu]
      exact (read _).mpr hz
  rw [←hL]
  exact hZ.preimage (p.fiberι t ≫ l).continuous

end OriginalR47CentralSurvivorClosed318

#print axioms OriginalR47CentralSurvivorClosed318.closed_in_old_chart
#print axioms OriginalR47CentralSurvivorClosed318.isolate_in_fibre
