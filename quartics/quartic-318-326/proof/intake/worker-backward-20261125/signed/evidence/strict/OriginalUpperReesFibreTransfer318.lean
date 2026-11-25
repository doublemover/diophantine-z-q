module
public import OriginalUpperClosedMapFibreConnected318
public import OriginalUpperR40SplitFieldFibre318
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public section

namespace OriginalUpperReesFibreTransfer318

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set
universe u

variable {W X Y Z : Scheme.{u}}

/-- The image of the actual upper point fibre in a Cartesian square is
the entire lower point fibre, even over a nonsplit residue extension. -/
theorem image_point {a : W ⟶ X} {p : W ⟶ Y} {f : X ⟶ Z} {b : Y ⟶ Z}
    (h : IsPullback a p f b) (y : Y) :
    a '' (p ⁻¹' ({y} : Set Y)) = f ⁻¹' ({b y} : Set Z) := by
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    change p w = y at hw
    change f (a w) = b y
    have hh := congrArg (fun g : W ⟶ Z => g w) h.w
    simp only [Scheme.Hom.comp_apply] at hh
    exact hh.trans (congrArg b hw)
  · intro hx
    change f x = b y at hx
    obtain ⟨w, hwa, hwp⟩ := Scheme.exists_preimage_of_isPullback h x y hx
    exact ⟨w, hwp, hwa⟩

theorem descend_connected_point {a : W ⟶ X} {p : W ⟶ Y} {f : X ⟶ Z} {b : Y ⟶ Z}
    (h : IsPullback a p f b) (y : Y)
    (hc : _root_.IsConnected (p ⁻¹' ({y} : Set Y))) :
    _root_.IsConnected (f ⁻¹' ({b y} : Set Z)) := by
  rw [← image_point h y]
  exact hc.image a a.continuous.continuousOn

/-- The ordinary pullback of the exact residue field is the scheme
fibre in the shared chart, and its topology is the actual point fibre. -/
theorem connected_in_square {a : W ⟶ X} {p : W ⟶ Y} {f : X ⟶ Z} {b : Y ⟶ Z}
    (h : IsPullback a p f b) (y : Y)
    (hc : ConnectedSpace (↥(pullback (C:=Scheme) f (Y.fromSpecResidueField y ≫ b)))) :
    _root_.IsConnected (p ⁻¹' ({y} : Set Y)) := by
  let : ConnectedSpace (↥(pullback (C:=Scheme) f (Y.fromSpecResidueField y ≫ b))) := hc
  let e : p.fiber y ≅ pullback f (Y.fromSpecResidueField y ≫ b) :=
    ((IsPullback.of_hasPullback p (Y.fromSpecResidueField y)).paste_horiz h).isoPullback
  let : ConnectedSpace (↥(p.fiber y)) :=
    (Scheme.homeoOfIso e.symm).surjective.connectedSpace (Scheme.homeoOfIso e.symm).continuous
  exact isConnected_iff_connectedSpace.mpr
    ((p.fiberHomeo y).surjective.connectedSpace (p.fiberHomeo y).continuous)

/-- The exact common chart over the literal R40 blowup has connected
point fibre at any point mapping to its old centre. The marked point of
the shared étale chart supplies the only literal prime read. -/
theorem split_connected_in_square {R : Type} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (q : R) (hq : Irreducible q) (d : ℕ)
    {T V : Scheme}
    {a : V ⟶ OriginalUpperR40SplitFieldFibre318.model q d} {p : V ⟶ T}
    {b : T ⟶ Spec (CommRingCat.of (OriginalThickCentralReesChart318.O q d))}
    (h : IsPullback a p (OriginalUpperR40SplitFieldFibre318.toOld q d) b) (t : T)
    (hcentre : (b t).asIdeal = OriginalThickCentralReesChart318.I q d) :
    _root_.IsConnected (p ⁻¹' ({t} : Set T)) := by
  have hread (z : Spec (T.residueField t)) :
      ((T.fromSpecResidueField t ≫ b) z).asIdeal = OriginalThickCentralReesChart318.I q d := by
    have he : (T.fromSpecResidueField t ≫ b) z = b t :=
      (Scheme.Hom.comp_apply (T.fromSpecResidueField t) b z).trans
        (congrArg (fun y : T => b y) (Scheme.fromSpecResidueField_apply t z))
    exact (congrArg PrimeSpectrum.asIdeal he).trans hcentre
  apply connected_in_square h t
  exact OriginalUpperR40SplitFieldFibre318.split_field q hq d
    (K := T.residueField t) (T.fromSpecResidueField t ≫ b) hread

/-- In one genuine proper round, surjectivity and connectedness of the
composite fibres follow from nonempty connected fibres of each step. -/
theorem comp_connected (b : Y ⟶ X) (a : Z ⟶ Y) [IsProper a]
    (ha : ∀ y, _root_.IsConnected (a ⁻¹' ({y} : Set Y)))
    (hb : ∀ x, _root_.IsConnected (b ⁻¹' ({x} : Set X))) (x : X) :
    _root_.IsConnected ((a ≫ b) ⁻¹' ({x} : Set X)) := by
  have has : Function.Surjective a := by
    intro y
    obtain ⟨z, hz⟩ := (ha y).nonempty
    change a z = y at hz
    exact ⟨z, hz⟩
  have he : (a ≫ b) ⁻¹' ({x} : Set X) = a ⁻¹' (b ⁻¹' ({x} : Set X)) := by
    ext z
    simp only [Set.mem_preimage, Scheme.Hom.comp_apply]
  rw [he]
  refine ⟨?_, OriginalUpperClosedMapFibreConnected318.preimage a.isClosedMap
    (hb x).isPreconnected (fun y _ => has y) (fun y _ => (ha y).isPreconnected)⟩
  obtain ⟨y, hy⟩ := (hb x).nonempty
  obtain ⟨z, hz⟩ := has y
  refine ⟨z, ?_⟩
  change b y = x at hy
  change b (a z) = x
  rw [hz, hy]

end OriginalUpperReesFibreTransfer318

#print axioms OriginalUpperReesFibreTransfer318.image_point
#print axioms OriginalUpperReesFibreTransfer318.descend_connected_point
#print axioms OriginalUpperReesFibreTransfer318.connected_in_square
#print axioms OriginalUpperReesFibreTransfer318.comp_connected
#print axioms OriginalUpperReesFibreTransfer318.split_connected_in_square
