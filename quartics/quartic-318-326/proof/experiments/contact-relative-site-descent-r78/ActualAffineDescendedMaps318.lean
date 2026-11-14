module
public import ActualAffineDescentData318
public section
noncomputable section
namespace ActualAffineDescendedMaps318
open AlgebraicGeometry CategoryTheory LineSheafClass318 ActualAffineDescentData318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {R S : CommRingCat.{u}} [Algebra R S] [Module.FaithfullyFlat R S]
abbrev line (D : Datum R S) := ActualAffineLineReconstruction318.line R S D.line D.overlap D.diagonal D.triple
abbrev comparison (D : Datum R S) := ActualAffineLineReconstruction318.pullbackIso R S D.line D.overlap D.diagonal D.triple

/-- The descended map of actual geometric data, with the original
covering sheaf map retained through its exact tensor intertwiner. -/
@[expose] def map {D E : Datum R S} (h : Hom D E) : (line D).object ⟶ (line E).object :=
  GeometricAffineDescendedMorphism318.map h.tensor

lemma map_commutes {D E : Datum R S} (h : Hom D E) :
    (Scheme.Modules.pullback (ActualAffineDoubleNerve318.baseMap R S)).map (map h) ≫
      (comparison E).hom = (comparison D).hom ≫ h.sheafHom :=
  GeometricAffineDescendedMorphism318.map_commutes h.tensor

lemma map_unique {D E : Datum R S} (h : Hom D E)
    (k : (line D).object ⟶ (line E).object)
    (hk : (Scheme.Modules.pullback (ActualAffineDoubleNerve318.baseMap R S)).map k ≫
      (comparison E).hom = (comparison D).hom ≫ h.sheafHom) : k = map h :=
  GeometricAffineDescendedMorphism318.map_unique h.tensor k hk

lemma exists_unique_map {D E : Datum R S} (h : Hom D E) :
    ∃! k : (line D).object ⟶ (line E).object,
      (Scheme.Modules.pullback (ActualAffineDoubleNerve318.baseMap R S)).map k ≫
        (comparison E).hom = (comparison D).hom ≫ h.sheafHom :=
  ⟨map h, map_commutes h, fun k hk => map_unique h k hk⟩

lemma map_id (D : Datum R S) : map (Hom.id D) = 𝟙 (line D).object := by
  unfold map
  rw [Hom.tensor_id]
  exact GeometricAffineDescendedFunctor318.map_id (tensorDatum D)

lemma map_comp {D E F : Datum R S} (h : Hom D E) (k : Hom E F) :
    map (h.comp k) = map h ≫ map k := by
  unfold map
  rw [Hom.tensor_comp]
  exact GeometricAffineDescendedFunctor318.map_comp h.tensor k.tensor

/-- Compatible actual covering isomorphisms descend to actual base-line
isomorphisms; the supplied inverse equations concern original sheaf maps. -/
@[expose] def iso {D E : Datum R S} (h : Hom D E) (k : Hom E D)
    (hk : h.sheafHom ≫ k.sheafHom = 𝟙 D.line.object)
    (kh : k.sheafHom ≫ h.sheafHom = 𝟙 E.line.object) : (line D).object ≅ (line E).object :=
  GeometricAffineDescendedFunctor318.iso h.tensor k.tensor hk kh

/-- Transition maps with an actual covering cocycle descend with exactly
that cocycle. No independently assumed base transition equation is used. -/
lemma map_cocycle {D E F : Datum R S} (h : Hom D E) (k : Hom E F) (j : Hom D F)
    (hj : h.sheafHom ≫ k.sheafHom = j.sheafHom) : map h ≫ map k = map j :=
  GeometricAffineDescendedFunctor318.map_cocycle h.tensor k.tensor j.tensor hj
end ActualAffineDescendedMaps318
