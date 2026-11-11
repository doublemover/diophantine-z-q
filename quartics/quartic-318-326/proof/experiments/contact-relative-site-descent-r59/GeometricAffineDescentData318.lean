module
public import OverlapMorphismCoaction318
public section
noncomputable section
namespace GeometricAffineDescentData318
open AlgebraicGeometry CategoryTheory LineSheafClass318 AffineModuleBaseChange318
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R S : CommRingCat.{u}) [Algebra R S]

/-- Original geometric line data on the actual affine tensor spectra.
This is not an alias for module coalgebras. -/
structure Datum where
  line : Line (Spec S)
  overlap : OriginalLineOverlapCoaction318.first R S line ⟶
    OriginalLineOverlapCoaction318.second R S line
  diagonal : OriginalGeometricDiagonal318.Diagonal R S line overlap
  triple : OriginalGeometricTriple318.Cocycle R S line overlap

variable {R S}
structure Hom (D E : Datum R S) where
  sheafHom : D.line.object ⟶ E.line.object
  commutes : D.overlap ≫ (Scheme.Modules.pullback (Spec.map (rightMap R S S))).map sheafHom =
    (Scheme.Modules.pullback (Spec.map (leftMap R S S))).map sheafHom ≫ E.overlap

@[ext] lemma Hom.ext {D E : Datum R S} {h k : Hom D E}
    (hh : h.sheafHom = k.sheafHom) : h = k := by
  cases h
  cases k
  cases hh
  rfl

@[expose] def Hom.id (D : Datum R S) : Hom D D where
  sheafHom := 𝟙 _
  commutes := by
    have hr : (Scheme.Modules.pullback (Spec.map (rightMap R S S))).map (𝟙 D.line.object)=
        𝟙 (OriginalLineOverlapCoaction318.second R S D.line) :=
      (Scheme.Modules.pullback (Spec.map (rightMap R S S))).map_id D.line.object
    have hl : (Scheme.Modules.pullback (Spec.map (leftMap R S S))).map (𝟙 D.line.object)=
        𝟙 (OriginalLineOverlapCoaction318.first R S D.line) :=
      (Scheme.Modules.pullback (Spec.map (leftMap R S S))).map_id D.line.object
    exact (congrArg (fun k => D.overlap ≫ k) hr).trans
      ((Category.comp_id D.overlap).trans ((Category.id_comp D.overlap).symm.trans
        (congrArg (fun k => k ≫ D.overlap) hl.symm)))

@[expose] def Hom.comp {D E F : Datum R S} (h : Hom D E) (k : Hom E F) : Hom D F where
  sheafHom := h.sheafHom ≫ k.sheafHom
  commutes := by
    rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, h.commutes,
      Category.assoc, k.commutes, ← Category.assoc]

/-- Coalgebra structure is derived from the genuine geometric laws. -/
abbrev coalgebra (D : Datum R S) := AffineOverlapCoassociativity318.coalgebra R S
  (OriginalLineAffineModel318.sections S D.line)
  (OriginalLineOverlapCoaction318.moduleHomEquiv R S D.line D.overlap)
  (AffineSplitDiagonalTranspose318.diagonal_to_module R S D.line D.overlap D.diagonal)
  (OriginalGeometricTriple318.cocycle_to_module R S D.line D.overlap D.triple)

@[expose] def Hom.coalgebraHom {D E : Datum R S} (h : Hom D E) : coalgebra D ⟶ coalgebra E where
  f := moduleSpecΓFunctor.map h.sheafHom
  h := OverlapMorphismCoaction318.geometric_coaction R S D.line E.line
    h.sheafHom D.overlap E.overlap h.commutes

@[reassoc] lemma Hom.coalgebraHom_comp {D E F : Datum R S} (h : Hom D E) (k : Hom E F) :
    (h.comp k).coalgebraHom = h.coalgebraHom ≫ k.coalgebraHom := by
  apply Comonad.Coalgebra.Hom.ext
  exact moduleSpecΓFunctor.map_comp h.sheafHom k.sheafHom

lemma Hom.coalgebraHom_id (D : Datum R S) : (Hom.id D).coalgebraHom = 𝟙 (coalgebra D) := by
  apply Comonad.Coalgebra.Hom.ext
  exact moduleSpecΓFunctor.map_id D.line.object

variable [Module.FaithfullyFlat R S]
abbrev descended (D : Datum R S) := AffineCoalgebraModule318.descended (algebraMap R S)
  (AffineCoalgebraLine318.faithfullyFlat R S) (coalgebra D)
abbrev moduleIso (D : Datum R S) := AffineCoalgebraModule318.moduleIso (algebraMap R S)
  (AffineCoalgebraLine318.faithfullyFlat R S) (coalgebra D)

@[expose] def Hom.baseModuleMap {D E : Datum R S} (h : Hom D E) : descended D ⟶ descended E :=
  (AffineCoalgebraModule318.equivalence (algebraMap R S)
    (AffineCoalgebraLine318.faithfullyFlat R S)).inverse.map h.coalgebraHom

/-- The descended module map retains the actual original section map via
the original equivalence's counit, rather than an unrelated module isomorphism. -/
lemma Hom.baseModuleMap_commutes {D E : Datum R S} (h : Hom D E) :
    (ModuleCat.extendScalars (algebraMap R S)).map h.baseModuleMap ≫ (moduleIso E).hom =
      (moduleIso D).hom ≫ moduleSpecΓFunctor.map h.sheafHom := by
  exact congrArg Comonad.Coalgebra.Hom.f
    ((AffineCoalgebraModule318.equivalence (algebraMap R S)
      (AffineCoalgebraLine318.faithfullyFlat R S)).counitIso.hom.naturality h.coalgebraHom)
end GeometricAffineDescentData318
