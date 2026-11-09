module
public import ActualAffineSheafData318
public section
noncomputable section
namespace ActualAffineTensorTransport318
open AlgebraicGeometry CategoryTheory LineSheafClass318 AffineModuleBaseChange318
open AffineCechRings318 ActualAffineDoubleNerve318 ActualAffineTripleMaps318 ActualAffineTripleNerve318
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

/-- The retained affine named comparison is exactly the generic canonical
sheaf path comparison, including both Spec equality transports. -/
lemma affine_path {A B C : CommRingCat.{u}} (f : A ⟶ B) (g : B ⟶ C) (h : A ⟶ C)
    (hh : g.hom.comp f.hom = h.hom) :
    OriginalLineNamedComparison318.pullbackAlong f g h hh =
      PullbackPathComposition318.iso (Spec.map g) (Spec.map f) (Spec.map h)
        (spec_path f g h hh) := by
  have hp := OriginalLineNamedComparison318.ring_path hh
  subst h
  apply Iso.ext
  simp only [OriginalLineNamedComparison318.pullbackAlong,
    AffineComparisonMates318.pullbackComp, PullbackPathComposition318.iso,
    Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.trans_hom, Iso.refl_hom,
    Category.comp_id, Category.assoc]

variable (R S : CommRingCat.{u}) [Algebra R S] (L : Line (Spec S))
  (τ : ActualAffineSheafData318.firstObject R S L ⟶ ActualAffineSheafData318.secondObject R S L)

/-- The original actual overlap, pulled along the actual double comparison
and canonically normalized to the original tensor-spectrum endpoints. -/
@[expose] def overlap : OriginalLineOverlapCoaction318.first R S L ⟶
    OriginalLineOverlapCoaction318.second R S L :=
  SheafPathTransport318.transport L.object (doubleIso R S).inv
    (ActualOverlapDiagram318.first (baseMap R S)) (ActualOverlapDiagram318.second (baseMap R S))
    (Spec.map (leftMap R S S)) (Spec.map (rightMap R S S))
    (inverse_first R S) (inverse_second R S) τ

/-- Every actual pair-map square transports its canonically normalized
sheaf edge to the exact tensor-spectrum geometric edge. -/
lemma face (q : ActualOverlapDiagram318.Triple (baseMap R S) ⟶
      ActualOverlapDiagram318.Double (baseMap R S))
    (m : double R S ⟶ triple R S)
    (v w : ActualOverlapDiagram318.Triple (baseMap R S) ⟶ Spec S)
    (v' w' : S ⟶ triple R S)
    (hs : (tripleIso R S).inv ≫ q = Spec.map m ≫ (doubleIso R S).inv)
    (hq₀ : q ≫ ActualOverlapDiagram318.first (baseMap R S) = v)
    (hq₁ : q ≫ ActualOverlapDiagram318.second (baseMap R S) = w)
    (hv : (tripleIso R S).inv ≫ v = Spec.map v')
    (hw : (tripleIso R S).inv ≫ w = Spec.map w')
    (hm₀ : m.hom.comp (leftMap R S S).hom = v'.hom)
    (hm₁ : m.hom.comp (rightMap R S S).hom = w'.hom) :
    SheafPathTransport318.transport L.object (tripleIso R S).inv v w
      (Spec.map v') (Spec.map w') hv hw
      (SheafPathTransport318.transport L.object q
        (ActualOverlapDiagram318.first (baseMap R S)) (ActualOverlapDiagram318.second (baseMap R S))
        v w hq₀ hq₁ τ) =
    OriginalGeometricEdge318.edge L (leftMap R S S) (rightMap R S S) m v' w' hm₀ hm₁
      (overlap R S L τ) := by
  have h := SheafPathTransport318.square L.object q (tripleIso R S).inv
    (doubleIso R S).inv (Spec.map m) hs
    (ActualOverlapDiagram318.first (baseMap R S)) (ActualOverlapDiagram318.second (baseMap R S))
    v w (Spec.map (leftMap R S S)) (Spec.map (rightMap R S S)) (Spec.map v') (Spec.map w')
    hq₀ hq₁ (inverse_first R S) (inverse_second R S) hv hw
    (spec_path _ _ _ hm₀) (spec_path _ _ _ hm₁) τ
  simpa only [overlap, SheafPathTransport318.transport, OriginalGeometricEdge318.edge,
    affine_path] using h
end ActualAffineTensorTransport318
