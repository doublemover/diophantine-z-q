module
public import CanonicalTildeMorphismTransport318
public section
noncomputable section
namespace ActualTildeMorphismDescent318
open AlgebraicGeometry CategoryTheory
open ActualAffineDoubleNerve318 ActualOverlapDiagram318
open CanonicalSheafOverlap318 CanonicalTildeMorphismTransport318
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R S : CommRingCat.{u}) [Algebra R S] [Module.FaithfullyFlat R S]
  {M N : ModuleCat R}

/-- Original canonical descent maps between affine tilde objects, on the
actual categorical double rather than a replacement tensor diagram. -/
structure Map (M N : ModuleCat R) where
  hom : (Scheme.Modules.pullback (baseMap R S)).obj (tilde M) ⟶
    (Scheme.Modules.pullback (baseMap R S)).obj (tilde N)
  compatible : actual (tilde M) (baseMap R S) ≫
      (Scheme.Modules.pullback (second (baseMap R S))).map hom =
    (Scheme.Modules.pullback (first (baseMap R S))).map hom ≫ actual (tilde N) (baseMap R S)

/-- The original actual-double square supplies the canonical scalar map;
the full scheme-to-tensor transport and both endpoint comparisons are used. -/
@[expose] def scalarMap (f : Map R S M N) : CanonicalScalarMorphismDescent318.Map R S M N where
  hom := moduleMap (CanonicalTildeOverlap318.ringMap R S) f.hom
  compatible := by
    apply scalar_square R S f.hom
    have h := SheafTransportIntertwiner318.square f.hom (doubleIso R S).inv
      (first (baseMap R S)) (second (baseMap R S))
      (Spec.map (AffineModuleBaseChange318.leftMap R S S))
      (Spec.map (AffineModuleBaseChange318.rightMap R S S))
      (inverse_first R S) (inverse_second R S)
      (actual (tilde M) (baseMap R S)) (actual (tilde N) (baseMap R S)) f.compatible
    rw [ActualCanonicalOverlap318.transport, ActualCanonicalOverlap318.transport] at h
    exact h

@[expose] def descend (f : Map R S M N) : tilde M ⟶ tilde N :=
  (tilde.functor R).map (CanonicalScalarMorphismDescent318.descend R S (scalarMap R S f))

/-- The reconstructed original base sheaf map pulls back to the exact
original covering map, not just to an isomorphic scalar representation. -/
lemma descend_cover (f : Map R S M N) :
    (Scheme.Modules.pullback (baseMap R S)).map (descend R S f) = f.hom := by
  let a := TildePullback318.pullbackIso (CanonicalTildeOverlap318.ringMap R S)
  apply (cancel_mono (a.hom.app N)).mp
  have hn := a.hom.naturality
    (CanonicalScalarMorphismDescent318.descend R S (scalarMap R S f))
  change (Scheme.Modules.pullback (baseMap R S)).map (descend R S f) ≫ a.hom.app N =
    a.hom.app M ≫ (tilde.functor S).map
      ((ModuleCat.extendScalars (algebraMap R S)).map
        (CanonicalScalarMorphismDescent318.descend R S (scalarMap R S f))) at hn
  rw [hn, CanonicalScalarMorphismDescent318.descend_cover]
  change a.hom.app M ≫ (tilde.functor S).map
    (moduleMap (CanonicalTildeOverlap318.ringMap R S) f.hom) = _
  rw [moduleMap, Functor.map_preimage]
  simp only [a, Category.assoc, Iso.hom_inv_id_app_assoc]

lemma descend_unique (f : Map R S M N) (g : tilde M ⟶ tilde N)
    (h : (Scheme.Modules.pullback (baseMap R S)).map g = f.hom) : g = descend R S f :=
  FaithfullyFlatTildeFaithful318.pullback_map_injective R S g (descend R S f)
    (h.trans (descend_cover R S f).symm)

/-- All original geometric compatible maps descend uniquely between the
original base tilde objects, with the literal pullback equation. -/
theorem effective (f : Map R S M N) :
    ∃! g : tilde M ⟶ tilde N, (Scheme.Modules.pullback (baseMap R S)).map g = f.hom :=
  ⟨descend R S f, descend_cover R S f, descend_unique R S f⟩
end ActualTildeMorphismDescent318
