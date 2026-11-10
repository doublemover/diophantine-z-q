module
public import OriginalAffineLineFaithfulness318
public section
noncomputable section
namespace CanonicalScalarMorphismDescent318
open AlgebraicGeometry CategoryTheory
open AffineModuleBaseChange318 CanonicalScalarOverlap318
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R S : CommRingCat.{u}) [Algebra R S] [Module.FaithfullyFlat R S]
  {M N : ModuleCat R}

/-- Original maps between scalar extensions, compatible with the original
canonical double-overlap maps. No coalgebra equation is an input. -/
structure Map (M N : ModuleCat R) where
  hom : coverModule R S M ⟶ coverModule R S N
  compatible : overlap R S M ≫ (ModuleCat.extendScalars (rightMap R S S).hom).map hom =
    (ModuleCat.extendScalars (leftMap R S S).hom).map hom ≫ overlap R S N

/-- The genuine double-overlap square implies the exact original
comparison-coalgebra morphism equation via the original unit transpose. -/
@[expose] def coalgebraHom (f : Map R S M N) :
    (Comonad.comparison (AffineCoalgebraModule318.adjunction (algebraMap R S))).obj M ⟶
      (Comonad.comparison (AffineCoalgebraModule318.adjunction (algebraMap R S))).obj N where
  f := f.hom
  h := by
    have h := OverlapMorphismCoaction318.module_coaction R S f.hom
      (overlap R S M) (overlap R S N) f.compatible
    rw [canonical_coaction, canonical_coaction] at h
    exact h

/-- Every canonical double-overlap-compatible map comes from exactly one
original base module map, using the actual faithfully flat equivalence. -/
theorem effective (f : Map R S M N) :
    ∃! g : M ⟶ N, (ModuleCat.extendScalars (algebraMap R S)).map g = f.hom :=
  AffineCoalgebraModule318.unique_morphism (algebraMap R S)
    (AffineCoalgebraLine318.faithfullyFlat R S) M N (coalgebraHom R S f)

@[expose] def descend (f : Map R S M N) : M ⟶ N := Classical.choose (effective R S f)

lemma descend_cover (f : Map R S M N) :
    (ModuleCat.extendScalars (algebraMap R S)).map (descend R S f) = f.hom :=
  (Classical.choose_spec (effective R S f)).1

lemma descend_unique (f : Map R S M N) (g : M ⟶ N)
    (h : (ModuleCat.extendScalars (algebraMap R S)).map g = f.hom) : g = descend R S f :=
  (Classical.choose_spec (effective R S f)).2 g h

/-- Scalar reconstruction retains the identity of the base map, rather
than merely supplying an unrelated preimage under an equivalence. -/
lemma descend_original (f : Map R S M N) (g : M ⟶ N)
    (h : f.hom = (ModuleCat.extendScalars (algebraMap R S)).map g) : descend R S f = g :=
  (descend_unique R S f g h.symm).symm

/-- Original inverse equations on the covering modules yield a genuine
isomorphism of the original base modules. -/
@[expose] def descendedIso (f : Map R S M N) (g : Map R S N M)
    (hfg : f.hom ≫ g.hom = 𝟙 _) (hgf : g.hom ≫ f.hom = 𝟙 _) : M ≅ N where
  hom := descend R S f
  inv := descend R S g
  hom_inv_id := by
    apply FaithfullyFlatTildeFaithful318.scalar_map_injective R S
    rw [Functor.map_comp, descend_cover, descend_cover, Functor.map_id, hfg]
  inv_hom_id := by
    apply FaithfullyFlatTildeFaithful318.scalar_map_injective R S
    rw [Functor.map_comp, descend_cover, descend_cover, Functor.map_id, hgf]
end CanonicalScalarMorphismDescent318
