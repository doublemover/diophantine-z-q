module
public import Mathlib.Algebra.Category.ModuleCat.Descent
public section
noncomputable section
namespace AffineCoalgebraModule318
open CategoryTheory
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
abbrev adjunction : ModuleCat.extendScalars.{u, u, u} f ⊣
    ModuleCat.restrictScalars.{u} f := ModuleCat.extendRestrictScalarsAdj f
abbrev Data := (adjunction f).toComonad.Coalgebra

/-- The actual pinned faithfully flat comonadicity theorem, applied to the
original extension/restriction adjunction. Input is a genuine coalgebra,
not geometric overlap data silently redefined as such. -/
@[expose] def equivalence (hf : f.FaithfullyFlat) : ModuleCat.{u} R ≌ Data f := by
  let : (Comonad.comparison (adjunction f)).IsEquivalence :=
    (comonadicExtendScalars hf).eqv
  exact (Comonad.comparison (adjunction f)).asEquivalence

@[expose] def descended (hf : f.FaithfullyFlat) (D : Data f) : ModuleCat.{u} R :=
  (equivalence f hf).inverse.obj D

@[expose] def coalgebraIso (hf : f.FaithfullyFlat) (D : Data f) :
    (Comonad.comparison (adjunction f)).obj (descended f hf D) ≅ D :=
  (equivalence f hf).counitIso.app D

/-- The reconstructed module has the exact original covering module as
its scalar extension, through the actual coalgebra counit isomorphism. -/
@[expose] def moduleIso (hf : f.FaithfullyFlat) (D : Data f) :
    (ModuleCat.extendScalars f).obj (descended f hf D) ≅ D.A :=
  (adjunction f).toComonad.forget.mapIso (coalgebraIso f hf D)

lemma coaction_compatibility (hf : f.FaithfullyFlat) (D : Data f) :
    (ModuleCat.extendScalars f).map ((adjunction f).unit.app (descended f hf D)) ≫
      (adjunction f).toComonad.toFunctor.map (moduleIso f hf D).hom =
    (moduleIso f hf D).hom ≫ D.a :=
  (coalgebraIso f hf D).hom.h

/-- Every original coalgebra-compatible map between scalar extensions
comes from one and only one original base module map. -/
lemma unique_morphism (hf : f.FaithfullyFlat) (M N : ModuleCat.{u} R)
    (a : (Comonad.comparison (adjunction f)).obj M ⟶
      (Comonad.comparison (adjunction f)).obj N) :
    ∃! h : M ⟶ N, (ModuleCat.extendScalars f).map h = a.f := by
  let : (Comonad.comparison (adjunction f)).IsEquivalence :=
    (comonadicExtendScalars hf).eqv
  let F := Comonad.comparison (adjunction f)
  refine ⟨F.preimage a, congrArg Comonad.Coalgebra.Hom.f (F.map_preimage a), ?_⟩
  intro h hh
  apply F.map_injective
  apply Comonad.Coalgebra.Hom.ext
  exact hh.trans (congrArg Comonad.Coalgebra.Hom.f (F.map_preimage a)).symm
end AffineCoalgebraModule318
