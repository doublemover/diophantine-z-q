module
public import CanonicalActualDescentLaws318
public import ActualAffineDescendedMaps318
public import LineSheafPullback318
public section
noncomputable section
namespace CanonicalActualDescentFunctor318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ActualAffineDescentData318 ActualAffineDoubleNerve318 CanonicalSheafOverlap318
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {B U D : Scheme.{u}} {M N : B.Modules} (f : U ⟶ B)

/-- Every original base morphism respects the canonical geometric overlap,
by the actual naturality of both named pullback path comparisons. -/
lemma overlap_natural (g : M ⟶ N) (p₀ p₁ : D ⟶ U) (b : D ⟶ B)
    (h₀ : p₀ ≫ f = b) (h₁ : p₁ ≫ f = b) :
    overlap M f p₀ p₁ b h₀ h₁ ≫
        (Scheme.Modules.pullback p₁).map ((Scheme.Modules.pullback f).map g) =
      (Scheme.Modules.pullback p₀).map ((Scheme.Modules.pullback f).map g) ≫
        overlap N f p₀ p₁ b h₀ h₁ := by
  have h0 := (PullbackPathComposition318.iso p₀ f b h₀).hom.naturality g
  have h1 := (PullbackPathComposition318.iso p₁ f b h₁).inv.naturality g
  change (PullbackPathComposition318.iso p₀ f b h₀).hom.app M ≫
      (PullbackPathComposition318.iso p₁ f b h₁).inv.app M ≫
        (Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback p₁).map g =
    (Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback p₀).map g ≫
      (PullbackPathComposition318.iso p₀ f b h₀).hom.app N ≫
        (PullbackPathComposition318.iso p₁ f b h₁).inv.app N
  rw [← h1, ← Category.assoc, ← h0, Category.assoc]

variable (R S : CommRingCat.{u}) [Algebra R S]

/-- Every original affine base line has canonical actual-double descent
data. The genuine diagonal and triple equations are proved, not supplied. -/
@[expose] def datum (L : Line (Spec R)) : Datum R S where
  line := LineSheafPullback318.line (baseMap R S) L
  overlap := actual L.object (baseMap R S)
  diagonal := CanonicalActualDescentLaws318.diagonal_identity L.object (baseMap R S)
    (Spec.map (𝟙 S)) (Spec.map_id S).symm
  triple := CanonicalActualDescentLaws318.triple L.object (baseMap R S)

/-- Original affine base maps induce actual geometric descent morphisms,
with the unchanged original Scheme.Modules.pullback as underlying map. -/
@[expose] def map {L K : Line (Spec R)} (g : L.object ⟶ K.object) : Hom (datum R S L) (datum R S K) where
  sheafHom := (Scheme.Modules.pullback (baseMap R S)).map g
  commutes := overlap_natural (baseMap R S) g
    (ActualOverlapDiagram318.first (baseMap R S)) (ActualOverlapDiagram318.second (baseMap R S))
    (ActualOverlapDiagram318.first (baseMap R S) ≫ baseMap R S) rfl
    (ActualOverlapDiagram318.edge_condition (baseMap R S)).symm

lemma map_identity (L : Line (Spec R)) : map R S (𝟙 L.object) = Hom.id (datum R S L) :=
  Hom.ext ((Scheme.Modules.pullback (baseMap R S)).map_id L.object)

lemma map_composition {L K Q : Line (Spec R)} (g : L.object ⟶ K.object) (h : K.object ⟶ Q.object) :
    map R S (g ≫ h) = (map R S g).comp (map R S h) :=
  Hom.ext ((Scheme.Modules.pullback (baseMap R S)).map_comp g h)
end CanonicalActualDescentFunctor318
