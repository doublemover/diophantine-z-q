module
public import OriginalOpenPullbackSections318
import all OriginalOpenPullbackSections318
public import ContactOriginalRestrictionCoordinates318
public section
noncomputable section
namespace ContactWholeOpenSectionRestriction318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalLaurentOverlap318 ContactOriginalLineBothCharts318
variable (c : Fin 4 → ℚˣ) (L : Line (ContactProjectiveModel318.model c))

private lemma path_imageLE {X Y Z : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]
    (g : Y ⟶ Z) [IsOpenImmersion g] (k : X ⟶ Z) [IsOpenImmersion k]
    (h : f ≫ g=k) : k ''ᵁ ⊤ ≤ g ''ᵁ ⊤ := by
  have he : (⟨f ≫ g, inferInstance⟩ : {l : X ⟶ Z // IsOpenImmersion l}) =
      ⟨k, inferInstance⟩ := Subtype.ext h
  have hi := congrArg (fun l : {l : X ⟶ Z // IsOpenImmersion l} => by
    letI : IsOpenImmersion l.val := l.property
    exact l.val ''ᵁ (⊤ : X.Opens)) he
  exact hi ▸ OpenChartSections318.imageLE f g

/-- Actual full finite-chart image sections of the original GLOBAL line. -/
def finiteSectionsEquiv : finiteSections c L ≃+
    Γ(L.object,(SourceGlobalAffine318.chartEmbedding c) ''ᵁ ⊤) :=
  OriginalOpenPullbackSections318.sectionsEquiv (SourceGlobalAffine318.chartEmbedding c) L.object

/-- Actual full infinity-chart image sections, retaining the same line. -/
def infinitySectionsEquiv : infinitySections c L ≃+
    Γ(L.object,(ContactWholeInfinityScheme318.into c) ''ᵁ ⊤) :=
  OriginalOpenPullbackSections318.sectionsEquiv (ContactWholeInfinityScheme318.into c) L.object

/-- The actual whole overlap line sections, before coordinate choices. -/
def overlapSectionsEquiv : Γ((ContactOriginalLineOverlap318.line c L).object,⊤) ≃+
    Γ(L.object,(into c) ''ᵁ ⊤) :=
  OriginalOpenPullbackSections318.sectionsEquiv (into c) L.object

/-- Direct geometric finite-chart restriction, using the original pullback
unit and the unchanged exact path comparison into the whole overlap. -/
def finiteDirect (m : finiteSections c L) : Γ((ContactOriginalLineOverlap318.line c L).object,⊤) :=
  ((ContactOriginalLineOverlap318.finiteComparison c L).hom).app ⊤
    (OriginalOpenPullbackSections318.sectionPull (finiteEdge c)
      ((Scheme.Modules.pullback (SourceGlobalAffine318.chartEmbedding c)).obj L.object) m)

def infinityDirect (m : infinitySections c L) : Γ((ContactOriginalLineOverlap318.line c L).object,⊤) :=
  ((ContactOriginalLineOverlap318.infinityComparison c L).hom).app ⊤
    (OriginalOpenPullbackSections318.sectionPull (infinityEdge c)
      ((Scheme.Modules.pullback (ContactWholeInfinityScheme318.into c)).obj L.object) m)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Exact restriction of original ambient finite-chart sections to the full
original intersection; no local or coefficient compatibility is supplied. -/
lemma finite_square (m : finiteSections c L) :
    overlapSectionsEquiv c L (finiteDirect c L m) =
      L.object.presheaf.map (homOfLE (show (into c) ''ᵁ ⊤ ≤
        (SourceGlobalAffine318.chartEmbedding c) ''ᵁ ⊤ by
          exact path_imageLE (finiteEdge c) (SourceGlobalAffine318.chartEmbedding c)
            (into c) (finiteEdge_into c))).op
        (finiteSectionsEquiv c L m) := by
  dsimp only [overlapSectionsEquiv,finiteDirect,finiteSectionsEquiv]
  rw [ContactOriginalLineOverlap318.finiteComparison_hom]
  exact OriginalOpenPullbackSections318.nested_path (finiteEdge c)
    (SourceGlobalAffine318.chartEmbedding c) (into c) (finiteEdge_into c) L.object m

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The same original ambient restriction square on the entire infinity
chart, with its unchanged comparison and no reduced-open restriction. -/
lemma infinity_square (m : infinitySections c L) :
    overlapSectionsEquiv c L (infinityDirect c L m) =
      L.object.presheaf.map (homOfLE (show (into c) ''ᵁ ⊤ ≤
        (ContactWholeInfinityScheme318.into c) ''ᵁ ⊤ by
          exact path_imageLE (infinityEdge c) (ContactWholeInfinityScheme318.into c)
            (into c) (infinityEdge_into c))).op
        (infinitySectionsEquiv c L m) := by
  dsimp only [overlapSectionsEquiv,infinityDirect,infinitySectionsEquiv]
  rw [ContactOriginalLineOverlap318.infinityComparison_hom]
  exact OriginalOpenPullbackSections318.nested_path (infinityEdge c)
    (ContactWholeInfinityScheme318.into c) (into c) (infinityEdge_into c) L.object m
end ContactWholeOpenSectionRestriction318
