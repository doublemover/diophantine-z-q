module
public import ContactOriginalLaurentOverlap318
public import PullbackPathComposition318

public section
noncomputable section
namespace ContactOriginalLineOverlap318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalLaurentOverlap318 ContactOriginalLineBothCharts318
variable (c : Fin 4 → ℚˣ) (L : Line (ContactProjectiveModel318.model c))

/-- The SAME original line pulled directly to the entire actual overlap. -/
abbrev line := LineSheafPullback318.line (into c) L

/-- Original finite-chart pullback, compared along its proved literal path. -/
def finiteComparison :
    (Scheme.Modules.pullback (finiteEdge c)).obj (finiteLine c L).object ≅ (line c L).object :=
  (PullbackPathComposition318.iso (finiteEdge c) (SourceGlobalAffine318.chartEmbedding c)
    (into c) (finiteEdge_into c)).app L.object

/-- Original infinity-chart pullback, compared along its proved literal path. -/
def infinityComparison :
    (Scheme.Modules.pullback (infinityEdge c)).obj (infinityLine c L).object ≅ (line c L).object :=
  (PullbackPathComposition318.iso (infinityEdge c) (ContactWholeInfinityScheme318.into c)
    (into c) (infinityEdge_into c)).app L.object

/-- The actual overlap isomorphism goes from infinity coordinates to finite
coordinates, with no supplied compatibility or cohomological premise. -/
def transition :
    (Scheme.Modules.pullback (infinityEdge c)).obj (infinityLine c L).object ≅
    (Scheme.Modules.pullback (finiteEdge c)).obj (finiteLine c L).object :=
  infinityComparison c L ≪≫ (finiteComparison c L).symm

@[reassoc] lemma transition_recovery : (transition c L).hom ≫ (finiteComparison c L).hom =
    (infinityComparison c L).hom := by
  simp only [transition,Iso.trans_hom,Iso.symm_hom,Category.assoc,Iso.inv_hom_id,Category.comp_id]

abbrev ring : CommRingCat := Γ(scheme c,⊤)
abbrev fromSpec : Spec (ring c) ⟶ scheme c := (isAffineOpen_top (scheme c)).fromSpec

/-- The original actual-affine section comparison, obtained by pulling the
same geometric transition along the canonical original fromSpec map. -/
@[expose] def sectionTransition :
    moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (fromSpec c)).obj
      ((Scheme.Modules.pullback (infinityEdge c)).obj (infinityLine c L).object)) ≅
    moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (fromSpec c)).obj
      ((Scheme.Modules.pullback (finiteEdge c)).obj (finiteLine c L).object)) :=
  moduleSpecΓFunctor.mapIso ((Scheme.Modules.pullback (fromSpec c)).mapIso (transition c L))

/-- This section map is literally induced by the original geometric overlap
isomorphism. No abstract vector-space isomorphism is chosen in its place. -/
lemma sectionTransition_hom : (sectionTransition c L).hom =
    moduleSpecΓFunctor.map ((Scheme.Modules.pullback (fromSpec c)).map (transition c L).hom) := rfl
end ContactOriginalLineOverlap318
