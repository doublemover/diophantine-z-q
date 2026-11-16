module
public import ActualTwoDescentOpenImmersionImageFrame318
public section
noncomputable section
namespace ActualTwoDescentOriginalIdealOpenFrameCover318
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalDegreeZeroIdealSheaf318
open ActualTwoDescentRootPrincipalOpenCover318 ActualTwoDescentOriginalRootIdealRestrictionComparison318
open ActualTwoDescentOriginalGlobalRootAffineFrames318 ActualTwoDescentOriginalIdealInfinityFrame318
open ActualTwoDescentOriginalRootRefinedCover318 ActualTwoDescentOpenImmersionImageFrame318
universe u
variable {K : Type u} [Field K] [CharZero K]

def chart (n : K) (i : Fin 3) : Option Bool → Scheme
  | none => infinityScheme n
  | some b => Spec (CommRingCat.of (RootChartRing n i b))
def embedding (n : K) (i : Fin 3) : (k : Option Bool) → chart n i k ⟶ originalCubicScheme n
  | none => infinityChart n
  | some b => rootLocalizationMorphism n i b ≫ affineChart n
instance embedding_open (n : K) (i : Fin 3) (k : Option Bool) :
    IsOpenImmersion (embedding n i k) := by cases k <;> infer_instance

def chartFrame (n : K) (i : Fin 3) (k : Option Bool) :
    (originalRootIdealSheaf n i).restrict (embedding n i k) ≅
      SheafOfModules.unit (chart n i k).ringCatSheaf := by
  cases k with
  | none => exact originalInfinityFrame n i
  | some b => exact originalGlobalAffineFrame n i b

def opens (n : K) (i : Fin 3) (k : ULift.{u} (Option Bool)) : (originalCubicScheme n).Opens :=
  (embedding n i k.down).opensRange

lemma actual_open_cover (n : K) (hn : n≠0) (i : Fin 3) :
    (⊤ : (originalCubicScheme n).Opens) ≤ ⨆ k, opens n i k := by
  intro x _
  rcases actual_original_root_refinement_covers n hn i x with ⟨b,q,hq⟩|⟨q,hq⟩
  · apply Opens.mem_iSup.mpr
    exact ⟨⟨some b⟩,q,hq⟩
  · apply Opens.mem_iSup.mpr
    exact ⟨⟨none⟩,q,hq⟩

def openFrame (n : K) (i : Fin 3) (k : ULift.{u} (Option Bool)) :
    SheafOfModules.unit (opens n i k).toScheme.ringCatSheaf ≅
      (originalRootIdealSheaf n i).restrict (opens n i k).ι :=
  imageFrame (embedding n i k.down) (originalRootIdealSheaf n i) (chartFrame n i k.down)
end ActualTwoDescentOriginalIdealOpenFrameCover318
