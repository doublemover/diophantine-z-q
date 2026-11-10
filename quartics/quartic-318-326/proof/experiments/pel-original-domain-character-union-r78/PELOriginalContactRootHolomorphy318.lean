module
public import PELOriginalContactRootFunctions318
public import PELOriginalCommonCubicHolomorphy318
public section
noncomputable section
namespace PELOriginalContactRootHolomorphy318
open Set Filter
open scoped Topology OnePoint Manifold ContDiff
open PELUnlevelledComplexBase318 PELOriginalContactRootFunctions318
open PELOriginalContactBranchSquare318 PELOriginalCommonContactBase318
open PELOriginalCharacterQuotient318 FourCharacterRootRecombination318
local instance : ChartedSpace ℂ UnlevelledBase:=unlevelledCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω UnlevelledBase:=unlevelled_manifold
local instance (i:Fin 4) : ChartedSpace ℂ (CharacterBase i):=
  PELOriginalCharacterTopologicalAtlas318.characterTopologicalCharts i
local instance (i:Fin 4) : IsManifold 𝓘(ℂ,ℂ) ω (CharacterBase i):=
  PELOriginalCharacterComplexAtlas318.character_manifold i
local instance : ChartedSpace ℂ (OnePoint ℂ):=ComplexSphereCharts318.sphereCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω (OnePoint ℂ):=ComplexSphereCharts318.sphere_manifold

lemma base_holomorphic (x:UnlevelledBase) (hx:x∈RegularSource):
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω base x := by
  have hm:ComplexSphereCharts318.affine∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω (OnePoint ℂ):=
    IsManifold.subset_maximalAtlas
      (show ComplexSphereCharts318.affine∈atlas ℂ (OnePoint ℂ) from ⟨false,rfl⟩)
  have hs:normalizedMap x∈ComplexSphereCharts318.affine.source:=by
    rw [normalized_finite x hx]
    exact ComplexSphereCharts318.affine_mem _
  exact (contMDiffAt_of_mem_maximalAtlas hm hs).comp x (holomorphic x)

lemma ordinate_holomorphic (x:UnlevelledBase) (hx:x∈RegularSource) (i:Fin 4):
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω
      (fun p=>PELOriginalCommonCubicCoordinate318.ordinate i (toCharacter i p)) x := by
  let xf:PELOriginalRegularCharacterProduct318.CharacterFiber (basePoint (base x)) i:=
    ⟨toCharacter i x,original_base x hx⟩
  have hr:=PELOriginalCommonCubicFiberEquiv318.fiber_regular (base x) (denominator_ne x hx) i xf
  have ht:=PELOriginalCommonCubicFiberEquiv318.fiber_base (base x) i xf
  exact (PELOriginalCommonCubicHolomorphy318.ordinate_holomorphic i _ hr (base x) ht).comp x
    (PELOriginalCharacterComplexAtlas318.character_projection_holomorphic i x)

/-- Holomorphy of the ACTUAL four functions on the unchanged original
source follows from their same-base triple-product formula and nonzero
full branch polynomial. No independently chosen root is substituted. -/
theorem roots_holomorphic (x:UnlevelledBase) (hx:x∈RegularSource) (k:Fin 4):
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun p=>roots p k) x := by
  have ht:=base_holomorphic x hx
  have hY:=ordinate_holomorphic x hx
  have hn:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω
      (fun p=>triple (fun i=>PELOriginalCommonCubicCoordinate318.ordinate i (toCharacter i p)) k) x:=by
    fin_cases k
    · exact ((hY 1).mul (hY 2)).mul (hY 3)
    · exact ((hY 0).mul (hY 2)).mul (hY 3)
    · exact ((hY 0).mul (hY 1)).mul (hY 3)
    · exact ((hY 0).mul (hY 1)).mul (hY 2)
  have hd:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω
      (fun p=>denominator branches (base p)) x:=
    (((ht.sub contMDiffAt_const).mul (ht.sub contMDiffAt_const)).mul
      (ht.sub contMDiffAt_const)).mul (ht.sub contMDiffAt_const)
  exact hn.div hd (denominator_ne x hx)
end PELOriginalContactRootHolomorphy318
