module
public import InfinityMonicPresentation318
public import SpecSchematicDensity318
public import SchematicEqualityExtension318
public import WeierstrassBaseChange318
public import CubicClosedImmersion318
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import all WeierstrassGluing318
import all WeierstrassBaseChange318
public section
noncomputable section
namespace FiniteChartSchematicDensity318
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open WeierstrassOverlap318 WeierstrassGluing318
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R:Type u} [CommRing R] (A B:R)

theorem infinity_localization_injective : Function.Injective
    (algebraMap (Infinity A B) (InfinityOverlap A B)):=by
  apply IsLocalization.injective (M:=Submonoid.powers (InfinityChart318.z A B))
  rintro q ⟨n,rfl⟩
  exact (nonZeroDivisors (Infinity A B)).pow_mem
    (InfinityMonicPresentation318.z_regular A B) n

instance intoInfinity_dense : IsSchemeTheoreticallyDominant (intoInfinity A B):=by
  exact SpecSchematicDensity318.spec_of_injective
    (CommRingCat.ofHom (algebraMap (Infinity A B) (InfinityOverlap A B)))
    (infinity_localization_injective A B)

/-- Actual finite chart is schematically dense in the whole glued curve,
for arbitrary commutative bases, including rings with nilpotents. -/
theorem finiteChart_dense : IsSchemeTheoreticallyDominant (finiteChart A B):=by
  have hI:(intoInfinity A B≫infinityChart A B).ker=(infinityChart A B).ker:=by
    rw [Scheme.Hom.ker_comp,(intoInfinity A B).ker_eq_bot,Scheme.IdealSheafData.map_bot]
  have hle:(finiteChart A B).ker≤(infinityChart A B).ker:=by
    rw [←hI]
    rw [show intoInfinity A B≫infinityChart A B=intoAffine A B≫finiteChart A B
      from (pushout.condition).symm]
    exact Scheme.Hom.le_ker_comp _ _
  constructor
  apply le_antisymm ?_ bot_le
  rw [←Scheme.Hom.ker_eq_bot_of_isIso (𝟙 (scheme A B)),
    ←Scheme.Hom.iInf_ker_openCover_map_comp (𝟙 (scheme A B)) (WeierstrassBaseChange318.twoChartCover A B)]
  apply le_iInf
  intro b
  cases b
  · change (finiteChart A B).ker≤(infinityChart A B≫𝟙 _).ker
    simpa using hle
  · change (finiteChart A B).ker≤(finiteChart A B≫𝟙 _).ker
    simp

/-- Maps to any separated relative target are determined by their actual
finite-chart restriction, with no reducedness or field-point premise. -/
theorem hom_ext {Y Z:Scheme.{u}} (f g:scheme A B⟶Y) (s:Y⟶Z) [IsSeparated s]
    (h:f≫s=g≫s) (hfinite:finiteChart A B≫f=finiteChart A B≫g):f=g:=by
  letI:=finiteChart_dense A B
  exact SchematicEqualityExtension318.ext s h (finiteChart A B) hfinite

/-- Concrete equality extension into another actual completed short cubic. -/
theorem hom_ext_to_completed (A' B':R) (f g:scheme A B⟶scheme A' B')
    (h:f≫structureMap A' B'=g≫structureMap A' B')
    (hfinite:finiteChart A B≫f=finiteChart A B≫g):f=g:=by
  letI:=CubicClosedImmersion318.structure_proper A' B'
  exact hom_ext A B f g (structureMap A' B') h hfinite
end FiniteChartSchematicDensity318

