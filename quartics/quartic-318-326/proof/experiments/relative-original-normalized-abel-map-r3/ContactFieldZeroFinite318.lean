module
public import OriginalIntegralPolynomialZeroFinite318
public import OriginalPolynomialChartFree318
public import ContactFieldIntegralLine318
public import ContactOriginalSectionZeros318
public section
noncomputable section
namespace ContactFieldZeroFinite318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalSectionZeros318
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (K : CommRingCat.{0}) [Field K] [Algebra ℚ K] (c : Fin 4 → ℚˣ)
  (L : Line (curve K c)) (s : Γ(L.object,⊤)) (hs : s≠0)
local instance : IsScalarTower ℚ (Polynomial ℚ) (finiteRing c) :=
  IsScalarTower.of_algebraMap_eq' (R:=ℚ) (S:=Polynomial ℚ) (A:=finiteRing c)
    (RingHom.ext_rat _ _)
local instance : IsScalarTower ℚ (Polynomial ℚ) (infinityRing c) :=
  IsScalarTower.of_algebraMap_eq' (R:=ℚ) (S:=Polynomial ℚ) (A:=infinityRing c) rfl
local instance : Module.Finite (Polynomial ℚ) (finiteRing c) :=
  (ContactKummerOrder318.source_finite_free c).1
local instance : Module.Free (Polynomial ℚ) (finiteRing c) :=
  (ContactKummerOrder318.source_finite_free c).2

/-- The actual full finite-chart zero algebra of a nonzero global field
section is finite-dimensional, retaining its evaluation ideal and all
scheme multiplicities. No chosen nonzero polynomial is supplied. -/
lemma finite_chart : Module.Finite K
    ((K ⊗[ℚ] finiteRing c)⧸finiteIdeal K c L s) :=
  OriginalIntegralPolynomialZeroFinite318.open_pull K (CommRingCat.of (K ⊗[ℚ] finiteRing c))
    (finiteInto K c) L s hs

/-- The same finite-dimensionality for the full reciprocal zero chart,
using its separate original polynomial action and the same global section. -/
lemma infinity_chart : Module.Finite K
    ((K ⊗[ℚ] infinityRing c)⧸infinityIdeal K c L s) :=
  OriginalIntegralPolynomialZeroFinite318.open_pull K (CommRingCat.of (K ⊗[ℚ] infinityRing c))
    (infinityInto K c) L s hs
end ContactFieldZeroFinite318
