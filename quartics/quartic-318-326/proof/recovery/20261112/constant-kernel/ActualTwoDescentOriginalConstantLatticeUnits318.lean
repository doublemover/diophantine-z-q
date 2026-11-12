module
public import ActualTwoDescentOriginalKernelStalkRegularity318
public section
noncomputable section
namespace ActualTwoDescentOriginalConstantLatticeUnits318
open AlgebraicGeometry CategoryTheory
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalSchemeIntegral318
open ActualTwoDescentOriginalDoublePoleLocalGlobal318
variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
local instance (n : K) : Nonempty (⊤ : (originalCubicScheme n).Opens) := ⟨⟨genericPoint _,trivial⟩⟩
local instance (n : K) : IsProper (structureMap n) := ActualTwoDescentOriginalSeparatedComparison318.proper n
/-- Canonical base coefficient in the ACTUAL generic stalk, through
native global sections and the literal original structure map. -/
def baseCoefficient (n : K) : K →+* SchemeFunctionField n :=
  ((originalCubicScheme n).germToFunctionField ⊤).hom.comp
    (ActualTwoDescentProperClosedFieldConstants318.structural (structureMap n))
/-- FULL constant-unit classification in the algebraically closed
geometric setting needed for E[2]. No arbitrary native-lift equivalence
is assumed, and no claim over a nonclosed field is smuggled in. -/
lemma constant_unit (n : K) (a : (SchemeFunctionField n)ˣ)
    (ha : ∀ x f,f∈pointImage n x ↔ (a:SchemeFunctionField n)*f∈pointImage n x) :
    ∃! c : Kˣ,baseCoefficient n (c:K)=(a:SchemeFunctionField n) := by
  obtain ⟨s,hs⟩ := ActualTwoDescentOriginalKernelStalkRegularity318.global_unit n a ha
  obtain ⟨c,hc,_⟩ := ActualTwoDescentProperClosedFieldConstants318.units (structureMap n) s
  have hc' : baseCoefficient n (c:K)=(a:SchemeFunctionField n) := by
    change (originalCubicScheme n).germToFunctionField ⊤
      (ActualTwoDescentProperClosedFieldConstants318.structural (structureMap n) (c:K))=_
    rw [hc,hs]
  refine ⟨c,hc',?_⟩
  intro d hd
  apply Units.ext
  exact (baseCoefficient n).injective (hd.trans hc'.symm)

end ActualTwoDescentOriginalConstantLatticeUnits318
