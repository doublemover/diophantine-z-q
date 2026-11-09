module
public import AffineStructureHOne318
public import ContactGlobalSmooth318

public section
noncomputable section
namespace ActualSourceAffineHOne318
open AlgebraicGeometry CategoryTheory
open SheafCohomologyRetraction318
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ)
local instance finiteDomain : IsDomain (ContactKummerOrder318.SourceOrder c) :=
  ContactKummerOrder318.source_domain c
local instance infinityDomain : IsDomain (InfinityOpenChart318.OpenOrder c) :=
  InfinityOpenChart318.openOrder_domain c

/-- Vanishing on the actual complete finite chart, retaining all finite branch points. -/
theorem finite_chart_zero
    (x : structureH (Spec (CommRingCat.of (ContactKummerOrder318.SourceOrder c))) 1) : x = 0 :=
  AffineStructureHOne318.structureH_one_zero _ x

/-- Vanishing on the actual original reciprocal infinity neighborhood. -/
theorem infinity_chart_zero
    (x : structureH (ReciprocalInfinityNormalization318.neighborhood c) 1) : x = 0 :=
  AffineStructureHOne318.structureH_one_zero
    (CommRingCat.of (InfinityOpenChart318.OpenOrder c)) x

/-- Both charts are exactly those in the existing open cover of the original global model. -/
theorem cover_chart_zero (b : Bool) (x : structureH ((ContactGlobalSmooth318.cover c).X b) 1) :
    x = 0 := by
  cases b
  · exact finite_chart_zero c x
  · exact infinity_chart_zero c x

end ActualSourceAffineHOne318
