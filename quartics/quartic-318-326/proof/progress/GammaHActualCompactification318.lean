module
public import GammaHCompactQuotient318
public section
noncomputable section
open Function Filter Topology TopologicalSpace
open GammaHGroup318 GammaHDiamond318 GammaHAction318 GammaHCuspEnds318
open GammaHCompactAction318 GammaHCompactQuotient318
namespace GammaHActualCompactification318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

variable (N:ℕ) (hN:5≤N) [NeZero N] (H:Subgroup (ZMod N)ˣ)

/-- The genuine Gamma_H orbit quotient itself embeds into the constructed
compact H quotient, through the proved concrete diamond homeomorphism. -/
@[expose] def original : GammaHQuotient318.Curve N H→CompactCurve N hN H :=
  originalMap N hN H ∘ (GammaHDiamondQuotient318.actualHomeomorph N H).symm

theorem original_projection (tau:UpperHalfPlane) :
    original N hN H (GammaHQuotient318.projection N H tau)=
      projection N hN H (AllCuspFilling318.original N hN (GammaOneAtlas318.quotientMap N tau)) := rfl

theorem original_openEmbedding : IsOpenEmbedding (original N hN H) :=
  (originalMap_openEmbedding N hN H).comp (GammaHDiamondQuotient318.actualHomeomorph N H).symm.isOpenEmbedding

theorem original_dense : DenseRange (original N hN H) :=
  (originalMap_dense N hN H).comp (GammaHDiamondQuotient318.actualHomeomorph N H).symm.surjective.denseRange
    (originalMap_continuous N hN H)

theorem range_original : Set.range (original N hN H)=(Set.range (cuspMap N hN H))ᶜ := by
  rw [original,Set.range_comp,(GammaHDiamondQuotient318.actualHomeomorph N H).symm.surjective.range_eq,
    Set.image_univ,range_originalMap]

theorem original_j (z:GammaHQuotient318.Curve N H) :
    compactJ N hN H (original N hN H z)=(GammaHQuotient318.jMap N H z:OnePoint ℂ) := by
  obtain ⟨tau,rfl⟩:=(GammaHQuotient318.projection_openQuotient N H).surjective z
  change compactJ N hN H (originalMap N hN H
      (GammaHDiamondQuotient318.quotient N H (GammaOneAtlas318.quotientMap N tau)))=_
  rw [compactJ_original,GammaHQuotient318.jMap_projection,QuotientJ318.jMap_projection]

theorem compactJ_eq_infty_iff (z:CompactCurve N hN H) :
    compactJ N hN H z=OnePoint.infty ↔ z∈Set.range (cuspMap N hN H) := by
  constructor
  · induction z using Quotient.inductionOn with
    | h z =>
      intro hz
      change AllCuspInfinity318.jInfinity N hN z=OnePoint.infty at hz
      obtain ⟨c,rfl⟩:=(GammaHFilledAction318.jInfinity_eq_infty_iff N hN z).mp hz
      exact ⟨⟦c⟧,rfl⟩
  · rintro ⟨c,rfl⟩
    exact compactJ_cusp N hN H c

/-- Actual compact topological point-level Gamma_H source, with dense open
actual Gamma_H quotient, its actual finite cusp-orbit complement, and genuine
continuous j. A complex atlas on this quotient and algebraic comparison are
not asserted by this topological theorem. -/
theorem actual_compactification :
    CompactSpace (CompactCurve N hN H) ∧ T2Space (CompactCurve N hN H) ∧
    SecondCountableTopology (CompactCurve N hN H) ∧ ConnectedSpace (CompactCurve N hN H) ∧
    IsOpenEmbedding (original N hN H) ∧ DenseRange (original N hN H) ∧
    Injective (cuspMap N hN H) ∧ Set.range (original N hN H)=(Set.range (cuspMap N hN H))ᶜ ∧
    Continuous (compactJ N hN H) ∧
    (∀z:GammaHQuotient318.Curve N H,compactJ N hN H (original N hN H z)=
      (GammaHQuotient318.jMap N H z:OnePoint ℂ)) := by
  obtain ⟨hc,ht,hs,hconn⟩:=compact_topology N hN H
  exact ⟨hc,ht,hs,hconn,original_openEmbedding N hN H,original_dense N hN H,
    cuspMap_injective N hN H,range_original N hN H,compactJ_continuous N hN H,original_j N hN H⟩

end GammaHActualCompactification318
