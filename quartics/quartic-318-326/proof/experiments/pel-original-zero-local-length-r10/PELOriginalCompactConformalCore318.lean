module
public import PELOriginalOpenDenseInterior318
public section
noncomputable section
namespace PELOriginalCompactConformalCore318
open Set Metric
open PELOriginalOpenDenseInterior318 PELOriginalMaximalSphere318
open PELOriginalMaximalQuotient318 PELMaximalActualComplexDomain318
open PELMaximalHalfOctagonOriginalPoints318 PELMaximalHalfOctagonCoordinates318
open PELMaximalHalfOctagonShape318 PELMaximalHalfOctagonBoundary318
open QuaternionicJointPeriodTopology318

/-- Complete arithmetic cut-fiber classification separates EVERY cut
boundary point from the genuine arithmetic interior. -/
theorem boundary_not_originalInterior (P:upperCut)
    (hP:(upperCutCenter P).val∉strictPolygon) : cutProjection P∉originalInterior := by
  rintro ⟨τ,hτ,hτP⟩
  have hτc:=((closedDomain_membership (τ:ℂ)).mp (openDomain_subset hτ)).2
  let Q:upperCut:=⟨coordinates τ,hτc⟩
  have hQ:cutPoint Q=τ:=cutPoint_recovers τ hτc
  have hs:(upperCutCenter Q).val∈strictPolygon:=hτ.2
  have he:cutProjection Q=cutProjection P:=by
    change maximalProjection (cutPoint Q)=cutProjection P
    rw [hQ]
    exact hτP
  rcases (cutProjection_fibers Q P).mp he with heq|⟨hb,_⟩
  · exact hP (heq ▸ hs)
  · exact hb.2 (by rw [interior_eq_strict];exact hs)

abbrev CoreDisk := closedBall (0:ℂ) (1/2:ℝ)
instance : CompactSpace CoreDisk := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)

lemma coreDisk_in_unit (w:CoreDisk) : (w:ℂ)∈ball (0:ℂ) 1 := by
  have hw:=w.property
  rw [mem_closedBall,dist_zero_right] at hw
  rw [mem_ball,dist_zero_right]
  linarith

/-- The actual conformal inverse of the CLOSED half-radius disk. Every
point lies strictly inside the original complex half-cut. -/
@[expose] def corePoint (e:OpenPartialHomeomorph ℂ ℂ)
    (hs:e.source=openDomain) (ht:e.target=ball 0 1) (w:CoreDisk) : HalfPlane :=
  ⟨e.symm w,(show e.symm (w:ℂ)∈openDomain from
    hs ▸ e.map_target (ht.symm ▸ coreDisk_in_unit w)).1⟩

lemma corePoint_interior (e:OpenPartialHomeomorph ℂ ℂ)
    (hs:e.source=openDomain) (ht:e.target=ball 0 1) (w:CoreDisk) :
    (corePoint e hs ht w:ℂ)∈openDomain :=
  hs ▸ e.map_target (ht.symm ▸ coreDisk_in_unit w)

lemma corePoint_continuous (e:OpenPartialHomeomorph ℂ ℂ)
    (hs:e.source=openDomain) (ht:e.target=ball 0 1) : Continuous (corePoint e hs ht) := by
  have hc:Continuous (fun w:CoreDisk=>e.symm (w:ℂ)) := by
    apply continuous_iff_continuousAt.mpr
    intro w
    have hw:(w:ℂ)∈e.symm.source:=ht.symm ▸ coreDisk_in_unit w
    exact ((e.symm.continuousOn (w:ℂ) hw).continuousAt
      (e.symm.open_source.mem_nhds hw)).comp w continuous_subtype_val.continuousAt
  exact hc.subtype_mk _

@[expose] def coreImage (e:OpenPartialHomeomorph ℂ ℂ)
    (hs:e.source=openDomain) (ht:e.target=ball 0 1) : Set MaximalBase :=
  range (maximalProjection ∘ corePoint e hs ht)

lemma coreImage_compact (e:OpenPartialHomeomorph ℂ ℂ)
    (hs:e.source=openDomain) (ht:e.target=ball 0 1) : IsCompact (coreImage e hs ht) :=
  isCompact_range (maximalProjection_continuous.comp (corePoint_continuous e hs ht))

lemma coreImage_interior (e:OpenPartialHomeomorph ℂ ℂ)
    (hs:e.source=openDomain) (ht:e.target=ball 0 1) : coreImage e hs ht⊆originalInterior := by
  rintro q ⟨w,rfl⟩
  exact ⟨corePoint e hs ht w,corePoint_interior e hs ht w,rfl⟩

/-- A single genuine arithmetic open neighborhood of ALL seam and corner
orbits. It is defined by removing a constructed compact INTERIOR image. -/
@[expose] def seamNeighborhood (e:OpenPartialHomeomorph ℂ ℂ)
    (hs:e.source=openDomain) (ht:e.target=ball 0 1) : Set MaximalBase :=
  (coreImage e hs ht)ᶜ

lemma seamNeighborhood_open (e:OpenPartialHomeomorph ℂ ℂ)
    (hs:e.source=openDomain) (ht:e.target=ball 0 1) : IsOpen (seamNeighborhood e hs ht) :=
  (coreImage_compact e hs ht).isClosed.isOpen_compl

lemma boundary_in_seamNeighborhood (e:OpenPartialHomeomorph ℂ ℂ)
    (hs:e.source=openDomain) (ht:e.target=ball 0 1) (P:upperCut)
    (hP:(upperCutCenter P).val∉strictPolygon) :
    cutProjection P∈seamNeighborhood e hs ht := by
  intro hc
  exact boundary_not_originalInterior P hP (coreImage_interior e hs ht hc)

/-- EVERY interior representative of a point in the actual seam
neighborhood has conformal modulus strictly larger than one half. -/
theorem interior_modulus_lower (e:OpenPartialHomeomorph ℂ ℂ)
    (hs:e.source=openDomain) (ht:e.target=ball 0 1)
    (τ:HalfPlane) (hτ:(τ:ℂ)∈openDomain)
    (hq:maximalProjection τ∈seamNeighborhood e hs ht) : (1/2:ℝ)<‖e τ‖ := by
  by_contra hn
  have hw:e (τ:ℂ)∈closedBall (0:ℂ) (1/2:ℝ) := by
    rw [mem_closedBall,dist_zero_right]
    exact le_of_not_gt hn
  apply hq
  refine ⟨⟨e τ,hw⟩,?_⟩
  apply congrArg maximalProjection
  apply Subtype.ext
  exact e.left_inv (hs.symm ▸ hτ)
end PELOriginalCompactConformalCore318
