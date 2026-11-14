module
public import ComplexSphereRegularTarget318
public import PELOriginalMaximalSphere318
public section
noncomputable section
namespace PELOriginalOpenDenseInterior318
open Set Filter
open scoped Topology OnePoint
open QuaternionicJointPeriodTopology318 PELDirichletHeight318
open PELMaximalActualComplexDomain318 PELMaximalHalfOctagonOriginalPoints318
open PELMaximalHalfOctagonCoordinates318 PELMaximalHalfOctagonShape318
open PELMaximalHalfOctagonBoundary318 PELMaximalHalfOctagonSphere318
open PELOriginalMaximalQuotient318 PELOriginalMaximalSphere318
set_option maxHeartbeats 2600000

/-- Original complex half-cut interior, inside the unchanged half-plane. -/
@[expose] def halfInterior : Set HalfPlane := {τ | (τ:ℂ)∈openDomain}
/-- Its image under the ACTUAL full-normalizer arithmetic projection. -/
@[expose] def originalInterior : Set MaximalBase := maximalProjection '' halfInterior

lemma halfInterior_open : IsOpen halfInterior :=
  openDomain_open.preimage continuous_subtype_val

lemma maximalProjection_open : IsOpenMap maximalProjection := by
  have h : IsOpenMap PELUnlevelledComplexBase318.projection := isOpenMap_quotient_mk'_mul
  exact PELOriginalMaximalQuotient318.projection_open.comp h

theorem originalInterior_open : IsOpen originalInterior :=
  maximalProjection_open halfInterior halfInterior_open

lemma cut_originalInterior (P : upperCut) (hP : (upperCutCenter P).val∈strictPolygon) :
    cutProjection P∈originalInterior := by
  refine ⟨cutPoint P,?_,rfl⟩
  change 0<(cutPoint P:ℂ).im ∧ centerHomeomorph (coordinates (cutPoint P))∈strictPolygon
  refine ⟨(cutPoint P).property,?_⟩
  rw [coordinates_halfPlane,cutPoint_coordinates]
  exact hP

/-- The old arithmetic TOPological sphere is used only to establish
source density. No holomorphic structure is transported through it and
it is NOT identified with the new conformal sphere map. -/
lemma auxiliary_regular_preimage (q : MaximalBase)
    (hq : originalMaximalSphere q∈ComplexSphereRegularTarget318.regular) :
    q∈originalInterior := by
  obtain ⟨z,rfl⟩ := centeredProjection_surjective q
  rw [originalMaximalSphere_projection] at hq
  have hs : z.val∈strictPolygon := by
    by_contra hn
    have hb : z.val∈frontier centeredPolygon := by
      rw [←closure_sdiff_interior,polygon_closed.closure_eq,interior_eq_strict]
      exact ⟨z.property,hn⟩
    have hnorm := (normalized_boundary_iff z).mpr hb
    exact ComplexSphereRegularTarget318.unit_boundary_not_regular
      (polygonDiskHomeomorph z).val hnorm hq
  apply cut_originalInterior (upperCutCenter.symm z)
  simpa only [Homeomorph.apply_symm_apply] using hs

/-- The original arithmetic interior is genuinely DENSE in the actual
MaximalBase, including all boundary identifications and corner orbits. -/
theorem originalInterior_dense : Dense originalInterior := by
  apply dense_iff_inter_open.mpr
  intro O hO hne
  have hIm : IsOpen (originalMaximalSphere '' O) := originalMaximalSphere.isOpenMap O hO
  have hImn : (originalMaximalSphere '' O).Nonempty := hne.image _
  obtain ⟨w,⟨q,hq,hqw⟩,hw⟩ :=
    ComplexSphereRegularTarget318.regular_dense.inter_open_nonempty _ hIm hImn
  exact ⟨q,hq,auxiliary_regular_preimage q (hqw.symm ▸ hw)⟩

/-- No two original strict interior points are identified by the FULL
normalizer. This uses the complete half-cut fiber classification. -/
theorem maximalProjection_injective_on_interior : InjOn maximalProjection halfInterior := by
  intro τ hτ σ hσ he
  have hτc := ((closedDomain_membership (τ:ℂ)).mp (openDomain_subset hτ)).2
  have hσc := ((closedDomain_membership (σ:ℂ)).mp (openDomain_subset hσ)).2
  let P : upperCut := ⟨coordinates τ,hτc⟩
  let Q : upperCut := ⟨coordinates σ,hσc⟩
  have hP : cutPoint P=τ := cutPoint_recovers τ hτc
  have hQ : cutPoint Q=σ := cutPoint_recovers σ hσc
  have hpq : cutProjection P=cutProjection Q := by
    change maximalProjection (cutPoint P)=maximalProjection (cutPoint Q)
    rw [hP,hQ]
    exact he
  rcases (cutProjection_fibers P Q).mp hpq with hsame | ⟨hb,_⟩
  · exact hP.symm.trans ((congrArg cutPoint hsame).trans hQ)
  · have hs : (upperCutCenter P).val∈strictPolygon := hτ.2
    have hi : (upperCutCenter P).val∈interior centeredPolygon := by
      rw [interior_eq_strict]
      exact hs
    exact False.elim (hb.2 hi)
end PELOriginalOpenDenseInterior318
