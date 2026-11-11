module
public import ReflectedDiskJoukowski318
public import Mathlib.Topology.Homeomorph.Lemmas
public section
noncomputable section
namespace ReflectedDiskJoukowskiTopology318
open Set Metric Filter Topology
open scoped OnePoint
open ReflectedDiskJoukowski318 SphereInversion318

theorem reciprocal_formula (z : ℂ) (hz : z^2-1≠0) :
    inversion ((z/(z^2-1):ℂ):OnePoint ℂ)=joukowski z := by
  by_cases h0 : z=0
  · subst z; simp [joukowski,inversion_zero]
  · rw [inversion_coe (div_ne_zero h0 hz)]
    simp only [joukowski,if_neg h0]
    apply congrArg (fun x : ℂ => (x:OnePoint ℂ))
    field_simp [h0,hz]
    <;> ring

theorem joukowski_continuous : Continuous joukowski := by
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : z=0
  · subst z
    have hp : ContinuousAt (fun z : ℂ => z^2-1) 0 :=
      (continuousAt_id.pow 2).sub continuousAt_const
    have hf : ContinuousAt (fun z : ℂ => z/(z^2-1)) 0 :=
      continuousAt_id.div hp (by norm_num)
    have hc := inversion_continuous.continuousAt.comp
      (OnePoint.continuous_coe.continuousAt.comp hf)
    apply hc.congr_of_eventuallyEq
    have hn : ∀ᶠ z : ℂ in 𝓝 0, z^2-1≠0 :=
      hp.eventually (eventually_ne_nhds (by norm_num : (0:ℂ)^2-1≠0))
    filter_upwards [hn] with z hz
    exact (reciprocal_formula z hz).symm
  · have hc : ContinuousAt (fun z : ℂ => ((z-z⁻¹:ℂ):OnePoint ℂ)) z :=
      OnePoint.continuous_coe.continuousAt.comp
        (continuousAt_id.sub (continuousAt_id.inv₀ hz))
    apply hc.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hz] with w hw
    simp only [joukowski,if_neg hw]

theorem diskMap_continuous : Continuous diskMap :=
  joukowski_continuous.comp continuous_subtype_val

instance diskCompact : CompactSpace Disk :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall (0:ℂ) 1)

/-- This intermediate kernel quotient is accompanied by the explicit complete
fiber classification, not used to hide an arithmetic orbit condition. -/
abbrev FoldedDisk := Quotient (Setoid.ker diskMap)

@[expose] def comparison : FoldedDisk → OnePoint ℂ :=
  Quotient.lift diskMap (fun _ _ h => h)

theorem comparison_continuous : Continuous comparison :=
  diskMap_continuous.quotient_lift (fun _ _ h => h)

theorem comparison_bijective : Function.Bijective comparison := by
  constructor
  · intro a b hab
    obtain ⟨z,rfl⟩ := Quotient.mk_surjective a
    obtain ⟨w,rfl⟩ := Quotient.mk_surjective b
    exact Quotient.sound hab
  · intro y
    obtain ⟨z,hz⟩ := diskMap_surjective y
    exact ⟨Quotient.mk _ z,hz⟩

instance foldedDiskCompact : CompactSpace FoldedDisk := by
  apply isCompact_univ_iff.mp
  have hs : Function.Surjective (Quotient.mk (Setoid.ker diskMap)) := Quotient.mk_surjective
  rw [←Set.range_eq_univ.mpr hs,←Set.image_univ]
  exact isCompact_univ.image continuous_quot_mk

/-- An explicit compact quotient homeomorphism onto the INDEPENDENT standard
complex one-point sphere. The complete disk fiber relation is algebraic. -/
@[expose] def foldedDiskSphere : FoldedDisk ≃ₜ OnePoint ℂ :=
  (Equiv.ofBijective comparison comparison_bijective).toHomeomorphOfContinuousClosed
    comparison_continuous comparison_continuous.isClosedMap
end ReflectedDiskJoukowskiTopology318
