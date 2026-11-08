module
public import OpenJLocalComparison318
public section
noncomputable section
namespace OpenJLocalPointMaps318
open OpenJComplexEvaluation318 Filter Topology
set_option maxHeartbeats 0

/-- Actual local holomorphic coordinate comparison data. The following
existence theorem constructs all fields from the genuine modular functions. -/
structure Chart (N : ℕ) [NeZero N] (tau : UpperHalfPlane) where
  domain : Set ℂ
  isOpen_domain : IsOpen domain
  center_mem : (tau:ℂ) ∈ domain
  scale : ℂ → ℂ
  holomorphic : AnalyticOnNhd ℂ scale domain
  admissible : ∀ z ∈ domain, Admissible (UpperHalfPlane.ofComplex z)
  nonzero : ∀ z ∈ domain, scale z ≠ 0
  coeff4 : ∀ z (hz : z ∈ domain),
    (ModularWeierstrass318.curve (UpperHalfPlane.ofComplex z)).a₄ =
      scale z^4 * (fiber N (UpperHalfPlane.ofComplex z) (admissible z hz)).a₄
  coeff6 : ∀ z (hz : z ∈ domain),
    (ModularWeierstrass318.curve (UpperHalfPlane.ofComplex z)).a₆ =
      scale z^6 * (fiber N (UpperHalfPlane.ofComplex z) (admissible z hz)).a₆

/-- No local analytic trivialization is supplied as a hypothesis. -/
theorem nonempty_chart (N : ℕ) [NeZero N] (tau : UpperHalfPlane) (h : Admissible tau) :
    Nonempty (Chart N tau) := by
  obtain ⟨u,hu,_,hv⟩ := OpenJLocalComparison318.exists_local_comparison N tau h
  obtain ⟨U,hU,hUo,hUc⟩ := eventually_nhds_iff.mp (hu.eventually_analyticAt.and hv)
  have had : ∀ z ∈ U, Admissible (UpperHalfPlane.ofComplex z) := fun z hz => (hU z hz).2.choose
  refine ⟨⟨U,hUo,hUc,u,fun z hz => (hU z hz).1,had,
    fun z hz => (hU z hz).2.choose_spec.1,
    fun z hz => (hU z hz).2.choose_spec.2.1,
    fun z hz => (hU z hz).2.choose_spec.2.2⟩⟩

@[expose] def chart (N : ℕ) [NeZero N] (tau : UpperHalfPlane) (h : Admissible tau) : Chart N tau :=
  (nonempty_chart N tau h).some

/-- Every point of the constructed open comparison chart has an actual
additive point equivalence given by the same holomorphic coordinate scaling. -/
@[expose] def pointAddEquiv {N : ℕ} [NeZero N] {tau : UpperHalfPlane}
    (c : Chart N tau) (z : ℂ) (hz : z ∈ c.domain) :
    (fiber N (UpperHalfPlane.ofComplex z) (c.admissible z hz)).toAffine.Point ≃+
      (ModularWeierstrass318.curve (UpperHalfPlane.ofComplex z)).toAffine.Point :=
  ShortScaling318.pointAddEquiv _ _ (Units.mk0 (c.scale z) (c.nonzero z hz))
    (c.coeff4 z hz) (c.coeff6 z hz)

/-- On overlapping constructed charts, the two coordinate maps differ
only by genuine elliptic negation. This is the sign descent datum still to
be accounted for in a coarse modular comparison. -/
theorem overlap_eq_or_neg {N : ℕ} [NeZero N] {tau sigma : UpperHalfPlane}
    (c : Chart N tau) (d : Chart N sigma) (z : ℂ)
    (hc : z ∈ c.domain) (hd : z ∈ d.domain) :
    (∀ P, pointAddEquiv c z hc P = pointAddEquiv d z hd P) ∨
    (∀ P, pointAddEquiv c z hc P = -pointAddEquiv d z hd P) := by
  exact OpenJScalingAmbiguity318.point_maps_eq_or_neg N (UpperHalfPlane.ofComplex z)
    (c.admissible z hc) (Units.mk0 (c.scale z) (c.nonzero z hc))
    (Units.mk0 (d.scale z) (d.nonzero z hd))
    (c.coeff4 z hc) (c.coeff6 z hc) (d.coeff4 z hd) (d.coeff6 z hd)

end OpenJLocalPointMaps318
