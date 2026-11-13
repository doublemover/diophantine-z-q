module
public import RiemannMappingInterior318
public import OpenImageHomeomorphChart318
public import ComplexHolomorphicChartInverse318
public import Mathlib.Analysis.Complex.OpenMapping
public section
noncomputable section
namespace RiemannMappingBiholomorph318
open Set Metric Topology Filter
set_option maxHeartbeats 2400000

/-- A disk-valued holomorphic bijection is open on its actual source.
Surjectivity onto two distinct disk points rules out the constant case. -/
theorem open_image {U : Set ℂ} (hU : IsOpen U) (hconn : IsPreconnected U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hb : BijOn f U (ball 0 1)) :
    ∀ s⊆U, IsOpen s → IsOpen (f '' s) := by
  rcases (hf.analyticOnNhd hU).is_constant_or_isOpen hconn with hc | ho
  · obtain ⟨c,hc⟩ := hc
    obtain ⟨x,hx,hfx⟩ := hb.surjOn (by simp : (0:ℂ)∈ball 0 1)
    obtain ⟨y,hy,hfy⟩ := hb.surjOn (by norm_num [Metric.mem_ball] : (1/2:ℂ)∈ball 0 1)
    have he : (0:ℂ)=1/2 := hfx.symm.trans ((hc x hx).trans ((hc y hy).symm.trans hfy))
    norm_num at he
  · exact ho

@[expose] def restricted {U : Set ℂ} (f : ℂ → ℂ) (hb : BijOn f U (ball 0 1)) :
    U → ball (0:ℂ) 1 := fun z => ⟨f z,hb.mapsTo z.property⟩

theorem restricted_bijective {U : Set ℂ} (f : ℂ → ℂ) (hb : BijOn f U (ball 0 1)) :
    Function.Bijective (restricted f hb) := by
  constructor
  · intro z w h
    exact Subtype.ext (hb.injOn z.property w.property (congrArg Subtype.val h))
  · intro y
    obtain ⟨x,hx,hxy⟩ := hb.surjOn y.property
    exact ⟨⟨x,hx⟩,Subtype.ext hxy⟩

theorem restricted_continuous {U : Set ℂ} (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f U) (hb : BijOn f U (ball 0 1)) :
    Continuous (restricted f hb) :=
  (continuousOn_iff_continuous_restrict.mp hf.continuousOn).subtype_mk _

theorem restricted_open {U : Set ℂ} (hU : IsOpen U) (hconn : IsPreconnected U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U) (hb : BijOn f U (ball 0 1)) :
    IsOpenMap (restricted f hb) := by
  intro s hs
  have hi : IsOpen (f '' (Subtype.val '' s)) :=
    open_image hU hconn hf hb _ (by rintro _ ⟨z,hz,rfl⟩; exact z.property)
      (hU.isOpenEmbedding_subtypeVal.isOpenMap s hs)
  have he : restricted f hb '' s=Subtype.val ⁻¹' (f '' (Subtype.val '' s)) := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨z.val,⟨z,hz,rfl⟩,rfl⟩
    · rintro ⟨x,⟨z,hz,rfl⟩,hxy⟩
      exact ⟨z,hz,Subtype.ext hxy⟩
  rw [he]
  exact hi.preimage continuous_subtype_val

/-- The actual restriction of the Riemann map, with its continuous inverse
constructed from the complex open mapping theorem. -/
@[expose] def diskHomeomorph {U : Set ℂ} (hU : IsOpen U) (hconn : IsPreconnected U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U) (hb : BijOn f U (ball 0 1)) :
    U ≃ₜ ball (0:ℂ) 1 :=
  (Equiv.ofBijective (restricted f hb) (restricted_bijective f hb)).toHomeomorphOfContinuousOpen
    (restricted_continuous f hf hb) (restricted_open hU hconn f hf hb)

@[expose] def chart {U : Set ℂ} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hne : Nonempty U) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U)
    (hb : BijOn f U (ball 0 1)) : OpenPartialHomeomorph ℂ ℂ :=
  OpenImageHomeomorphChart318.extend U (ball 0 1) hU isOpen_ball hne
    (diskHomeomorph hU hconn f hf hb)

theorem chart_source {U : Set ℂ} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hne : Nonempty U) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U) (hb : BijOn f U (ball 0 1)) :
    (chart hU hconn hne f hf hb).source=U :=
  OpenImageHomeomorphChart318.extend_source _ _ _ _ _ _

theorem chart_target {U : Set ℂ} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hne : Nonempty U) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U) (hb : BijOn f U (ball 0 1)) :
    (chart hU hconn hne f hf hb).target=ball 0 1 :=
  OpenImageHomeomorphChart318.extend_target _ _ _ _ _ _

theorem chart_eq {U : Set ℂ} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hne : Nonempty U) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U) (hb : BijOn f U (ball 0 1)) :
    EqOn (chart hU hconn hne f hf hb) f U := by
  intro z hz
  exact OpenImageHomeomorphChart318.extend_value _ _ _ _ _ _ ⟨z,hz⟩

/-- Holomorphy of both directions is proved for the SAME source/target
partial homeomorphism, not transported onto a merely topological disk. -/
theorem chart_biholomorphic {U : Set ℂ} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hne : Nonempty U) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U) (hb : BijOn f U (ball 0 1)) :
    (∀ z∈U, AnalyticAt ℂ (chart hU hconn hne f hf hb) z) ∧
    (∀ w∈ball (0:ℂ) 1, AnalyticAt ℂ (chart hU hconn hne f hf hb).symm w) := by
  let e := chart hU hconn hne f hf hb
  have hs : e.source=U := chart_source hU hconn hne f hf hb
  have ht : e.target=ball 0 1 := chart_target hU hconn hne f hf hb
  have ha (z : ℂ) (hz : z∈U) : AnalyticAt ℂ e z := by
    apply (hf.analyticOnNhd hU z hz).congr
    filter_upwards [hU.mem_nhds hz] with x hx
    exact (chart_eq hU hconn hne f hf hb hx).symm
  refine ⟨ha,?_⟩
  intro w hw
  have hwt : w∈e.target := ht.symm ▸ hw
  have hx := e.map_target hwt
  have hh := ComplexHolomorphicChartInverse318.inverse_analytic e hx
    (ha (e.symm w) (hs ▸ hx))
  rwa [e.right_inv hwt] at hh

/-- Complete interior Riemann mapping in genuine complex charts, including
an analytic inverse. There is deliberately no boundary extension here. -/
theorem exists_biholomorphic_disk {U : Set ℂ} (hU : IsOpen U)
    (hconn : IsSimplyConnected U) (hproper : U≠univ) {z₀ : ℂ} (hz₀ : z₀∈U) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, e.source=U ∧ e.target=ball 0 1 ∧ e z₀=0 ∧
      (∀ z∈U,AnalyticAt ℂ e z) ∧ (∀ w∈ball (0:ℂ) 1,AnalyticAt ℂ e.symm w) := by
  obtain ⟨f,hf,hb,hzero⟩ := Complex.exists_bijOn_unitBall_map_eq_zero318 hU hconn hproper hz₀
  let hc := hconn.isPathConnected.isConnected.isPreconnected
  let hn : Nonempty U := ⟨⟨z₀,hz₀⟩⟩
  refine ⟨chart hU hc hn f hf hb,chart_source hU hc hn f hf hb,
    chart_target hU hc hn f hf hb,?_,chart_biholomorphic hU hc hn f hf hb⟩
  exact (chart_eq hU hc hn f hf hb hz₀).trans hzero
end RiemannMappingBiholomorph318
