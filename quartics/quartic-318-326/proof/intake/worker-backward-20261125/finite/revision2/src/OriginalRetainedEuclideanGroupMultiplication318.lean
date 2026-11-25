module

public import OriginalRetainedMultiplicationInTrueCharts318
public import OriginalRetainedEuclideanAtlas318
public import Mathlib.Topology.ContinuousOn

@[expose] public section
noncomputable section

namespace OriginalRetainedEuclideanGroupMultiplication318

open AlgebraicGeometry CategoryTheory
open OriginalRetainedProjectiveAffinePiece318 OriginalRetainedClosedProjectiveEvaluation318
open OriginalRetainedProjectiveAffinePoints318 OriginalRetainedComplexZeroByPasting318
open OriginalRetainedAffineChartPointEquiv318 OriginalActualChartPairEvaluation318
open OriginalActualRegularMapAtComplexChart318 OriginalRetainedMultiplicationInTrueCharts318
open OriginalRetainedEuclideanAtlas318
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

variable {κ : Type} [Fintype κ] [DecidableEq κ]
variable {A Y E : Scheme} (a : A ⟶ Y) [GrpObj (Over.mk a)] (P33 : E ⟶ Y) (σ : T ⟶ E)
local notation "F" => fiber a (σ≫P33)
local notation "X" => retainedCarrier a P33 σ
local notation "P" => (Over.mk (𝟙 T) ⟶ F)
variable (embedding : X ⟶ Ambient κ) (C : ∀ i, Chart a P33 σ embedding i)
local notation "rows" => (fun i => Rows (C i).I)
local notation "addrₐ" => (fun i => OriginalRetainedAffineChartPointEquiv318.evaluate a P33 σ embedding (C i))
local instance chosenTopology : TopologicalSpace P := euclidean a P33 σ embedding C

def originalChartProduct (i j : κ) (z : rows i × rows j) : P := addrₐ i z.1 * addrₐ j z.2

theorem chart_product_continuousAt (i j : κ) (z : rows i × rows j) :
    ContinuousAt (originalChartProduct a P33 σ embedding C i j) z := by
  let p := originalChartProduct a P33 σ embedding C i j
  obtain ⟨⟨k,row⟩,pin⟩ := all_points_addressed a P33 σ embedding C (p z)
  let V := C k
  let B := Poly κ k ⧸ V.I
  have center : (p z).left fieldClosedPoint ∈ Set.range V.j := by
    change addrₐ k row=p z at pin
    rw [←pin]
    exact (addr_in_chart a P33 σ embedding C k row) (Set.mem_range_self fieldClosedPoint)
  obtain ⟨s,l,hz,hl⟩ :=
    original_mul_localization a P33 σ embedding (C i) (C j) z.1 z.2 V center
  let val (rs : rows i × rows j) := pairRead (C i).I (C j).I rs.1 rs.2
  let U : Set (rows i × rows j) := {r | val r s≠0}
  have openU : IsOpen U := isOpen_ne_fun
    (tensor_values_continuous (C i).I (C j).I s) continuous_const
  have zU : z∈U := hz
  let lift (u : U) : T ⟶ Spec (CommRingCat.of B) :=
    localPoint s (val u.val).toRingHom u.property ≫ l
  have whole (u : U) : lift u≫V.j=(p u.val).left := by
    exact (same_whole_map V.j s l _ hl _ u.property).trans
      (original_multiply_read a P33 σ embedding (C i) (C j) u.val.1 u.val.2)
  let into (u : U) : PointsInPiece V.I a P33 σ V.j :=
    ⟨p u.val, by
      rintro _ ⟨v,rfl⟩
      exact ⟨lift u v,congrArg (fun f : T ⟶ X => f v) (whole u)⟩⟩
  let target (u : U) : rows k := (chartEquiv a P33 σ embedding V).symm (into u)
  have exactPoint (u : U) : addrₐ k (target u)=p u.val :=
    congrArg Subtype.val ((chartEquiv a P33 σ embedding V).apply_symm_apply (into u))
  have read_underlying (u : U) :
      (read a P33 σ embedding V (into u)).toRingHom=(Spec.preimage (lift u)).hom := by
    letI : IsOpenImmersion V.j := V.openChart
    have e : Spec.map (CommRingCat.ofHom
        (read a P33 σ embedding V (into u)).toRingHom)≫V.j=lift u≫V.j :=
      (read_returns a P33 σ embedding V (into u)).trans (whole u).symm
    have fix := (cancel_mono V.j).mp e
    exact congrArg (fun c : CommRingCat.of B ⟶ CommRingCat.of ℂ => c.hom)
      (Spec.map_injective (fix.trans (Spec.map_preimage _).symm))
  have coord (u : U) (t : {t : κ // t≠k}) :
      (target u).val t=(Spec.preimage (lift u)).hom (Ideal.Quotient.mk V.I (MvPolynomial.X t)) := by
    change (read a P33 σ embedding V (into u)) (Ideal.Quotient.mk V.I (MvPolynomial.X t))=_
    exact RingHom.congr_fun (read_underlying u) _
  have ct : Continuous target := by
    apply continuous_induced_rng.2
    apply continuous_pi
    intro t
    obtain ⟨n,r,form⟩ := actual_coordinate_fraction s l
      (Ideal.Quotient.mk V.I (MvPolynomial.X t))
    have equal : (fun u : U => (target u).val t)=fun u : U => val u.val r/(val u.val s)^n := by
      funext u
      exact (coord u t).trans (form (val u.val).toRingHom u.property)
    change Continuous (fun u : U => (target u).val t)
    rw [equal]
    have ht (x) : Continuous (fun u : U => val u.val x) :=
      (tensor_values_continuous (C i).I (C j).I x).comp continuous_subtype_val
    exact (ht r).div₀ ((ht s).pow n) (fun u => pow_ne_zero _ u.property)
  have cont : Continuous (fun u : U => p u.val) := by
    have eq : (fun u : U => p u.val)=fun u : U => addrₐ k (target u) :=
      funext (fun u => (exactPoint u).symm)
    rw [eq]
    exact (addr_continuous a P33 σ embedding C k).comp ct
  have on : ContinuousOn p U := continuousOn_iff_continuous_domRestrict.2 cont
  exact (on z zU).continuousAt (openU.mem_nhds zU)

/-- On the actual compact Euclidean atlas, the actual installed
multiplication is continuous. In particular fixed translations
have the true analytic neighbourhood carrier, not a new group. -/
theorem original_mul_continuous : Continuous (fun z : P×P => z.1*z.2) := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨⟨i,r⟩,hi⟩ := all_points_addressed a P33 σ embedding C x.1
  obtain ⟨⟨j,s⟩,hj⟩ := all_points_addressed a P33 σ embedding C x.2
  change addrₐ i r=x.1 at hi
  change addrₐ j s=x.2 at hj
  have transport := ((chart_open_embedding a P33 σ embedding C i).prodMap
    (chart_open_embedding a P33 σ embedding C j)).continuousAt_iff.mp
      (chart_product_continuousAt a P33 σ embedding C i j (r,s))
  change ContinuousAt (fun z : P×P => z.1*z.2) (addrₐ i r,addrₐ j s) at transport
  simpa only [hi,hj,Prod.eta] using transport

end OriginalRetainedEuclideanGroupMultiplication318
