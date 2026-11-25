module

public import OriginalActualRegularMapAtComplexChart318
public import OriginalRetainedEuclideanAtlas318
public import Mathlib.Topology.ContinuousOn

@[expose] public section
noncomputable section

namespace OriginalRetainedAffineMapContinuity318

open AlgebraicGeometry CategoryTheory
open OriginalRetainedProjectiveAffinePiece318 OriginalRetainedClosedProjectiveEvaluation318
open OriginalRetainedProjectiveAffinePoints318 OriginalRetainedComplexZeroByPasting318
open OriginalRetainedAffineChartPointEquiv318 OriginalRetainedEuclideanAtlas318
open OriginalActualRegularMapAtComplexChart318
open scoped Topology

section LocalRegularRead
variable {W R B : Type} [TopologicalSpace W] [CommRing R] [CommRing B]
variable {X : Scheme}
variable (f : Spec (CommRingCat.of R) ⟶ X) (v : W → R →+* ℂ)
variable (v_cont : ∀ b : R, Continuous (fun w : W => v w b))
variable (j : Spec (CommRingCat.of B) ⟶ X) [IsOpenImmersion j]

/-- Keep one actual Scheme localization at the center. Each regular
target function is continuous on this same open, by its own exact
fraction computed in the localization. -/
include v_cont in
theorem exact_local_continuous_read (w : W)
    (hw : (point (v w)≫f) fieldClosedPoint∈Set.range j) :
    ∃ (U : Set W) (_openU : IsOpen U) (_wU : w∈U)
      (lift : U → (T ⟶ Spec (CommRingCat.of B))),
      (∀ x : U, lift x≫j=point (v x.val)≫f) ∧
      ∀ b : B, Continuous (fun x : U => (Spec.preimage (lift x)).hom b) := by
  obtain ⟨s,l,hs,fac⟩ := actual_local_ring j f (v w) hw
  let U : Set W := {x | v x s ≠ 0}
  let lift (x : U) : T ⟶ Spec (CommRingCat.of B) :=
    localPoint s (v x.val) x.property≫l
  refine ⟨U,isOpen_ne_fun (v_cont s) continuous_const,hs,lift,?_,?_⟩
  · intro x
    exact same_whole_map j s l f fac (v x.val) x.property
  · intro b
    obtain ⟨n,r,formula⟩ := actual_coordinate_fraction s l b
    have eq : (fun x : U => (Spec.preimage (lift x)).hom b) =
        fun x : U => v x.val r/(v x.val s)^n := by
      funext x
      exact formula (v x.val) x.property
    rw [eq]
    exact ((v_cont r).comp continuous_subtype_val).div₀
      (((v_cont s).comp continuous_subtype_val).pow n)
      (fun x => pow_ne_zero n x.property)

end LocalRegularRead

section RetainedPointContinuity
variable {κ : Type} [Fintype κ] [DecidableEq κ]
variable {A Y E : Scheme} (a : A ⟶ Y) (P33 : E ⟶ Y) (σ : T ⟶ E)
local notation "X" => retainedCarrier a P33 σ
local notation "F" => fiber a (σ≫P33)
local notation "P" => (Over.mk (𝟙 T) ⟶ F)
variable (embedding : X ⟶ Ambient κ) (C : ∀ i, Chart a P33 σ embedding i)
local instance chosenTopology : TopologicalSpace P := euclidean a P33 σ embedding C
variable {W R : Type} [TopologicalSpace W] [CommRing R] [Algebra ℂ R]
variable (j : Spec (CommRingCat.of R) ⟶ X)
variable (jBase : j≫F.hom=Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))
variable (v : W → R →ₐ[ℂ] ℂ)

def mapped (w : W) : P :=
  Over.homMk (point (v w).toRingHom≫j) (by
    rw [Category.assoc,jBase,point,←Spec.map_comp,←CommRingCat.ofHom_comp]
    have h : (v w).toRingHom.comp (algebraMap ℂ R)=RingHom.id ℂ :=
      RingHom.ext (fun x => (v w).commutes x)
    rw [h]
    change Spec.map (𝟙 (CommRingCat.of ℂ))=𝟙 T
    exact Spec.map_id _)

theorem mapped_left (w : W) :
    (mapped a P33 σ j jBase v w).left=point (v w).toRingHom≫j := rfl

/-- An actual affine map in the original arithmetic-selected
complex fibre is continuous for its true point values in the
Euclidean topology constructed from the actual projective embedding.
In the original local log this applies to the old centered smooth
chart and also to translated actual group maps. -/
theorem mapped_continuous (v_cont : ∀ b : R, Continuous (fun w : W => v w b)) :
    Continuous (mapped a P33 σ j jBase v) := by
  apply continuous_iff_continuousAt.2
  intro w
  let f := mapped a P33 σ j jBase v
  obtain ⟨⟨i,r⟩,hr⟩ := all_points_addressed a P33 σ embedding C (f w)
  let V := C i
  let B := Poly κ i ⧸ V.I
  letI : IsOpenImmersion V.j := V.openChart
  have center : (point (v w).toRingHom≫j) fieldClosedPoint ∈ Set.range V.j := by
    change (f w).left fieldClosedPoint∈Set.range V.j
    change OriginalRetainedAffineChartPointEquiv318.evaluate a P33 σ embedding V r=f w at hr
    rw [←hr]
    exact addr_in_chart a P33 σ embedding C i r (Set.mem_range_self _)
  obtain ⟨U,Uo,Uw,lift,whole,read_cts⟩ :=
    exact_local_continuous_read j (fun x => (v x).toRingHom) v_cont V.j w center
  let asPoint (u : U) : PointsInPiece V.I a P33 σ V.j :=
    ⟨f u.val,by
      rintro _ ⟨t,rfl⟩
      exact ⟨lift u t,congrArg (fun h : T ⟶ X => h t) (whole u)⟩⟩
  let row (u : U) : Rows V.I := (chartEquiv a P33 σ embedding V).symm (asPoint u)
  have eval_eq (u : U) :
      OriginalRetainedAffineChartPointEquiv318.evaluate a P33 σ embedding V (row u)=f u.val :=
    congrArg Subtype.val ((chartEquiv a P33 σ embedding V).apply_symm_apply (asPoint u))
  have read_exact (u : U) :
      (read a P33 σ embedding V (asPoint u)).toRingHom=(Spec.preimage (lift u)).hom := by
    have eq : point (read a P33 σ embedding V (asPoint u)).toRingHom≫V.j=lift u≫V.j :=
      (read_returns a P33 σ embedding V (asPoint u)).trans (whole u).symm
    exact congrArg (fun h : CommRingCat.of B ⟶ CommRingCat.of ℂ => h.hom)
      (Spec.map_injective (((cancel_mono V.j).mp eq).trans (Spec.map_preimage _).symm))
  have row_cts : Continuous row := by
    apply continuous_induced_rng.2
    apply continuous_pi
    intro k
    let b := Ideal.Quotient.mk V.I (MvPolynomial.X k)
    have eq : (fun u : U => (row u).val k)=fun u => (Spec.preimage (lift u)).hom b := by
      funext u
      change read a P33 σ embedding V (asPoint u) b=(Spec.preimage (lift u)).hom b
      exact RingHom.congr_fun (read_exact u) b
    rw [eq]
    exact read_cts b
  have on : ContinuousOn f U := by
    apply continuousOn_iff_continuous_domRestrict.2
    change Continuous (fun u : U => f u.val)
    rw [show (fun u : U => f u.val)=
      (fun u => OriginalRetainedAffineChartPointEquiv318.evaluate a P33 σ embedding V (row u))
      from funext (fun u => (eval_eq u).symm)]
    exact (addr_continuous a P33 σ embedding C i).comp row_cts
  exact (on w Uw).continuousAt (Uo.mem_nhds Uw)

end RetainedPointContinuity

end OriginalRetainedAffineMapContinuity318
