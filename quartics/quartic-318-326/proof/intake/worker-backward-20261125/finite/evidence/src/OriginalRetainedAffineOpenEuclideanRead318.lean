module

public import OriginalRetainedAffineMapContinuity318
public import OriginalCyclicDivisorRetainedSchemeRead318

@[expose] public section
noncomputable section

namespace OriginalRetainedAffineOpenEuclideanRead318

open AlgebraicGeometry CategoryTheory
open OriginalRetainedProjectiveAffinePiece318 OriginalRetainedClosedProjectiveEvaluation318
open OriginalRetainedProjectiveAffinePoints318 OriginalRetainedComplexZeroByPasting318
open OriginalRetainedAffineChartPointEquiv318 OriginalRetainedEuclideanAtlas318
open OriginalRetainedAffineMapContinuity318 OriginalActualRegularMapAtComplexChart318
open scoped Topology

variable {κ : Type} [Fintype κ] [DecidableEq κ]
variable {A Y E : Scheme} (a : A ⟶ Y) (P33 : E ⟶ Y) (σ : T ⟶ E)
local notation "X" => retainedCarrier a P33 σ
local notation "F" => fiber a (σ≫P33)
local notation "P" => (Over.mk (𝟙 T) ⟶ F)
variable (embedding : X ⟶ Ambient κ) (C : ∀ i, Chart a P33 σ embedding i)
local instance chosenTopology : TopologicalSpace P := euclidean a P33 σ embedding C

variable {R : Type} [CommRing R] [Algebra ℂ R]
variable (J : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion J]
variable (jBase : J≫F.hom=Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))
local notation "row" => (fun i => Rows (C i).I)
local notation "addrₐ" => (fun i => OriginalRetainedAffineChartPointEquiv318.evaluate a P33 σ embedding (C i))

def oldOpen : Set P := {x | Set.range x.left⊆Set.range J}

theorem in_open_iff (x : P) :
    x∈oldOpen a P33 σ J ↔ x.left fieldClosedPoint∈Set.range J := by
  constructor
  · intro h
    exact h (Set.mem_range_self _)
  · intro h
    rintro _ ⟨t,rfl⟩
    have e : t=fieldClosedPoint := Subsingleton.elim _ _
    rw [e]
    exact h

/-- The actual old selected affine is open in the constructed
Euclidean topology. This is not an assumption about its analytic
image, and requires no change to the embedded arithmetic fibre. -/
theorem oldOpen_isOpen :
    IsOpen (oldOpen a P33 σ J) := by
  apply (open_iff a P33 σ embedding C _).2
  intro i
  apply isOpen_iff_mem_nhds.2
  intro x hx
  let V := C i
  let v (z : Rows V.I) := (evalRow V.I z).toRingHom
  have h (z : Rows V.I) : (addrₐ i z).left=point (v z)≫V.j :=
    evaluate_left a P33 σ embedding V z
  have cx : (point (v x)≫V.j) fieldClosedPoint∈Set.range J := by
    rw [←h]
    exact (in_open_iff a P33 σ J _).1 hx
  obtain ⟨s,l,hs,fac⟩ := actual_local_ring J V.j (v x) cx
  let S : Set (Rows V.I) := {z | v z s≠0}
  have Sopen : IsOpen S := isOpen_ne_fun (polynomial_of_readRow V.I s) continuous_const
  refine Filter.mem_of_superset (Sopen.mem_nhds hs) ?_
  intro z hz
  apply (in_open_iff a P33 σ J _).2
  rw [h,←same_whole_map J s l V.j fac (v z) hz]
  exact ⟨(localPoint s (v z) hz≫l) fieldClosedPoint,rfl⟩

def readActual (x : oldOpen a P33 σ J) : R →ₐ[ℂ] ℂ :=
  OriginalCyclicDivisorRetainedSchemeRead318.read J x.val.left x.property F.hom x.val.w jBase

theorem readActual_returns (x : oldOpen a P33 σ J) :
    point (readActual a P33 σ J jBase x).toRingHom≫J=x.val.left :=
  OriginalCyclicDivisorRetainedSchemeRead318.read_returns J x.val.left x.property F.hom x.val.w jBase

theorem readActual_on_lift (x : oldOpen a P33 σ J)
    (u : T ⟶ Spec (CommRingCat.of R)) (hu : u≫J=x.val.left) :
    (readActual a P33 σ J jBase x).toRingHom=(Spec.preimage u).hom := by
  have h := (readActual_returns a P33 σ J jBase x).trans hu.symm
  exact congrArg (fun k : CommRingCat.of R ⟶ CommRingCat.of ℂ => k.hom)
    (Spec.map_injective (((cancel_mono J).mp h).trans (Spec.map_preimage u).symm))

section Compare
variable (r : R)

theorem readActual_continuous : Continuous (fun x : oldOpen a P33 σ J =>
    readActual a P33 σ J jBase x r) := by
  let U := oldOpen a P33 σ J
  let g (x : U) := readActual a P33 σ J jBase x r
  let subAddr (i : κ) (x : addrₐ i ⁻¹' U) : U := ⟨addrₐ i x.val,x.property⟩
  have onCharts (i : κ) : Continuous (g ∘ subAddr i) := by
    apply continuous_iff_continuousAt.2
    intro x
    let V := C i
    let v (z : addrₐ i ⁻¹' U) := (evalRow V.I z.val).toRingHom
    have h (z : addrₐ i ⁻¹' U) : (subAddr i z).val.left=point (v z)≫V.j :=
      evaluate_left a P33 σ embedding V z.val
    have cx : (point (v x)≫V.j) fieldClosedPoint∈Set.range J := by
      rw [←h]
      exact (in_open_iff a P33 σ J _).1 (subAddr i x).property
    obtain ⟨S,So,Sx,lift,whole,read_cts⟩ := exact_local_continuous_read V.j v
      (fun b => (polynomial_of_readRow V.I b).comp continuous_subtype_val) J x cx
    have equals : (fun z : S => (g ∘ subAddr i) z.val)=
        fun z : S => (Spec.preimage (lift z)).hom r := by
      funext z
      exact RingHom.congr_fun (readActual_on_lift a P33 σ J jBase (subAddr i z.val)
        (lift z) ((whole z).trans (h z.val).symm)) r
    have on : ContinuousOn (g ∘ subAddr i) S := by
      apply continuousOn_iff_continuous_domRestrict.2
      rw [show (fun z : S => (g ∘ subAddr i) z.val)=_ from equals]
      exact read_cts r
    exact (on x Sx).continuousAt (So.mem_nhds Sx)
  apply continuous_def.2
  intro W hW
  let V : Set P := Subtype.val '' (g ⁻¹' W)
  have Vopen : IsOpen V := by
    apply (open_iff a P33 σ embedding C _).2
    intro i
    let D := addrₐ i ⁻¹' U
    have Dopen : IsOpen D := (addr_continuous a P33 σ embedding C i).isOpen_preimage _
      (oldOpen_isOpen a P33 σ embedding C J)
    have same : addrₐ i ⁻¹' V =
        (Subtype.val : D → row i) '' ((g ∘ subAddr i) ⁻¹' W) := by
      ext x
      constructor
      · rintro ⟨z,hz,e⟩
        let xr : D := ⟨x,e ▸ z.property⟩
        have h : subAddr i xr=z := Subtype.ext e.symm
        exact ⟨xr,(show g (subAddr i xr)∈W by rw [h]; exact hz),rfl⟩
      · rintro ⟨z,hz,rfl⟩
        exact ⟨subAddr i z,hz,rfl⟩
    rw [same]
    exact Dopen.isOpenMap_subtype_val _ ((onCharts i).isOpen_preimage _ hW)
  have e : (Subtype.val : U → P) ⁻¹' V=g ⁻¹' W :=
    Set.preimage_image_eq _ Subtype.val_injective
  rw [←e]
  exact continuous_subtype_val.isOpen_preimage _ Vopen

end Compare

end OriginalRetainedAffineOpenEuclideanRead318
