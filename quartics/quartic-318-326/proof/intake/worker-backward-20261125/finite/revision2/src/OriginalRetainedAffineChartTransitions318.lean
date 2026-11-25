module

public import OriginalRetainedAffineChartPointEquiv318
public import OriginalRetainedProjectiveChartDomain318
public import Mathlib.Topology.Constructions

@[expose] public section
noncomputable section

namespace OriginalRetainedAffineChartTransitions318

open AlgebraicGeometry CategoryTheory Limits MvPolynomial
open OriginalRetainedProjectiveAffinePiece318 OriginalRetainedClosedProjectiveEvaluation318
open OriginalRetainedProjectiveAffinePoints318 OriginalRetainedComplexZeroByPasting318
open OriginalRetainedProjectiveRatio318 OriginalRetainedAffineChartPointEquiv318
open OriginalRetainedProjectiveChartDomain318

variable {κ : Type} [Fintype κ] [DecidableEq κ]
variable {A Y E : Scheme} (a : A ⟶ Y) (P33 : E ⟶ Y) (σ : T ⟶ E)
local notation "X" => retainedCarrier a P33 σ
local notation "F" => fiber a (σ ≫ P33)
local notation "P" => (Over.mk (𝟙 T) ⟶ F)
variable (embedding : X ⟶ Ambient κ)
variable {i k : κ} (C : Chart a P33 σ embedding i) (D : Chart a P33 σ embedding k)
local notation "RY" => Rows C.I
local notation "RZ" => Rows D.I
local notation "atC" => OriginalRetainedAffineChartPointEquiv318.evaluate a P33 σ embedding C
local notation "atD" => OriginalRetainedAffineChartPointEquiv318.evaluate a P33 σ embedding D

/-- Pull the actual affine-open factorization across the literal
Cartesian square. No quotient equation for the new chart is given. -/
theorem in_of_image (p : P) (v : κ → ℂ)
    (pin : p.left≫embedding=actualPointFromVector v k) :
    Set.range p.left ⊆ Set.range D.j := by
  let U : Scheme := piece κ a P33 σ embedding k
  let j : U ⟶ X := pieceToOriginal κ a P33 σ embedding k
  let e : T ⟶ Spec (CommRingCat.of (Poly κ k)) :=
    Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (ratio v k)).toRingHom)
  have equality : p.left≫embedding=e≫affineArrow κ k := pin
  let w : T ⟶ U := pullback.lift p.left e equality
  have old : w≫j=p.left := pullback.lift_fst p.left e equality
  rw [D.rangeChart]
  rintro _ ⟨t,rfl⟩
  exact ⟨w t, congrArg (fun b : T ⟶ X => b t) old⟩

/-- Both directions matter: the domain in the source solution row
is literally the nonzero projective coordinate of the other chart. -/
theorem chart_domain (r : RY) :
    Set.range (atC r).left ⊆ Set.range D.j ↔ promote r.val k≠0 := by
  let p := atC r
  let v := promote r.val
  have h : p.left≫embedding=actualPointFromVector v i :=
    evaluate_ambient a P33 σ embedding C r
  have hi : v i≠0 := promote_nonzero r.val
  constructor
  · intro hD
    obtain ⟨x,hx⟩ := hD (Set.mem_range_self complexPointZero)
    have val : (p.left≫embedding) complexPointZero ∈ Set.range (affineArrow κ k) := by
      refine ⟨quotientArrow k D.I x,?_⟩
      have eq := congrArg
        (fun z : quotientSpec k D.I ⟶ Ambient κ => z x) D.toAmbient
      change embedding (D.j x) = affineArrow κ k (quotientArrow k D.I x) at eq
      change affineArrow κ k (quotientArrow k D.I x) = embedding (p.left complexPointZero)
      rw [← hx]
      exact eq.symm
    rw [h] at val
    exact (chart_range_iff v i hi k).1 val
  · intro hk
    exact in_of_image a P33 σ embedding D p v (h.trans (actual_chart_ratio v i hi k hk))

abbrev Overlap := {r : RY // promote r.val k≠0}

/-- The target quotient row is read from the same whole point by
the genuine target chart equivalence, not supplied independently. -/
def transition (r : Overlap (k:=k) a P33 σ embedding C) : RZ :=
  (chartEquiv a P33 σ embedding D).symm
    ⟨atC r.val, (chart_domain a P33 σ embedding C D r.val).2 r.property⟩

theorem same_point (r : Overlap (k:=k) a P33 σ embedding C) :
    atD (transition a P33 σ embedding C D r)=atC r.val :=
  congrArg Subtype.val ((chartEquiv a P33 σ embedding D).apply_symm_apply
    ⟨atC r.val,(chart_domain a P33 σ embedding C D r.val).2 r.property⟩)

/-- The transition therefore has exactly the expected rational
function on every original target coordinate, by mono affine
immersion and full Spec preimage, not numerical agreement alone. -/
theorem transition_coordinates (r : Overlap (k:=k) a P33 σ embedding C) :
    (transition a P33 σ embedding C D r).val=ratio (promote r.val.val) k := by
  let q : RZ := transition a P33 σ embedding C D r
  let v := promote r.val.val
  have hC : (atC r.val).left≫embedding=actualPointFromVector v k :=
    (evaluate_ambient a P33 σ embedding C r.val).trans
      (actual_chart_ratio v i (promote_nonzero r.val.val) k r.property)
  have eq : actualPointFromVector (promote q.val) k=actualPointFromVector v k := by
    rw [←evaluate_ambient a P33 σ embedding D q]
    change (atD (transition a P33 σ embedding C D r)).left≫embedding=_
    rw [same_point]
    exact hC
  unfold actualPointFromVector at eq
  rw [ratio_promote] at eq
  letI : IsOpenImmersion (affineArrow κ k) := affineArrow_open κ k
  have cmp := Spec.map_injective ((cancel_mono (affineArrow κ k)).mp eq)
  funext j
  have ej := congrArg
    (fun α : CommRingCat.of (Poly κ k) ⟶ CommRingCat.of ℂ => α.hom (MvPolynomial.X j)) cmp
  change MvPolynomial.aeval q.val (MvPolynomial.X j)=MvPolynomial.aeval (ratio v k) (MvPolynomial.X j) at ej
  simpa only [MvPolynomial.aeval_X] using ej

theorem overlap_open : IsOpen {r : RY | promote r.val k≠0} := by
  by_cases h : k=i
  · subst k
    simpa [promote] using (isOpen_univ : IsOpen (Set.univ : Set RY))
  · change IsOpen {r : RY | r.val ⟨k,h⟩≠0}
    exact isOpen_ne_fun ((continuous_apply ⟨k,h⟩).comp continuous_subtype_val) continuous_const

theorem transition_continuous : Continuous (transition a P33 σ embedding C D) := by
  let V := Overlap (k:=k) a P33 σ embedding C
  have coordinate (j : κ) : Continuous (fun r : V => promote r.val.val j) := by
    by_cases h : j=i
    · subst j
      simpa [promote] using (continuous_const : Continuous (fun _ : V => (1:ℂ)))
    · change Continuous (fun r : V => r.val.val ⟨j,h⟩)
      exact (continuous_apply ⟨j,h⟩).comp (continuous_subtype_val.comp continuous_subtype_val)
  apply continuous_induced_rng.2
  have hfun : Continuous (fun r : V => ratio (promote r.val.val) k) := by
    apply continuous_pi
    intro j
    change Continuous (fun r : V => promote r.val.val j.val * (promote r.val.val k)⁻¹)
    exact continuous_mul.comp₂ (coordinate j.val) ((coordinate k).inv₀ fun r => r.property)
  have eq : (fun r : V => (transition a P33 σ embedding C D r).val) =
      fun r : V => ratio (promote r.val.val) k :=
    funext (transition_coordinates a P33 σ embedding C D)
  change Continuous (fun r : V => (transition a P33 σ embedding C D r).val)
  rwa [eq]

end OriginalRetainedAffineChartTransitions318
