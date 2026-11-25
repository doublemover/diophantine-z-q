module

public import OriginalRetainedClosedProjectiveEvaluation318
public import OriginalRetainedProjectiveAffinePoints318

@[expose] public section
noncomputable section

namespace OriginalRetainedAffineChartPointEquiv318

open AlgebraicGeometry CategoryTheory MvPolynomial
open OriginalRetainedProjectiveAffinePiece318 OriginalRetainedClosedProjectiveEvaluation318
open OriginalRetainedProjectiveAffinePoints318 OriginalRetainedComplexZeroByPasting318
open OriginalRetainedProjectiveRatio318

variable {κ : Type} [Fintype κ] [DecidableEq κ]
variable {A Y E : Scheme} (a : A ⟶ Y) (P33 : E ⟶ Y) (σ : T ⟶ E)
local notation "X" => retainedCarrier a P33 σ
local notation "F" => fiber a (σ ≫ P33)
local notation "P" => (Over.mk (𝟙 T) ⟶ F)
variable (embedding : X ⟶ Ambient κ)
variable {i : κ} (C : Chart a P33 σ embedding i)
local notation "R" => Poly κ i
local notation "Q" => (R ⧸ C.I)
local notation "Row" => Rows C.I
local notation "InChart" => PointsInPiece C.I a P33 σ C.j

/-- Insert the unit in the actual distinguished coordinate, without
asserting the remaining dehomogenized variables are independent. -/
def promote (r : {k : κ // k≠i} → ℂ) (k : κ) : ℂ :=
  if h : k=i then 1 else r ⟨k,h⟩

theorem promote_ith (r : {k : κ // k≠i} → ℂ) : promote r i=1 := by simp [promote]

theorem promote_nonzero (r : {k : κ // k≠i} → ℂ) : promote r i≠0 := by simp [promote]

theorem ratio_promote (r : {k : κ // k≠i} → ℂ) : ratio (promote r) i=r := by
  funext j
  simp [ratio,promote,j.property]

def rowKills (r : Row) : KillsChart a P33 σ embedding C (promote r.val) := by
  intro b hb
  rw [RingHom.mem_ker]
  change MvPolynomial.aeval (ratio (promote r.val) i) b=0
  rw [ratio_promote]
  exact r.property b hb

def evaluate (r : Row) : P :=
  actual a P33 σ embedding C (promote r.val) (rowKills a P33 σ embedding C r)

theorem quotientRead_is_evalRow (r : Row) :
    quotientRead a P33 σ embedding C (promote r.val) (rowKills a P33 σ embedding C r) =
      evalRow C.I r := by
  apply Ideal.Quotient.algHom_ext
  apply AlgHom.ext
  intro b
  have h := RingHom.congr_fun
    (quotientRead_comp a P33 σ embedding C (promote r.val) (rowKills a P33 σ embedding C r)) b
  have g := DFunLike.congr_fun (evalRow_comp C.I r) b
  change quotientRead a P33 σ embedding C (promote r.val) (rowKills a P33 σ embedding C r)
    (Ideal.Quotient.mk C.I b) = MvPolynomial.aeval (ratio (promote r.val) i) b at h
  rw [ratio_promote] at h
  exact h.trans g.symm

theorem evaluate_left (r : Row) :
    (evaluate a P33 σ embedding C r).left =
      Spec.map (CommRingCat.ofHom (evalRow C.I r).toRingHom)≫C.j := by
  change Spec.map (CommRingCat.ofHom
    (quotientRead a P33 σ embedding C _ (rowKills a P33 σ embedding C r)).toRingHom)≫C.j = _
  rw [quotientRead_is_evalRow]

theorem evaluate_ambient (r : Row) :
    (evaluate a P33 σ embedding C r).left≫embedding=actualPointFromVector (promote r.val) i :=
  actual_ambient a P33 σ embedding C _ (rowKills a P33 σ embedding C r)

def liftRow (r : Row) : InChart :=
  ⟨evaluate a P33 σ embedding C r, by
    rw [evaluate_left]
    rintro _ ⟨t,rfl⟩
    exact ⟨Spec.map (CommRingCat.ofHom (evalRow C.I r).toRingHom) t,rfl⟩⟩

theorem chosen_chart_base :
    C.j ≫ retainedBase a P33 σ = Spec.map (CommRingCat.ofHom (algebraMap ℂ Q)) := C.toBase

def read (p : InChart) : Q →ₐ[ℂ] ℂ :=
  letI : IsOpenImmersion C.j := C.openChart
  originalPointRead C.I a P33 σ C.j (chosen_chart_base a P33 σ embedding C) p

theorem read_returns (p : InChart) :
    Spec.map (CommRingCat.ofHom (read a P33 σ embedding C p).toRingHom)≫C.j=p.val.left := by
  letI : IsOpenImmersion C.j := C.openChart
  exact originalPointRead_returns C.I a P33 σ C.j (chosen_chart_base a P33 σ embedding C) p

def readRowOnWholePoint (p : InChart) : Row :=
  ⟨readRow C.I (read a P33 σ embedding C p),readRow_mem C.I _⟩

theorem eval_read (p : InChart) :
    liftRow a P33 σ embedding C (readRowOnWholePoint a P33 σ embedding C p)=p := by
  apply Subtype.ext
  apply Over.OverMorphism.ext
  change (evaluate a P33 σ embedding C _).left=p.val.left
  rw [evaluate_left]
  letI : IsOpenImmersion C.j := C.openChart
  exact actual_point_from_dehomogenized_row C.I a P33 σ C.j
    (chosen_chart_base a P33 σ embedding C) p

theorem read_eval (r : Row) :
    readRowOnWholePoint a P33 σ embedding C (liftRow a P33 σ embedding C r)=r := by
  let p := liftRow a P33 σ embedding C r
  letI : IsOpenImmersion C.j := C.openChart
  have h : Spec.map (CommRingCat.ofHom (read a P33 σ embedding C p).toRingHom)≫C.j =
      Spec.map (CommRingCat.ofHom (evalRow C.I r).toRingHom)≫C.j :=
    (read_returns a P33 σ embedding C p).trans (evaluate_left a P33 σ embedding C r)
  have eq := Spec.map_injective ((cancel_mono C.j).mp h)
  have e : read a P33 σ embedding C p = evalRow C.I r := by
    apply AlgHom.ext
    intro x
    exact congrArg (fun α : CommRingCat.of Q ⟶ CommRingCat.of ℂ => α.hom x) eq
  apply Subtype.ext
  change readRow C.I (read a P33 σ embedding C p)=r.val
  rw [e,readRow_returns]

/-- The two genuine directions are readings of the very same
arithmetic-derived complex points, not an identification of two
distinct ambient schemes or a set-theoretic parametrization. -/
def chartEquiv : Row ≃ InChart where
  toFun := liftRow a P33 σ embedding C
  invFun := readRowOnWholePoint a P33 σ embedding C
  left_inv := read_eval a P33 σ embedding C
  right_inv := eval_read a P33 σ embedding C

end OriginalRetainedAffineChartPointEquiv318
