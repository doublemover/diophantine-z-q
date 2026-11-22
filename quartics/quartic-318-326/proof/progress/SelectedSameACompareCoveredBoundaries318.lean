module

public import SelectedSameASignedCoverInjectiveJoin318
public import SelectedSameACoboundaryGivesActualGlobalLift318
import all SelectedSameAGenuineBoundaryLifts318

/-! Compare the actual old and principal-unit boundary on one common
cover. The missing arithmetic-geometric coefficient comparison is
not an input masquerading as exactness or as equality in H¹: it is
the explicit restricted affine gauge, with its original sign.
The proof computes the difference inside one actual injective row. -/

public section
noncomputable section

open CategoryTheory Opposite TopologicalSpace

namespace SelectedSameACompareCoveredBoundaries318

open SelectedSameAActualLiftDifference318 (Sh local_inclusion_injective)
open SelectedSameASignedLiftCocycle318 (res coeff coeff_beta)
open SelectedSameASignedCoverInjectiveJoin318 (factor_cover_coeff)
open SelectedSameAGenuineBoundaryLifts318 (boundary)
open SelectedSameALiteralInjectiveRow318 (factor target target_shortExact boundary_eq)

universe u w

variable (X : TopCat.{u})
variable [HasSheafify (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable {ι : Type u} (U : ι → Opens X)

/-- Subtraction of actual lift differences in a single exact row. -/
theorem coeff_sub {T : ShortComplex (Sh X)} (hT : T.ShortExact)
    (z₁ z₂ : T.X₃.obj.obj (op (⊤ : Opens X)))
    (t₁ t₂ : ∀ i, T.X₂.obj.obj (op (U i)))
    (h₁ : ∀ i, T.g.hom.app (op (U i)) (t₁ i) = res X T.X₃ le_top z₁)
    (h₂ : ∀ i, T.g.hom.app (op (U i)) (t₂ i) = res X T.X₃ le_top z₂)
    (hs : ∀ i, T.g.hom.app (op (U i)) (t₁ i - t₂ i) = res X T.X₃ le_top (z₁ - z₂))
    (i j : ι) :
    coeff X T hT U (z₁ - z₂) (fun i => t₁ i - t₂ i) hs i j =
      coeff X T hT U z₁ t₁ h₁ i j - coeff X T hT U z₂ t₂ h₂ i j := by
  let W := U i ⊓ U j
  let fW := T.f.hom.app (op W)
  let ri := res X T.X₂ (show W ≤ U i from inf_le_left)
  let rj := res X T.X₂ (show W ≤ U j from inf_le_right)
  apply local_inclusion_injective X T hT W
  change fW (coeff X T hT U (z₁ - z₂) (fun i => t₁ i - t₂ i) hs i j) =
    fW (coeff X T hT U z₁ t₁ h₁ i j - coeff X T hT U z₂ t₂ h₂ i j)
  calc
    _ = rj (t₁ j - t₂ j) - ri (t₁ i - t₂ i) := coeff_beta X T hT U
        (z₁ - z₂) (fun i => t₁ i - t₂ i) hs i j
    _ = (rj (t₁ j) - ri (t₁ i)) - (rj (t₂ j) - ri (t₂ i)) := by
      rw [rj.hom.map_sub (t₁ j) (t₂ j), ri.hom.map_sub (t₁ i) (t₂ i)]
      abel
    _ = fW (coeff X T hT U z₁ t₁ h₁ i j) -
        fW (coeff X T hT U z₂ t₂ h₂ i j) :=
      congrArg₂ (fun x y : T.X₂.obj.obj (op W) => x - y)
        (coeff_beta X T hT U z₁ t₁ h₁ i j).symm
        (coeff_beta X T hT U z₂ t₂ h₂ i j).symm
    _ = fW (coeff X T hT U z₁ t₁ h₁ i j - coeff X T hT U z₂ t₂ h₂ i j) :=
      (fW.hom.map_sub _ _).symm

variable [HasExt.{w} (Sh X)]

/-- The first source row is the old cotangent row with the actual
left contraction. The second is the forward normalized principal-unit
row with its marked identity into the same additive structure sheaf.
The comparison consumes the two actual lift families on the same
refined opens and the signed geometric gauge there. -/
theorem boundary_eq_of_old_minus_forward
    {S Q : ShortComplex (Sh X)} {L : Sh X}
    (hS : S.ShortExact) (hQ : Q.ShortExact)
    (lambdaA : S.X₁ ⟶ L) (muA : Q.X₁ ⟶ L) (hc : (⊤ : Opens X) ≤ ⨆ i, U i)
    (zS : S.X₃.obj.obj (op (⊤ : Opens X)))
    (zQ : Q.X₃.obj.obj (op (⊤ : Opens X)))
    (tS : ∀ i, S.X₂.obj.obj (op (U i)))
    (tQ : ∀ i, Q.X₂.obj.obj (op (U i)))
    (hs : ∀ i, S.g.hom.app (op (U i)) (tS i) = res X S.X₃ le_top zS)
    (hq : ∀ i, Q.g.hom.app (op (U i)) (tQ i) = res X Q.X₃ le_top zQ)
    (d : ∀ i, L.obj.obj (op (U i)))
    (hd : ∀ i j, lambdaA.hom.app (op (U i ⊓ U j)) (coeff X S hS U zS tS hs i j) -
        muA.hom.app (op (U i ⊓ U j)) (coeff X Q hQ U zQ tQ hq i j) =
      res X L inf_le_left (d i) - res X L inf_le_right (d j)) :
    Sheaf.H.map lambdaA 1 (boundary X hS zS) = Sheaf.H.map muA 1 (boundary X hQ zQ) := by
  let T := target X L
  let hT : T.ShortExact := target_shortExact X L
  let FS := factor X hS lambdaA
  let FQ := factor X hQ muA
  let x : T.X₃.obj.obj (op (⊤ : Opens X)) := FS.τ₃.hom.app (op (⊤ : Opens X)) zS
  let y : T.X₃.obj.obj (op (⊤ : Opens X)) := FQ.τ₃.hom.app (op (⊤ : Opens X)) zQ
  let u (i : ι) : T.X₂.obj.obj (op (U i)) := FS.τ₂.hom.app (op (U i)) (tS i)
  let v (i : ι) : T.X₂.obj.obj (op (U i)) := FQ.τ₂.hom.app (op (U i)) (tQ i)
  obtain ⟨hu, huc⟩ := factor_cover_coeff X hS lambdaA U zS tS hs
  obtain ⟨hv, hvc⟩ := factor_cover_coeff X hQ muA U zQ tQ hq
  have hu' (i : ι) : T.g.hom.app (op (U i)) (u i) = res X T.X₃ le_top x := hu i
  have hv' (i : ι) : T.g.hom.app (op (U i)) (v i) = res X T.X₃ le_top y := hv i
  have hsub (i : ι) :
      T.g.hom.app (op (U i)) (u i - v i) = res X T.X₃ le_top (x - y) := by
    rw [(T.g.hom.app (op (U i))).hom.map_sub, hu', hv',
      (res X T.X₃ (show U i ≤ (⊤ : Opens X) from le_top)).hom.map_sub]
  have hcoef (i j : ι) :
      coeff X T hT U (x - y) (fun i => u i - v i) hsub i j =
        res X T.X₁ inf_le_left (d i) - res X T.X₁ inf_le_right (d j) := by
    have h := coeff_sub X U hT x y u v hu' hv' hsub i j
    refine h.trans ?_
    have hs' : coeff X T hT U x u hu' i j =
      lambdaA.hom.app (op (U i ⊓ U j)) (coeff X S hS U zS tS hs i j) := huc i j
    have hq' : coeff X T hT U y v hv' i j =
      muA.hom.app (op (U i ⊓ U j)) (coeff X Q hQ U zQ tQ hq i j) := hvc i j
    exact (congrArg₂ (fun a b : T.X₁.obj.obj (op (U i ⊓ U j)) => a - b) hs' hq').trans (hd i j)
  have hz : boundary X hT (x - y) = 0 := by
    unfold boundary
    exact SelectedSameACoboundaryGivesActualGlobalLift318.boundary_zero
      X T hT U hc (x - y) (fun i => u i - v i) hsub d hcoef
  let bx : L.H 1 := boundary X hT x
  let by' : L.H 1 := boundary X hT y
  have hxy : bx = by' :=
    sub_eq_zero.mp ((map_sub (boundary X hT) x y).symm.trans hz)
  have hLeft : Sheaf.H.map lambdaA 1 (boundary X hS zS) = bx :=
    (boundary_eq X hS lambdaA zS).symm
  have hRight : by' = Sheaf.H.map muA 1 (boundary X hQ zQ) :=
    boundary_eq X hQ muA zQ
  exact Eq.trans hLeft (Eq.trans hxy hRight)

end SelectedSameACompareCoveredBoundaries318
