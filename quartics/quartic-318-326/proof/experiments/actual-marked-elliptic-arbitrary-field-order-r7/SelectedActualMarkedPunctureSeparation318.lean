module

public import SelectedActualComplexWholeRootField318
public import HolomorphicCharts318
import ActualJOrbitClassification318

public section
noncomputable section

open scoped MatrixGroups
open OpenJComplexEvaluation318
open SelectedComplexOrdinaryBase318
open SelectedActualComplexWholeRootField318
open CanonicalXModularity318 ModularTorusTransport318 ModularTorsionTransport318
open MarkedPeriod318 EllipticTorsion318

namespace SelectedActualMarkedPunctureSeparation318

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

private theorem same_x_eq_or_eq_neg {W : WeierstrassCurve ℂ}
    (P Q : W.toAffine.Point) (hp : P ≠ 0) (hq : Q ≠ 0)
    (hx : pointX P = pointX Q) : P = Q ∨ P = -Q := by
  cases P with
  | zero => exact False.elim (hp rfl)
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero => exact False.elim (hq rfl)
    | some x₂ y₂ h₂ =>
      change x₁ = x₂ at hx
      exact WeierstrassCurve.Affine.Point.X_eq_iff.mp hx

private theorem standard_ne_zero (N : ℕ) [NeZero N] (hN : 1 < N) (τ : UpperHalfPlane) :
    standardPoint N τ ≠ 0 := by
  intro h
  have hOrder := standardPoint_order N τ
  rw [h] at hOrder
  have he : (1 : ℕ) = N := by simpa using hOrder
  omega

private theorem negative_label_gives_gammaOne
    (N : ℕ) (g : SL(2,ℤ))
    (h : residueMap g N (standardLabel N) = - (standardLabel N)) :
    -g ∈ CongruenceSubgroup.Gamma1 N := by
  have hc : (g 1 0 : ZMod N) = 0 := by
    have hC := congrArg Prod.fst h
    have h' : -(g 1 0 : ZMod N) = 0 := by
      simpa [residueMap,standardLabel] using hC
    exact neg_eq_zero.mp h'
  have ha : (g 0 0 : ZMod N) = -1 := by
    have hA := congrArg Prod.snd h
    simpa [residueMap,standardLabel] using hA
  apply (label_stabilizer N (-g)).mp
  apply Prod.ext <;>
    simp [residueMap,standardLabel,Matrix.SpecialLinearGroup.coe_neg,Matrix.neg_apply,
      Int.cast_neg,ha,hc]

/-- Equality of the actual two ordinary coordinates separates the
genuine fine-level orbit, for arbitrary N. Unlike the level-three
argument this does not enlarge the source action to Gamma0(N):
the two possible signs are resolved by the exact matrices g and -g. -/
theorem quotient_eq_of_marked_coordinates_eq
    (N : ℕ) [NeZero N] (hN : 1 < N)
    (τ σ : UpperHalfPlane) (hτ : Admissible τ) (hσ : Admissible σ)
    (hj : ActualQJ318.jInvariant τ = ActualQJ318.jInvariant σ)
    (hx : SelectedMarkedPeriodCoordinate318.arithmeticX N τ =
      SelectedMarkedPeriodCoordinate318.arithmeticX N σ) :
    GammaOneAtlas318.quotientMap N τ = GammaOneAtlas318.quotientMap N σ := by
  obtain ⟨g,rfl⟩ := ActualJOrbitClassification318.exists_modular_of_j_eq τ σ hj
  let G := (Matrix.SpecialLinearGroup.mapGL (R := ℤ) ℝ) g
  let d := UpperHalfPlane.denom G τ
  let Q := standardPoint N (g • τ)
  let P := pointAddEquiv g τ (standardPoint N τ)
  have hScale : CanonicalXScale318.scale ((g • τ : UpperHalfPlane) : ℂ) =
      d^2 * CanonicalXScale318.scale (τ : ℂ) :=
    CanonicalXModularity318.scale_transform G ⟨g,rfl⟩ τ
  have hp₀ := CanonicalXScale318.scale_ne_zero N τ hτ
  have hq₀ := CanonicalXScale318.scale_ne_zero N (g • τ) hσ
  have hVal : pointX Q = d^2 * pointX (standardPoint N τ) := by
    calc
      pointX Q = SelectedMarkedPeriodCoordinate318.arithmeticX N (g • τ) *
          CanonicalXScale318.scale ((g • τ : UpperHalfPlane) : ℂ) := by
        unfold SelectedMarkedPeriodCoordinate318.arithmeticX
        rw [div_mul_cancel₀ _ hq₀] <;> rfl
      _ = (pointX (standardPoint N τ) / CanonicalXScale318.scale (τ : ℂ)) *
          (d^2 * CanonicalXScale318.scale (τ : ℂ)) := by
        rw [← hx,hScale] <;> rfl
      _ = d^2 * pointX (standardPoint N τ) := by
        field_simp [hp₀]
        <;> ring
  have hxPQ : pointX P = pointX Q :=
    (pointX_transport g τ (standardPoint N τ)).trans hVal.symm
  have hp : P ≠ 0 := by
    intro hzero
    apply standard_ne_zero N hN τ
    apply (pointAddEquiv g τ).injective
    exact hzero.trans (map_zero (pointAddEquiv g τ)).symm
  have hq : Q ≠ 0 := standard_ne_zero N hN (g • τ)
  rcases same_x_eq_or_eq_neg P Q hp hq hxPQ with he | he
  · exact ((quotient_eq_iff_marked_transport N τ (g • τ)).mpr ⟨g,rfl,he⟩).symm
  · have hResid : residueMap g N (standardLabel N) = - (standardLabel N) := by
      apply torsionMap_injective (g • τ) N
      rw [← torsion_transport,map_neg]
      exact he
    have hNeg := negative_label_gives_gammaOne N g hResid
    have hQuot := (quotient_eq_iff_marked_transport N τ ((-g) • τ)).mpr
      ⟨-g,rfl,(point_stabilizer N (-g) τ).mpr hNeg⟩
    simpa only [ModularGroup.SL_neg_smul] using hQuot.symm

/-- The exact existing period-map pair separates the actual Γ₁ orbit.
There is no choice of roots of the original polynomial in this assertion. -/
theorem quotient_eq_of_periodMap_eq (N : ℕ) [NeZero N] (hN : 1 < N)
    (t s : Period) (h : periodMap N t = periodMap N s) :
    GammaOneAtlas318.quotientMap N t.val = GammaOneAtlas318.quotientMap N s.val := by
  have hJ := congrArg (fun z : Ordinary × ℂ => z.1.val) h
  have hX := congrArg Prod.snd h
  exact quotient_eq_of_marked_coordinates_eq N hN t.val s.val t.property s.property hJ hX

/-- In the same actual complex quotient chart, equality of the
ordinary J/marked-x data forces equality of the complex parameters.
This is the injectivity needed for the local uniformizer argument. -/
theorem local_fine_chart_eq_of_marked_coordinates_eq
    (N : ℕ) [NeZero N] (hN : 5 ≤ N) (τ : UpperHalfPlane) (w u : ℂ)
    (hw : w ∈ (HolomorphicCharts318.localChart N hN τ).target)
    (hu : u ∈ (HolomorphicCharts318.localChart N hN τ).target)
    (hwo : Admissible (UpperHalfPlane.ofComplex w)) (huo : Admissible (UpperHalfPlane.ofComplex u))
    (hJ : ActualQJ318.jInvariant (UpperHalfPlane.ofComplex w) =
      ActualQJ318.jInvariant (UpperHalfPlane.ofComplex u))
    (hX : SelectedMarkedPeriodCoordinate318.arithmeticX N (UpperHalfPlane.ofComplex w) =
      SelectedMarkedPeriodCoordinate318.arithmeticX N (UpperHalfPlane.ofComplex u)) :
    w = u := by
  let e := HolomorphicCharts318.localChart N hN τ
  have hE : e.symm w = e.symm u := by
    change (HolomorphicCharts318.localChart N hN τ).symm w =
      (HolomorphicCharts318.localChart N hN τ).symm u
    simp only [HolomorphicCharts318.localChart_symm_apply]
    exact quotient_eq_of_marked_coordinates_eq N (by omega)
      (UpperHalfPlane.ofComplex w) (UpperHalfPlane.ofComplex u) hwo huo hJ hX
  calc
    w = e (e.symm w) := (e.right_inv hw).symm
    _ = e (e.symm u) := congrArg e hE
    _ = u := e.right_inv hu

end SelectedActualMarkedPunctureSeparation318

#print axioms SelectedActualMarkedPunctureSeparation318.quotient_eq_of_periodMap_eq
#print axioms SelectedActualMarkedPunctureSeparation318.local_fine_chart_eq_of_marked_coordinates_eq
