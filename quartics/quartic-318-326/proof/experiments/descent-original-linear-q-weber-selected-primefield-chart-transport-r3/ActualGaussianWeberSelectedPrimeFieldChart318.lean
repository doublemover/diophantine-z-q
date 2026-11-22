module
public import ActualGaussianWeberSelectedGaussianPrime318
public import ActualGaussianWeberTranslationFunctionField318
public section
noncomputable section

namespace ActualGaussianWeberSelectedPrimeFieldChart318

open IsLocalRing Polynomial
open ActualGaussianWeberSelectedGaussianPrime318
open ActualGaussianWeberQuadraticGenericChart318 ActualGaussianWeberGenericChartDomain318
open ActualGaussianWeberGaussLocalization318 ActualGaussianWeberTranslationFunctionField318

theorem along_chart_injective {K L : Type*} [Field K] [Field L] (f : K→+*L) :
    Function.Injective (((fractionMap L).comp (mapChart f)) : Chart K→+*FunctionField L) := by
  intro A B h
  have h' : fractionMap L (mapChart f A)=fractionMap L (mapChart f B) := h
  exact mapChart_injective f f.injective (fractionMap_injective L h')

@[expose] def along_coefficients {K L : Type*} [Field K] [Field L] (f : K→+*L) :
    FunctionField K→+*FunctionField L :=
  IsFractionRing.lift (K := FunctionField K)
    (g := (((fractionMap L).comp (mapChart f)) : Chart K→+*FunctionField L))
    (along_chart_injective f)

private theorem along_chart {K L : Type*} [Field K] [Field L] (f : K→+*L) (z : Chart K) :
    along_coefficients f (fractionMap K z)=fractionMap L (mapChart f z) := by
  unfold along_coefficients
  exact IsFractionRing.lift_algebraMap (K := FunctionField K)
    (g := (((fractionMap L).comp (mapChart f)) : Chart K→+*FunctionField L))
    (along_chart_injective f) z

private theorem along_polynomial {K L : Type*} [Field K] [Field L]
    (f : K→+*L) (P : K[X]) :
    along_coefficients f (fractionMap K (AdjoinRoot.of (relation K) P))=
      fractionMap L (AdjoinRoot.of (relation L) (P.map f)) := by
  rw [along_chart]
  simp only [mapChart,AdjoinRoot.map_of,coe_mapRingHom]

theorem along_x {K L : Type*} [Field K] [Field L] (f : K→+*L) :
    along_coefficients f (xGeneric K)=xGeneric L := by
  change along_coefficients f (fractionMap K (AdjoinRoot.of (relation K) X))=_
  rw [along_polynomial,map_X] <;> rfl

theorem along_y {K L : Type*} [Field K] [Field L] (f : K→+*L) :
    along_coefficients f (yGeneric K)=yGeneric L := by
  change along_coefficients f (fractionMap K (AdjoinRoot.root (relation K)))=_
  rw [along_chart]
  change fractionMap L (mapChart f (AdjoinRoot.root (relation K)))=
    fractionMap L (AdjoinRoot.root (relation L))
  simp only [mapChart,AdjoinRoot.map_root]

theorem along_const {K L : Type*} [Field K] [Field L] (f : K→+*L) (i : K) :
    along_coefficients f (constGeneric K i)=constGeneric L (f i) := by
  change along_coefficients f (fractionMap K (AdjoinRoot.of (relation K) (C i)))=_
  rw [along_polynomial,map_C] <;> rfl

variable {p : ℕ} [Fact p.Prime]

/-- The actual chart function-field map at the fixed signed base place.
The residue equivalence is that of the same Gaussian prime. -/
@[expose] def selectedField (s : ZMod p) (hs : s^2= -1) :
    FunctionField (ResidueField (BasePlace s hs))→+*FunctionField (ZMod p) :=
  along_coefficients (residueEquiv s hs).toRingHom

/-- Exact transport of the actual selected unit and both actual chart
generators, before any scalar or Frobenius theorem enters. -/
theorem selected_i_and_generic_coordinates (s : ZMod p) (hs : s^2= -1) :
    let V := BasePlace s hs
    let k := ResidueField V
    let F := selectedField s hs
    F (constGeneric k (residue V (integralI s hs)))=constGeneric (ZMod p) s ∧
    F (xGeneric k)=xGeneric (ZMod p) ∧ F (yGeneric k)=yGeneric (ZMod p) := by
  dsimp only
  let V := BasePlace s hs
  let k := ResidueField V
  let f : k→+*ZMod p := (residueEquiv s hs).toRingHom
  refine ⟨?_,along_x f,along_y f⟩
  exact (along_const f (residue V (integralI s hs))).trans
    (congrArg (constGeneric (ZMod p)) (residueEquiv_i s hs))

end ActualGaussianWeberSelectedPrimeFieldChart318
