module
public import ActualJOrbitClassification318
public import ArithmeticPointTopology318
public import ThreeEffectiveSource318
public section
noncomputable section
open scoped MatrixGroups
namespace ArithmeticComparisonInjective318
open OpenJComplexEvaluation318 CanonicalXModularity318
open ThreeArithmeticQuotient318 ModularArithmeticCoordinates318
open MarkedPeriod318 EllipticTorsion318 ModularTorusTransport318 ModularTorsionTransport318
set_option maxHeartbeats 0

lemma gamma0_of_arithmeticX_eq (g : SL(2,ℤ)) (tau : UpperHalfPlane)
    (ht : Admissible tau) (hx : arithmeticX (g•tau)=arithmeticX tau) :
    g∈CongruenceSubgroup.Gamma0 3 := by
  have hs := CanonicalXModularity318.scale_transform
    ((Matrix.SpecialLinearGroup.mapGL (R:=ℤ) ℝ) g) ⟨g,rfl⟩ tau
  change CanonicalXScale318.scale (g•tau:UpperHalfPlane)=_ at hs
  have hn := CanonicalXScale318.scale_ne_zero 1 tau ht
  have hnt := CanonicalXScale318.scale_ne_zero 1 (g•tau)
    (ThreeArithmeticPoint318.admissible_transform g tau ht)
  have hstd : standardX (g•tau)=
      UpperHalfPlane.denom ((Matrix.SpecialLinearGroup.mapGL (R:=ℤ) ℝ) g) tau^2*standardX tau := by
    calc
      standardX (g•tau)=arithmeticX (g•tau)*CanonicalXScale318.scale (g•tau:UpperHalfPlane) := by
        unfold arithmeticX
        rw [div_mul_cancel₀ _ hnt]
      _=arithmeticX tau*(UpperHalfPlane.denom
          ((Matrix.SpecialLinearGroup.mapGL (R:=ℤ) ℝ) g) tau^2*CanonicalXScale318.scale (tau:ℂ)) := by
        rw [hx,hs]
      _=_ := by unfold arithmeticX; field_simp [hn] <;> ring
  let P : AnalyticThreeSignPoints318.Points (g•tau) :=
    ⟨pointAddEquiv g tau (standardPoint 3 tau),by
      change addOrderOf ((pointAddEquiv g tau).toAddMonoidHom (standardPoint 3 tau))=3
      rw [addOrderOf_injective (pointAddEquiv g tau).toAddMonoidHom (pointAddEquiv g tau).injective,
        standardPoint_order]⟩
  let Q : AnalyticThreeSignPoints318.Points (g•tau) :=
    ⟨standardPoint 3 (g•tau),standardPoint_order 3 (g•tau)⟩
  have hroot : AnalyticThreeSignPoints318.toRoot (g•tau) P=
      AnalyticThreeSignPoints318.toRoot (g•tau) Q := by
    apply Subtype.ext
    rw [ThreeArithmeticPoint318.toRoot_val,ThreeArithmeticPoint318.toRoot_val]
    change pointX (pointAddEquiv g tau (standardPoint 3 tau))=standardX (g•tau)
    rw [pointX_transport]
    exact hstd.symm
  have hsign := (AnalyticThreeSignPoints318.toRoot_eq_iff (g•tau) P Q).mp hroot
  have hlabel : residueMap g 3 (standardLabel 3)=standardLabel 3 ∨
      residueMap g 3 (standardLabel 3)= -(standardLabel 3) := by
    rcases hsign with h | h
    · left
      apply torsionMap_injective (g•tau) 3
      rw [←torsion_transport]
      exact h
    · right
      apply torsionMap_injective (g•tau) 3
      rw [map_neg,←torsion_transport]
      exact h
  apply CongruenceSubgroup.Gamma0_mem.mpr
  rcases hlabel with h | h
  · have hc := congrArg Prod.fst h
    simpa [residueMap,standardLabel] using hc
  · have hc := congrArg Prod.fst h
    simpa [residueMap,standardLabel] using hc

/-- Actual j and normalized torsion x separate the effective level-three source orbits. -/
theorem quotient_eq_of_coordinates_eq (tau sigma : UpperHalfPlane)
    (ht : Admissible tau) (hs : Admissible sigma)
    (hj : ActualQJ318.jInvariant tau=ActualQJ318.jInvariant sigma)
    (hx : arithmeticX tau=arithmeticX sigma) :
    GammaOneAtlas318.quotientMap 3 tau=GammaOneAtlas318.quotientMap 3 sigma := by
  obtain ⟨g,rfl⟩ := ActualJOrbitClassification318.exists_modular_of_j_eq tau sigma hj
  exact (ThreeEffectiveSource318.quotient_gamma0_invariant g
    (gamma0_of_arithmeticX_eq g tau ht hx.symm) tau).symm

/-- Injectivity of the actual map to the specified rank-four full fixed algebra,
including the central sign rather than identifying the rank-eight cover with the coarse quotient. -/
theorem complexPoint_injective (N : ℕ) [NeZero N] : Function.Injective (complexPoint N) := by
  intro p q hpq
  have hj : ActualQJ318.jInvariant (representative p)=ActualQJ318.jInvariant (representative q) := by
    have h := congrArg (fun f => f (algebraMap (OpenJModel318.Base N)
      (LiteralThreeXComparison318.Fixed N) (OpenJModel318.jCoord N))) hpq
    simpa only [complexPoint,ThreeArithmeticPoint318.fixedPoint_j] using h
  have hx : arithmeticX (representative p)=arithmeticX (representative q) := by
    simpa only [complexPoint_x,sourceX] using congrArg (fun f => f (xGenerator N)) hpq
  have he := quotient_eq_of_coordinates_eq (representative p) (representative q)
    (representative_admissible p) (representative_admissible q) hj hx
  apply Subtype.ext
  simpa only [representative_projection] using he

end ArithmeticComparisonInjective318
