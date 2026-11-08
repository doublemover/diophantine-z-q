module
public import ThreePrimitiveOrbit318
public section
noncomputable section
namespace ThreeArithmeticFiberSurjective318
open OpenJModel318 OpenJAffineScheme318 OpenJComplexEvaluation318
open ThreeArithmeticPoint318 CanonicalXModularity318 ThreeArithmeticQuotient318
open ModularCurveChange318
open scoped MatrixGroups
set_option maxHeartbeats 0

/-- Every point in the actual arithmetic four-point fiber above a realized
analytic j-value is attained by an actual integral modular transform of that
period. This is fiber surjectivity, not an assumption of global j-surjectivity. -/
theorem exists_modular_preimage (N : ℕ) [NeZero N] (tau : UpperHalfPlane) (h : Admissible tau) :
    letI : Algebra (Base N) ℂ := (evaluation N tau h).toAlgebra
    ∀f : LiteralThreeXComparison318.Fixed N →ₐ[Base N] ℂ,
      ∃g : SL(2,ℤ), fixedPoint N (g•tau) (admissible_transform g tau h)=f.toRingHom := by
  letI : Algebra (Base N) ℂ := (evaluation N tau h).toAlgebra
  intro f
  let e := ThreeTorsionSignQuotient318.signQuotientEquiv (A N) (B N) (discriminant_unit N)
  let fX := f.comp e.toAlgHom
  let r := LiteralThreeXComparison318.rootEquiv N tau h fX
  obtain ⟨P,hP⟩ := AnalyticThreeSignPoints318.toRoot_surjective tau r
  obtain ⟨g,hg⟩ := ThreePrimitiveOrbit318.exists_point_transport tau P.val P.property
  have hxP : pointX P.val=CanonicalXScale318.scale (tau:ℂ)*
      fX (AdjoinRoot.root (ShortThreeTorsion318.polynomial (A N) (B N))) := by
    rw [←toRoot_val,hP]
    exact LiteralThreeXComparison318.rootEquiv_apply N tau h fX
  have hpX := congrArg (fun Q => pointX Q) hg
  rw [pointX_transport] at hpX
  have hs := CanonicalXModularity318.scale_transform
    ((Matrix.SpecialLinearGroup.mapGL (R:=ℤ) ℝ) g) ⟨g,rfl⟩ tau
  change CanonicalXScale318.scale (g•tau:UpperHalfPlane)=_ at hs
  have hxnew : arithmeticX (g•tau)=
      fX (AdjoinRoot.root (ShortThreeTorsion318.polynomial (A N) (B N))) := by
    change pointX (MarkedPeriod318.standardPoint 3 (g•tau)) /
      CanonicalXScale318.scale (g•tau:UpperHalfPlane)=_
    rw [←hpX,hs,hxP]
    field_simp [UpperHalfPlane.denom_ne_zero,CanonicalXScale318.scale_ne_zero N tau h]
  have he : point N (g•tau) (admissible_transform g tau h)=fX.toRingHom := by
    apply AdjoinRoot.ringHom_ext
    · rw [←AdjoinRoot.algebraMap_eq,point_comp_base]
      rw [evaluation_eq_of_j_eq N (g•tau) tau _ _ (j_transform g tau)]
      ext r
      exact (fX.commutes r).symm
    · rw [point_root]
      exact hxnew
  refine ⟨g,?_⟩
  ext z
  obtain ⟨x,rfl⟩ := e.surjective z
  change point N (g•tau) (admissible_transform g tau h) (e.symm (e x))=f (e x)
  rw [e.symm_apply_apply,he]
  rfl

/-- The preimage lies on the existing analytic quotient and has exactly
the original genuine j-value. -/
theorem exists_source_preimage (N : ℕ) [NeZero N] (tau : UpperHalfPlane) (h : Admissible tau) :
    letI : Algebra (Base N) ℂ := (evaluation N tau h).toAlgebra
    ∀f : LiteralThreeXComparison318.Fixed N →ₐ[Base N] ℂ,
      ∃q : ThreeArithmeticQuotient318.Source,
        complexPoint N q=f.toRingHom ∧ QuotientJ318.jMap 3 q.val=ActualQJ318.jInvariant tau := by
  letI : Algebra (Base N) ℂ := (evaluation N tau h).toAlgebra
  intro f
  obtain ⟨g,hg⟩ := exists_modular_preimage N tau h f
  refine ⟨projection (g•tau) (admissible_transform g tau h),?_,?_⟩
  · rw [complexPoint_projection,hg]
  · exact j_transform g tau

end ThreeArithmeticFiberSurjective318
