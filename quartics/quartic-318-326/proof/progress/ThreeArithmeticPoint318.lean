module
public import CanonicalXModularity318
public import AnalyticThreeSignPoints318
public section
noncomputable section
namespace ThreeArithmeticPoint318
open OpenJModel318 OpenJAffineScheme318 OpenJComplexEvaluation318 CanonicalXModularity318
open scoped MatrixGroups
set_option maxHeartbeats 0

lemma evaluation_eq_of_j_eq (N : ℕ) [NeZero N] (tau sigma : UpperHalfPlane)
    (ht : Admissible tau) (hs : Admissible sigma)
    (hj : ActualQJ318.jInvariant tau=ActualQJ318.jInvariant sigma) :
    evaluation N tau ht=evaluation N sigma hs := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (OpenJModel318.denominator N))
  simp only [evaluation,IsLocalization.Away.lift_comp,polynomialEval,hj]

lemma j_transform (g : SL(2,ℤ)) (tau : UpperHalfPlane) :
    ActualQJ318.jInvariant (g•tau)=ActualQJ318.jInvariant tau :=
  ActualJInvariant318.modular_invariant ((Matrix.SpecialLinearGroup.mapGL (R:=ℤ) ℝ) g) ⟨g,rfl⟩ tau

lemma admissible_transform (g : SL(2,ℤ)) (tau : UpperHalfPlane) (h : Admissible tau) :
    Admissible (g•tau) := by
  simpa only [Admissible,j_transform] using h

@[expose] def standardRoot (tau : UpperHalfPlane) : LiteralThreeXComparison318.AnalyticRoots tau :=
  AnalyticThreeSignPoints318.toRoot tau ⟨MarkedPeriod318.standardPoint 3 tau,
    MarkedPeriod318.standardPoint_order 3 tau⟩

lemma toRoot_val (tau : UpperHalfPlane) (P : AnalyticThreeSignPoints318.Points tau) :
    (AnalyticThreeSignPoints318.toRoot tau P).val=pointX P.val := by
  obtain ⟨P,hP⟩ := P
  cases P with
  | zero =>
    change addOrderOf (0 : (ModularWeierstrass318.curve tau).toAffine.Point)=3 at hP
    simp at hP
  | some x y hn => rfl

lemma standardRoot_val (tau : UpperHalfPlane) : (standardRoot tau).val=standardX tau :=
  toRoot_val tau _

@[expose] def pointAlgHom (N : ℕ) [NeZero N] (tau : UpperHalfPlane) (h : Admissible tau) :
    letI : Algebra (Base N) ℂ := (evaluation N tau h).toAlgebra
    ThreeTorsionAlgebra318.XRing (A N) (B N) →ₐ[Base N] ℂ := by
  letI : Algebra (Base N) ℂ := (evaluation N tau h).toAlgebra
  exact (LiteralThreeXComparison318.rootEquiv N tau h).symm (standardRoot tau)

/-- A genuine complex point of the specific integral arithmetic quartic,
constructed from the actual period point 1/3. -/
@[expose] def point (N : ℕ) [NeZero N] (tau : UpperHalfPlane) (h : Admissible tau) :
    ThreeTorsionAlgebra318.XRing (A N) (B N) →+* ℂ := by
  letI : Algebra (Base N) ℂ := (evaluation N tau h).toAlgebra
  exact (pointAlgHom N tau h).toRingHom

lemma point_base (N : ℕ) [NeZero N] (tau : UpperHalfPlane) (h : Admissible tau) (r : Base N) :
    point N tau h (algebraMap (Base N) (ThreeTorsionAlgebra318.XRing (A N) (B N)) r)=
      evaluation N tau h r := by
  letI : Algebra (Base N) ℂ := (evaluation N tau h).toAlgebra
  exact (pointAlgHom N tau h).commutes r

lemma point_comp_base (N : ℕ) [NeZero N] (tau : UpperHalfPlane) (h : Admissible tau) :
    (point N tau h).comp (algebraMap (Base N) (ThreeTorsionAlgebra318.XRing (A N) (B N)))=
      evaluation N tau h := RingHom.ext (point_base N tau h)

/-- Exact normalized torsion-coordinate formula for the arithmetic point. -/
lemma point_root (N : ℕ) [NeZero N] (tau : UpperHalfPlane) (h : Admissible tau) :
    point N tau h (AdjoinRoot.root (ShortThreeTorsion318.polynomial (A N) (B N)))=
      arithmeticX tau := by
  letI : Algebra (Base N) ℂ := (evaluation N tau h).toAlgebra
  have he := LiteralThreeXComparison318.rootEquiv_apply N tau h (pointAlgHom N tau h)
  have hr : LiteralThreeXComparison318.rootEquiv N tau h (pointAlgHom N tau h)=standardRoot tau :=
    (LiteralThreeXComparison318.rootEquiv N tau h).apply_symm_apply (standardRoot tau)
  rw [hr,standardRoot_val] at he
  apply (eq_div_iff (CanonicalXScale318.scale_ne_zero N tau h)).mpr
  change (pointAlgHom N tau h) (AdjoinRoot.root
    (ShortThreeTorsion318.polynomial (A N) (B N))) * CanonicalXScale318.scale (tau:ℂ) = standardX tau
  simpa only [mul_comm] using he.symm

/-- The actual source group preserves the constructed arithmetic point,
not merely its j-coordinate or the set of four possible x-labels. -/
theorem point_invariant (N : ℕ) [NeZero N] (g : SL(2,ℤ))
    (hg : g ∈ CongruenceSubgroup.Gamma1 3) (tau : UpperHalfPlane) (h : Admissible tau) :
    point N (g•tau) (admissible_transform g tau h)=point N tau h := by
  apply AdjoinRoot.ringHom_ext
  · rw [←AdjoinRoot.algebraMap_eq,point_comp_base,point_comp_base]
    exact evaluation_eq_of_j_eq N _ _ _ _ (j_transform g tau)
  · rw [point_root,point_root,arithmeticX_invariant g hg tau]

@[expose] def fixedPoint (N : ℕ) [NeZero N] (tau : UpperHalfPlane) (h : Admissible tau) :
    LiteralThreeXComparison318.Fixed N →+* ℂ :=
  (point N tau h).comp (ThreeTorsionSignQuotient318.signQuotientEquiv
    (A N) (B N) (discriminant_unit N)).symm.toRingEquiv.toRingHom

lemma fixedPoint_invariant (N : ℕ) [NeZero N] (g : SL(2,ℤ))
    (hg : g ∈ CongruenceSubgroup.Gamma1 3) (tau : UpperHalfPlane) (h : Admissible tau) :
    fixedPoint N (g•tau) (admissible_transform g tau h)=fixedPoint N tau h := by
  unfold fixedPoint
  rw [point_invariant N g hg tau h]

lemma fixedPoint_base (N : ℕ) [NeZero N] (tau : UpperHalfPlane) (h : Admissible tau)
    (r : Base N) : fixedPoint N tau h (algebraMap (Base N) (LiteralThreeXComparison318.Fixed N) r)=
      evaluation N tau h r := by
  change point N tau h ((ThreeTorsionSignQuotient318.signQuotientEquiv
    (A N) (B N) (discriminant_unit N)).symm
      (algebraMap (Base N) (LiteralThreeXComparison318.Fixed N) r)) = _
  rw [AlgEquiv.commutes,point_base]

lemma fixedPoint_j (N : ℕ) [NeZero N] (tau : UpperHalfPlane) (h : Admissible tau) :
    fixedPoint N tau h (algebraMap (Base N) (LiteralThreeXComparison318.Fixed N) (jCoord N))=
      ActualQJ318.jInvariant tau := by
  rw [fixedPoint_base,evaluation_jCoord]

end ThreeArithmeticPoint318
