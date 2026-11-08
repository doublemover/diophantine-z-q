module
public import ThreeArithmeticPoint318
public import QuotientJ318
public section
noncomputable section
namespace ThreeArithmeticQuotient318
open OpenJModel318 OpenJComplexEvaluation318 ThreeArithmeticPoint318
open GammaOneAtlas318 GammaOneFiber318 PeterssonQuotient318
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 0

/-- The actual analytic Gamma1(3) orbit quotient, restricted away from the
elliptic j-values excluded by the specified arithmetic integral model. -/
abbrev Source := {q : PeterssonQuotient318.Base (image 3) //
  QuotientJ318.jMap 3 q ≠ 0 ∧ QuotientJ318.jMap 3 q ≠ 1728}

@[expose] def projection (tau : UpperHalfPlane) (h : Admissible tau) : Source :=
  ⟨quotientMap 3 tau,h⟩

/-- Independence from the representative is proved using the actual
integral Gamma1 group and its actual marked-point transport. -/
theorem fixedPoint_eq_of_quotient_eq (N : ℕ) [NeZero N] (tau sigma : UpperHalfPlane)
    (ht : Admissible tau) (hs : Admissible sigma)
    (he : quotientMap 3 sigma=quotientMap 3 tau) :
    fixedPoint N sigma hs=fixedPoint N tau ht := by
  obtain ⟨g,hg,hP⟩ := (MarkedPeriod318.quotient_eq_iff_marked_transport 3 tau sigma).mp he
  have hm := (MarkedPeriod318.point_stabilizer 3 g tau).mp hP
  subst sigma
  exact fixedPoint_invariant N g hm tau ht

@[expose] def representative (q : Source) : UpperHalfPlane := (quotient_surjective 3 q.val).choose

lemma representative_projection (q : Source) : quotientMap 3 (representative q)=q.val :=
  (quotient_surjective 3 q.val).choose_spec

lemma representative_admissible (q : Source) : Admissible (representative q) := by
  have hj := congrArg (QuotientJ318.jMap 3) (representative_projection q)
  rw [QuotientJ318.jMap_projection] at hj
  simpa only [Admissible,hj] using q.property

/-- A genuine map from the existing analytic modular quotient to complex
points of the specified arithmetic full fixed algebra. This definition uses
a representative, but its exact representative-independent formula is proved below. -/
@[expose] def complexPoint (N : ℕ) [NeZero N] (q : Source) :
    LiteralThreeXComparison318.Fixed N →+* ℂ :=
  fixedPoint N (representative q) (representative_admissible q)

lemma complexPoint_projection (N : ℕ) [NeZero N] (tau : UpperHalfPlane) (h : Admissible tau) :
    complexPoint N (projection tau h)=fixedPoint N tau h := by
  apply fixedPoint_eq_of_quotient_eq
  exact representative_projection (projection tau h)

/-- Exact compatibility of the actual source-to-arithmetic map with genuine j. -/
theorem complexPoint_j (N : ℕ) [NeZero N] (q : Source) :
    complexPoint N q (algebraMap (OpenJModel318.Base N) (LiteralThreeXComparison318.Fixed N)
      (jCoord N))=QuotientJ318.jMap 3 q.val := by
  rw [complexPoint,fixedPoint_j]
  exact congrArg (QuotientJ318.jMap 3) (representative_projection q)

/-- Each descended point is an actual scheme-valued point of the specified
arithmetic model; no global analytification isomorphism is asserted. -/
@[expose] def schemePoint (N : ℕ) [NeZero N] (q : Source) :
    Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of (LiteralThreeXComparison318.Fixed N)) :=
  Scheme.Spec.map (CommRingCat.ofHom (complexPoint N q)).op

lemma schemePoint_projection (N : ℕ) [NeZero N] (tau : UpperHalfPlane) (h : Admissible tau) :
    schemePoint N (projection tau h)=
      Scheme.Spec.map (CommRingCat.ofHom (fixedPoint N tau h)).op := by
  rw [schemePoint,complexPoint_projection]

end ThreeArithmeticQuotient318
