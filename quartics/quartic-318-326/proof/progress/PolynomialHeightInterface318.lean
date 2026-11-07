module
public import FiniteGeneratorEnumeration318
public import PolynomialCandidate318
public import GlobalSaturationHeight318
public section
namespace PolynomialHeightInterface318
open ConcreteG8Domain LocalGenerator318 GlobalSaturationHeight318 FiniteGeneratorEnumeration318
open WeierstrassCurve.Affine
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- The primitive-polynomial box stated in the manuscript, before applying
the quadratic formula or the finite search. -/
@[expose] def PolynomialBox (u v:ℚ) : Prop :=
  (∃(a:ℤ)(b:ℕ),-9≤a ∧ a≤9 ∧ 1≤b ∧ b≤9 ∧ u=(a:ℚ)/b ∧ v=0) ∨
  (v≠0 ∧ ∃(a:ℕ)(b c:ℤ)(k:ℕ),
    1≤a ∧ a≤81 ∧ -162≤b ∧ b≤162 ∧ c.natAbs≤81 ∧ 1≤k ∧ k≤162 ∧
    Nat.gcd (Nat.gcd a b.natAbs) c.natAbs=1 ∧
    (a:K)*(pair u v)^2+(b:K)*(pair u v)+(c:K)=0 ∧
    b^2-4*(a:ℤ)*c=2*(k:ℤ)^2)

theorem polynomial_box_coordinates (u v:ℚ) (h:PolynomialBox u v) : CandidateCoordinates u v := by
  rcases h with hr|⟨hv,a,b,c,k,ha,hA,hb,hB,hc,hk,hK,hg,hpoly,hdisc⟩
  · exact Or.inl hr
  · have ha0 : (a:ℤ)≠0 := by omega
    have hpoly' : ((a:ℤ):K)*(pair u v)^2+(b:K)*(pair u v)+(c:K)=0 := by simpa using hpoly
    obtain ⟨hu,hv'⟩ := PolynomialCandidate318.quadratic_coordinates (a:ℤ) b c k u v ha0 hv hpoly' hdisc
    have hp := PolynomialCandidate318.primitive_candidate a b c k (by omega) hc hg hdisc
    right
    refine ⟨a,b,k,ha,hA,hb,hB,hk,hK,hp,?_,?_⟩
    · simpa using hu
    · simpa using hv'

/-- Exact still-unproved Northcott coefficient bound for this actual
absolute number-field x-height. No curve-square test is assumed here. -/
@[expose] def PolynomialHeightCoverage : Prop :=
  ∀Q:E.Point,xHeight Q<Real.log 9 → Q=0 ∨
    ∃(u v:ℚ)(y:K)(h:E.Nonsingular (pair u v) y),Q=Point.some _ y h ∧ PolynomialBox u v

theorem small_height_candidates (coverage:PolynomialHeightCoverage) (Q:E.Point)
    (hq:xHeight Q<Real.log 9) : Q=0 ∨ CandidatePoint Q := by
  rcases coverage Q hq with hz|⟨u,v,y,h,he,hbox⟩
  · exact Or.inl hz
  · exact Or.inr ⟨u,v,y,h,he,polynomial_box_coordinates u v hbox⟩

end PolynomialHeightInterface318
