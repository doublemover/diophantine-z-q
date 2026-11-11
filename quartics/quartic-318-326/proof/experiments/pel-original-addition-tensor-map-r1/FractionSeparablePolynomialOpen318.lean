module
public import FractionPolynomialFamilyLift318
public import Mathlib.FieldTheory.Separable
public section
noncomputable section
namespace FractionSeparablePolynomialOpen318
open Polynomial
variable (R K:Type*) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
/-- A monic separable polynomial over the ACTUAL fraction field spreads
to one literal nonzero principal open with its complete Bezout identity.
Consequently EVERY residue-field specialization there remains separable;
this is stronger than generic separability and uses no chosen root. -/
theorem exists_open (q:Polynomial K)(hm:q.Monic)(hs:q.Separable):
    ∃d:R,∃hd:d≠0,∃Q A B:Polynomial (Localization.Away d),
      Polynomial.map (FractionFiniteCoefficientLift318.toField R K d hd) Q=q ∧
      Q.Monic ∧ A*Q+B*Q.derivative=1:=by
  classical
  obtain ⟨a,b,hab⟩:=(Polynomial.separable_def' q).mp hs
  obtain ⟨d,hd,g,hg⟩:=FractionPolynomialFamilyLift318.exists_lift R K ![q,a,b]
  let e:=FractionFiniteCoefficientLift318.toField R K d hd
  have hi:Function.Injective e:=FractionFiniteCoefficientLift318.toField_injective R K d hd
  have hq:Polynomial.map e (g 0)=q:=hg 0
  have ha:Polynomial.map e (g 1)=a:=hg 1
  have hb:Polynomial.map e (g 2)=b:=hg 2
  refine ⟨d,hd,g 0,g 1,g 2,hq,?_,?_⟩
  · change (g 0).leadingCoeff=1
    apply hi
    rw [map_one,←Polynomial.leadingCoeff_map_of_injective hi,hq]
    exact hm
  · apply Polynomial.map_injective e hi
    simpa only [Polynomial.map_add,Polynomial.map_mul,Polynomial.map_one,
      ←Polynomial.derivative_map,hq,ha,hb] using hab

/-- The certificate survives arbitrary specialization, including at
points not known to come from the original analytic image. Monicity
preserves the full generic polynomial degree as well. -/
theorem specialize {d:R} {Q A B:Polynomial (Localization.Away d)}
    (hm:Q.Monic)(h:A*Q+B*Q.derivative=1)
    {L:Type*}[Field L](v:Localization.Away d→+*L):
    (Q.map v).Monic ∧ (Q.map v).Separable ∧ (Q.map v).natDegree=Q.natDegree:=by
  have hs:Q.Separable:=(Polynomial.separable_def' Q).mpr ⟨A,B,h⟩
  refine ⟨hm.map v,hs.map,?_⟩
  exact hm.natDegree_map v
end FractionSeparablePolynomialOpen318
