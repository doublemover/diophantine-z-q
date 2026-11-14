module
public import PELOriginalHomogeneousRatioDependence318
public section
noncomputable section
namespace PELOriginalChartFractionDependence318
open scoped BigOperators
open PELOriginalGradedSectionRing318 PELOriginalCubicRelationIdeal318 PELOriginalLevelTheta318
variable (τ:ℂ)(hτ:0<τ.im)
/-- A positive common degree is PRODUCED from all three actual chart
normal forms. Degree-zero numerators are retained, not excluded. -/
@[expose] def commonDegree(n:Fin 3→ℕ):ℕ:=1+∑i:Fin 3,n i
lemma commonDegree_pos(n:Fin 3→ℕ):0<commonDegree n:=by unfold commonDegree;omega
lemma degree_le(n:Fin 3→ℕ)(i:Fin 3):n i≤commonDegree n:=by
  have h:n i≤∑k:Fin 3,n k:=Finset.single_le_sum (fun k hk=>Nat.zero_le _) (Finset.mem_univ i)
  unfold commonDegree
  omega
@[expose] def commonNumerator(j:Label 3)(n:Fin 3→ℕ)(A:Fin 3→Equations)(i:Fin 3):Equations:=
  A i*(MvPolynomial.X j)^(commonDegree n-n i)
lemma numerator_homogeneous(j:Label 3)(n:Fin 3→ℕ)(A:Fin 3→Equations)
    (hA:∀i,(A i).IsHomogeneous (n i))(i:Fin 3):
    (commonNumerator j n A i).IsHomogeneous (commonDegree n):=by
  have h:=(hA i).mul (MvPolynomial.isHomogeneous_X_pow (R:=ℂ) j (commonDegree n-n i))
  simpa only [Nat.add_sub_of_le (degree_le n i)] using h
lemma common_fraction {K:Type*}[Field K][Algebra ℂ K]
    (F:Ring τ hτ→ₐ[ℂ]K)(j:Label 3)(hj:F (generators τ hτ j)≠0)
    (n:Fin 3→ℕ)(A:Fin 3→Equations)(i:Fin 3):
    F (presentation τ hτ (commonNumerator j n A i))/
      F (presentation τ hτ ((MvPolynomial.X j)^commonDegree n))=
      F (presentation τ hτ (A i))/(F (generators τ hτ j))^(n i):=by
  simp only [commonNumerator,map_mul,map_pow,variable_image]
  have hp:(F (generators τ hτ j))^commonDegree n=
      (F (generators τ hτ j))^(n i)*(F (generators τ hτ j))^(commonDegree n-n i):=by
    rw [←pow_add,Nat.add_sub_of_le (degree_le n i)]
  rw [hp]
  field_simp [hj] <;> ring
/-- ALL three genuine homogeneous chart fractions, with unrelated
original denominator powers, satisfy a nonzero polynomial relation.
No bounded-degree or common-denominator hypothesis is left to the
consumer: the common denominator above was actually constructed. -/
theorem not_algebraicIndependent {K:Type*}[Field K][Algebra ℂ K]
    (F:Ring τ hτ→ₐ[ℂ]K)(j:Label 3)(hj:F (generators τ hτ j)≠0)
    (n:Fin 3→ℕ)(A:Fin 3→Equations)(hA:∀i,(A i).IsHomogeneous (n i)):
    ¬AlgebraicIndependent ℂ
      (fun i=>F (presentation τ hτ (A i))/(F (generators τ hτ j))^(n i)):=by
  have h:=PELOriginalHomogeneousRatioDependence318.not_algebraicIndependent τ hτ F
    (commonDegree n) (commonDegree_pos n) ((MvPolynomial.X j)^commonDegree n)
    (commonNumerator j n A) (MvPolynomial.isHomogeneous_X_pow (R:=ℂ) j _)
    (numerator_homogeneous j n A hA) (by simpa only [map_pow,variable_image] using pow_ne_zero (commonDegree n) hj)
  simpa only [common_fraction τ hτ F j hj n A] using h
end PELOriginalChartFractionDependence318
