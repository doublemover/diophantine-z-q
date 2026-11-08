module
public import InfinityValuationFullInertia318
public import InfinityBasePoint318
public import Mathlib.NumberTheory.RamificationInertia.Galois
public section
noncomputable section
namespace InfinityReciprocalPrime318
open Polynomial InfinityReciprocalAction318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c:Fin 4→ℚˣ)
local instance chartAlgebra:Algebra (Base c) (Order c):=(ReciprocalInfinityBase318.chartMap c).toAlgebra
local instance chartSMul:SMul (Base c) (Order c):=(chartAlgebra c).toSMul
local instance chartModule:Module (Base c) (Order c):=Algebra.toModule
local instance baseDomain:IsDomain (Base c):=
  Localization.Away.isDomain (ReciprocalInfinityBase318.reciprocalDenominator_ne_zero c)
theorem base_dedekind:IsDedekindDomain (Base c):=
  IsLocalization.isDedekindDomain (ℚ[X])
    (M:=Submonoid.powers (ReciprocalInfinityBase318.reciprocalDenominator c))
    (by
      rintro _ ⟨n,rfl⟩
      exact mem_nonZeroDivisors_iff_ne_zero.mpr
        (pow_ne_zero n (ReciprocalInfinityBase318.reciprocalDenominator_ne_zero c))) (Base c)
/-- The literal rational s=0 prime on the original reciprocal open. -/
@[expose] def prime:Ideal (Base c):=RingHom.ker (InfinityBasePoint318.rationalPoint c)
theorem maximal:(prime c).IsMaximal:=by
  apply RingHom.ker_isMaximal_of_surjective
  intro q
  exact ⟨algebraMap ℚ[X] (Base c) (C q),by rw [InfinityBasePoint318.on_polynomial,Polynomial.eval_C]⟩
local instance basePrime:(prime c).IsPrime:=(maximal c).isPrime
lemma coordinate_mem:algebraMap ℚ[X] (Base c) X∈prime c:=by
  change InfinityBasePoint318.rationalPoint c (algebraMap ℚ[X] (Base c) X)=0
  rw [InfinityBasePoint318.on_polynomial,Polynomial.eval_X]
variable (Q:Ideal (Order c)) [Q.IsPrime]
local instance residueRat:Algebra ℚ Q.ResidueField:=
  ((algebraMap (Order c) Q.ResidueField).comp (algebraMap ℚ (Order c))).toAlgebra
variable (hs:InfinityPrimeSignInertia318.reciprocalCoordinate c∈Q)
include hs
lemma residue_base_square:(algebraMap (Order c) Q.ResidueField).comp (ReciprocalInfinityBase318.chartMap c)=
    (algebraMap ℚ Q.ResidueField).comp (InfinityBasePoint318.rationalPoint c):=by
  apply IsLocalization.ringHom_ext (Submonoid.powers (ReciprocalInfinityBase318.reciprocalDenominator c))
  apply Polynomial.ringHom_ext
  · intro q
    change algebraMap (Order c) Q.ResidueField
        (ReciprocalInfinityBase318.chartMap c (algebraMap ℚ[X] (Base c) (C q)))=
      algebraMap ℚ Q.ResidueField (InfinityBasePoint318.rationalPoint c (algebraMap ℚ[X] (Base c) (C q)))
    rw [InfinityBasePoint318.on_polynomial,Polynomial.eval_C]
    change algebraMap (Order c) Q.ResidueField
      (ReciprocalInfinityBase318.chartMap c (algebraMap ℚ (Base c) q))=_
    rw [RingHom.map_rat_algebraMap]
    rfl
  · change algebraMap (Order c) Q.ResidueField
        (InfinityPrimeSignInertia318.reciprocalCoordinate c)=
      algebraMap ℚ Q.ResidueField (InfinityBasePoint318.rationalPoint c (algebraMap ℚ[X] (Base c) X))
    rw [InfinityBasePoint318.on_polynomial,Polynomial.eval_X,map_zero]
    exact Ideal.algebraMap_residueField_eq_zero.mpr hs
/-- Every actual infinity prime lies over the same literal reciprocal base prime. -/
theorem liesOver:Q.LiesOver (prime c):=by
  constructor
  ext x
  change InfinityBasePoint318.rationalPoint c x=0 ↔ ReciprocalInfinityBase318.chartMap c x∈Q
  rw [←Ideal.algebraMap_residueField_eq_zero]
  have hx:=RingHom.congr_fun (residue_base_square c Q hs) x
  change algebraMap (Order c) Q.ResidueField (ReciprocalInfinityBase318.chartMap c x)=
    algebraMap ℚ Q.ResidueField (InfinityBasePoint318.rationalPoint c x) at hx
  rw [hx]
  constructor
  · intro h;rw [h,map_zero]
  · intro h
    exact (RingHom.injective (algebraMap ℚ Q.ResidueField)) (by simpa only [map_zero] using h)

omit hs in
/-- The actual finite reciprocal extension has separable residue extensions
at its rational infinity prime. -/
theorem residue_separable:Algebra.HasSeparableResidueFieldsAt (Base c) (Order c) (prime c):=by
  letI:Module.Finite (Base c) (Order c):=ReciprocalInfinityBase318.chartMap_finite c
  letI:Algebra.IsIntegral (Base c) (Order c):=Algebra.IsIntegral.of_finite _ _
  letI:Algebra ℚ (prime c).ResidueField:=
    ((algebraMap (Base c) (prime c).ResidueField).comp (algebraMap ℚ (Base c))).toAlgebra
  letI:CharZero (prime c).ResidueField:=Algebra.charZero_of_charZero ℚ (prime c).ResidueField
  infer_instance
end InfinityReciprocalPrime318
