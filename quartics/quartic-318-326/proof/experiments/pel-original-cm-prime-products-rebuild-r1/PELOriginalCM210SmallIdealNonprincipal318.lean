module
public import PELOriginalCM210SmallNormObstruction318
public import PELOriginalCM210NativePrimeNorm318
public import Mathlib.RingTheory.PrincipalIdealDomain
public section
noncomputable section
namespace PELOriginalCM210SmallIdealNonprincipal318
open PELOriginalCM210IntegralConjugation318 PELOriginalCM210NativeIntegerOrder318
open PELOriginalCM210NativeElementNorm318 PELOriginalCM210SmallNormObstruction318
open PELOriginalCM210NativePrimeResidue318 PELOriginalCM210NativePrimeNorm318
lemma no_principal_of_norm (I:Ideal O) (d:ℕ) (hn:Ideal.absNorm I=d)
    (hd:(d:ℤ)<210) (hns:∀r:ℤ,r^2≠(d:ℤ)) : ¬I.IsPrincipal := by
  intro hI
  letI := hI
  let z : R := integerEquiv.symm (Submodule.IsPrincipal.generator I)
  have hg : Ideal.span ({integerEquiv z}:Set O)=I := by
    simpa only [z,RingEquiv.apply_symm_apply] using Ideal.span_singleton_generator I
  have hnorm : (z.re^2+210*z.im^2).natAbs=d := by
    rw [←principal_norm,hg,hn]
  have he := congrArg (fun n:ℕ=>(n:ℤ)) hnorm
  rw [←Int.eq_natAbs_of_nonneg (norm_nonneg z)] at he
  exact small_norm (d:ℤ) hd hns z he
instance (i:Fin 14) : NeZero (divisor i) := ⟨Nat.ne_of_gt (divisor_properties i).1⟩
lemma actual_nonprincipal (i:Fin 14) :
    ¬(nativeIdeal (divisor i) (divisor_properties i).2.2).IsPrincipal := by
  apply no_principal_of_norm _ _ (native_norm _ _)
  · exact_mod_cast (divisor_properties i).2.1
  · exact divisor_nonsquare i
end PELOriginalCM210SmallIdealNonprincipal318
