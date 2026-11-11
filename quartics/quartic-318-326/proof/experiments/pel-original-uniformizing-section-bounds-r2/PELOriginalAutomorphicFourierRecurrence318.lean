module
public import EntireDoubleFourierTranslation318
public import PELOriginalLevelTheta318
public section
noncomputable section
namespace PELOriginalAutomorphicFourierRecurrence318
open QuaternionicRealPeriod318 PELOriginalThetaConvergence318
open PELOriginalThetaQuasiperiods318 PELOriginalLevelTheta318
open EntireDoubleFourierTranslation318 EntirePeriodicDoubleIntegral318
variable (τ:ℂ) (N:ℕ)

/-- The FULL space of entire functions with the original normalized
level-N automorphy, not the span of preselected characteristic functions. -/
structure Automorphic (f:ComplexVectors→ℂ):Prop where
  entire:Differentiable ℂ f
  integer:∀m:Index,∀z,f (z+integerVector m)=f z
  period:∀b:Index,∀z,f (z+periodVector τ b)=multiplier τ b z^N*f z
lemma first_period {f:ComplexVectors→ℂ}(h:Automorphic τ N f)(x y:ℂ):
    f ![x+1,y]=f ![x,y]:=by
  have he:![x,y]+integerVector (1,0)=![x+1,y]:=by
    ext i;fin_cases i <;> simp [integerVector]
  simpa only [he] using h.integer (1,0) ![x,y]
lemma second_period {f:ComplexVectors→ℂ}(h:Automorphic τ N f)(x y:ℂ):
    f ![x,y+1]=f ![x,y]:=by
  have he:![x,y]+integerVector (0,1)=![x,y+1]:=by
    ext i;fin_cases i <;> simp [integerVector]
  simpa only [he] using h.integer (0,1) ![x,y]
@[expose] def periodConstant(b:Index):ℂ:=
  Complex.exp (-((N:ℂ)*(Real.pi:ℂ)*Complex.I*quadratic τ b))
lemma multiplier_weight(b k:Index)(z:ComplexVectors):
    multiplier τ b z^N*weight k z=
      periodConstant τ N b*weight (k+shift N b) z:=by
  simp only [multiplier,weight,periodConstant,←Complex.exp_nat_mul,←Complex.exp_add]
  congr 1
  simp only [linear,shift,Prod.fst_add,Prod.snd_add]
  push_cast
  ring
lemma coefficient_period {f:ComplexVectors→ℂ}(h:Automorphic τ N f)(b k:Index):
    coefficient (translate f (periodVector τ b)) k=
      periodConstant τ N b*coefficient f (k+shift N b):=by
  have he:weighted (translate f (periodVector τ b)) k=
      fun z=>periodConstant τ N b*weighted f (k+shift N b) z:=by
    funext z
    simp only [weighted,translate,h.period]
    calc
      multiplier τ b z^N*f z*weight k z=
          f z*(multiplier τ b z^N*weight k z):=by ring
      _=periodConstant τ N b*(f z*weight (k+shift N b) z):=by
        rw [multiplier_weight]
        ring
  change periodIntegral (weighted (translate f (periodVector τ b)) k) 0=_
  rw [he,periodIntegral_mul]
  rfl

/-- Genuine Fourier recurrence for EVERY entire level-N automorphic
function. Both sides concern actual horizontal period integrals; it is
not inferred only for the constructed theta basis. -/
theorem full_recurrence {f:ComplexVectors→ℂ}(h:Automorphic τ N f)(b k:Index):
    periodConstant τ N b*coefficient f (k+shift N b)=
      character k (periodVector τ b)*coefficient f k:=by
  rw [←coefficient_period τ N h b k]
  exact coefficient_translation f h.entire (first_period τ N h)
    (second_period τ N h) k (periodVector τ b)

/-- The known characteristic functions are elements of the FULL space;
this direction is distinct from the spanning theorem to follow. -/
lemma characteristic_automorphic(hτ:0<τ.im)[NeZero N](r:Label N):
    Automorphic τ N (levelTheta τ N r):=
  ⟨holomorphic τ hτ N r,theta_integer τ N r,theta_period τ N r⟩
end PELOriginalAutomorphicFourierRecurrence318
