module
public import PELOriginalSiegelMatrix318
public section
noncomputable section
namespace PELOriginalSiegelNormalization318
open QuaternionicRealPeriod318 QuaternionicOrderPeriodQuotient318
open PELQuaternionRealRepresentation318 PELPrincipalOrderCoordinates318
open PELOriginalSymplecticCoordinates318 PELOriginalSiegelMatrix318
open PELPeriodRiemannForm318 PELOriginalPolarizationAutomorphy318
open PELOriginalHermitianForm318 PELOriginalPolarizationSemicharacter318
variable (τ:ℂ) (hτ:0<τ.im)
lemma parameter_ne (hτ:0<τ.im):τ≠0:=by intro h;simpa [h] using hτ
lemma beta_complex_ne:(beta:ℂ)≠0:=by exact_mod_cast beta_pos.ne'
lemma beta_complex_sq:(beta:ℂ)^2=5:=by exact_mod_cast beta_sq

/-- Inverse of the actual a-period matrix [period(e0),period(e2)].
Its determinant is -sqrt5*τ, nonzero on the original upper half-plane. -/
@[expose] def normalize (z:ComplexVectors):ComplexVectors:=
  ![z 1-(1-(beta:ℂ))/2*((z 0/τ-z 1)/(beta:ℂ)),(z 0/τ-z 1)/(beta:ℂ)]
@[expose] def denormalize (z:ComplexVectors):ComplexVectors:=
  ![τ*(z 0+(1+(beta:ℂ))/2*z 1),z 0+(1-(beta:ℂ))/2*z 1]
lemma denormalize_normalize (hτ:0<τ.im) (z:ComplexVectors):denormalize τ (normalize τ z)=z:=by
  ext i
  fin_cases i <;> simp [normalize,denormalize] <;>
    field_simp [parameter_ne τ hτ,beta_complex_ne] <;> ring
lemma normalize_denormalize (hτ:0<τ.im) (z:ComplexVectors):normalize τ (denormalize τ z)=z:=by
  ext i
  fin_cases i <;> simp [normalize,denormalize] <;>
    field_simp [parameter_ne τ hτ,beta_complex_ne] <;> ring
@[expose] def normalization (hτ:0<τ.im):ComplexVectors≃ₗ[ℂ]ComplexVectors where
  toFun:=normalize τ
  invFun:=denormalize τ
  left_inv:=denormalize_normalize τ hτ
  right_inv:=normalize_denormalize τ hτ
  map_add':=by intro z w;ext i;fin_cases i <;> simp [normalize] <;> ring
  map_smul':=by intro a z;ext i;fin_cases i <;> simp [normalize] <;> ring

@[expose] def standardPeriod (p:Pair):ComplexVectors:=fun j=>
  (p.1 j:ℂ)+omega τ j 0*(p.2 0:ℂ)+omega τ j 1*(p.2 1:ℂ)
/-- Exact original period coordinates, not equality of rank or covolume.
All four original integral-order generators map to Z²+Omega Z². -/
lemma original_period (p:Pair):
    normalization τ hτ (periodHom representation τ (embed (fromPair p)))=standardPeriod τ p:=by
  ext i
  fin_cases i <;>
    simp [normalization,normalize,standardPeriod,omega,periodHom,period,row,
      representation,matrix,embed,fromPair] <;>
    push_cast <;> field_simp [parameter_ne τ hτ,beta_complex_ne] <;>
    ring_nf <;> simp only [beta_complex_sq] <;> ring

lemma full_original_periods (z:ComplexVectors):
    z∈periodSubgroup representation order τ↔
      ∃p:Pair,normalization τ hτ z=standardPeriod τ p:=by
  constructor
  · rintro ⟨x,⟨a,rfl⟩,rfl⟩
    refine ⟨coordinates a,?_⟩
    simpa only [show fromPair (coordinates a)=a from from_to a] using
      original_period τ hτ (coordinates a)
  · rintro ⟨p,hp⟩
    have hz:z=periodHom representation τ (embed (fromPair p)):=
      (normalization τ hτ).injective (hp.trans (original_period τ hτ p).symm)
    rw [hz]
    exact ⟨embed (fromPair p),⟨fromPair p,rfl⟩,rfl⟩

@[expose] def normalizedHermitian (z w:ComplexVectors):ℂ:=
  form τ hτ ((normalization τ hτ).symm z) ((normalization τ hτ).symm w)
@[expose] def normalizedFactor (p:Pair) (z:ComplexVectors):ℂ:=
  factor τ hτ (latticeEquiv τ hτ (fromPair p)) ((normalization τ hτ).symm z)
lemma denormalized_period (p:Pair):
    (normalization τ hτ).symm (standardPeriod τ p)=
      (latticeEquiv τ hτ (fromPair p):ComplexVectors):=by
  have h:=congrArg (normalization τ hτ).symm (original_period τ hτ p)
  simpa only [LinearEquiv.symm_apply_apply] using h.symm
/-- Canonical theta factor expression for the SAME previously produced
line bundle. The only change is the genuine complex coordinate equivalence;
the original phase is exactly equal, not replaced up to an unspecified twist. -/
lemma normalized_factor_formula (p:Pair) (z:ComplexVectors):
    normalizedFactor τ hτ p z=
      Complex.exp ((Real.pi:ℂ)*(normalizedHermitian τ hτ z (standardPeriod τ p)+
        normalizedHermitian τ hτ (standardPeriod τ p) (standardPeriod τ p)/2))*
      Complex.exp ((Real.pi:ℂ)*Complex.I*(canonicalQuadratic p:ℂ)):=by
  have hphase:=same_phase (fromPair p)
  have hcoords:coordinates (fromPair p)=p:=to_from p
  rw [hcoords] at hphase
  simp only [normalizedFactor,factor,exponent,LinearEquiv.symm_apply_apply,Complex.exp_add]
  rw [show Complex.exp ((Real.pi:ℂ)*Complex.I*(quadratic (fromPair p):ℂ))=
    Complex.exp ((Real.pi:ℂ)*Complex.I*(canonicalQuadratic p:ℂ)) from hphase.symm]
  simp only [normalizedHermitian,denormalized_period]
end PELOriginalSiegelNormalization318
