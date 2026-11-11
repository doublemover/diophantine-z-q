module
public import ComplexProjectiveMarkerPoint318
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public section
noncomputable section
namespace HomogeneousQuotientChart318
open ComplexProjectiveMarkerPoint318 HomogeneousLocalization
variable {ι:Type*}
local instance standardGrading:GradedAlgebra (grading (ι:=ι)):=MvPolynomial.gradedAlgebra
variable (I:Ideal (Equations (ι:=ι)))(j:ι)
abbrev Chart:=HomogeneousLocalization.Away grading (MvPolynomial.X j)
abbrev QuotientRing:=Equations (ι:=ι)⧸I
abbrev LocalizedQuotient:=Localization.Away (Ideal.Quotient.mk I (MvPolynomial.X j))

/-- Actual homogeneous chart maps into the localization of the LITERAL
polynomial quotient. This keeps the original coordinate X_j, not a
chosen section or an abstract fraction field. -/
@[expose] def quotientMap:Chart j→+*LocalizedQuotient I j:=
  (Localization.awayMap (Ideal.Quotient.mk I) (MvPolynomial.X j)).comp
    (algebraMap (Chart j) (Localization.Away (MvPolynomial.X j)))
@[expose] def fraction(n:ℕ)(p:Equations (ι:=ι))(hp:p.IsHomogeneous n):Chart j:=
  HomogeneousLocalization.Away.mk grading (MvPolynomial.isHomogeneous_X ℂ j) n p
    (by simpa only [smul_eq_mul,mul_one] using hp)
lemma fraction_value(n:ℕ)(p:Equations (ι:=ι))(hp:p.IsHomogeneous n):
    quotientMap I j (fraction j n p hp)=
      IsLocalization.mk' (LocalizedQuotient I j) (Ideal.Quotient.mk I p)
        ⟨Ideal.Quotient.mk I (MvPolynomial.X j)^n,⟨n,rfl⟩⟩:=by
  simp only [quotientMap,RingHom.comp_apply,HomogeneousLocalization.algebraMap_apply,
    fraction,HomogeneousLocalization.Away.val_mk,Localization.mk_eq_mk',
    Localization.awayMap,IsLocalization.Away.map,IsLocalization.map_mk',map_pow]

/-- The degree-zero quotient localization is the actual subring of
(A/I)[1/X_j] consisting of fractions with homogeneous numerator and
matching denominator degree. The following normal form proves that
this is the entire such degree-zero ring, not a selected smaller ring. -/
@[expose] def degreeZero:Subring (LocalizedQuotient I j):=(quotientMap I j).range
lemma degreeZero_normal_form(z:degreeZero I j):
    ∃n p (hp:p.IsHomogeneous n),
      z.val=IsLocalization.mk' (LocalizedQuotient I j) (Ideal.Quotient.mk I p)
        ⟨Ideal.Quotient.mk I (MvPolynomial.X j)^n,⟨n,rfl⟩⟩:=by
  obtain ⟨a,ha⟩:=z.property
  obtain ⟨n,p,hp,hpa⟩:=HomogeneousLocalization.Away.mk_surjective grading
    (MvPolynomial.isHomogeneous_X ℂ j) a
  have hp':p.IsHomogeneous n:=by simpa only [smul_eq_mul,mul_one] using hp
  refine ⟨n,p,hp',?_⟩
  rw [←ha,←hpa]
  exact fraction_value I j n p hp'
lemma fraction_mem_degreeZero(n:ℕ)(p:Equations (ι:=ι))(hp:p.IsHomogeneous n):
    IsLocalization.mk' (LocalizedQuotient I j) (Ideal.Quotient.mk I p)
      ⟨Ideal.Quotient.mk I (MvPolynomial.X j)^n,⟨n,rfl⟩⟩∈degreeZero I j:=
  ⟨fraction j n p hp,fraction_value I j n p hp⟩

/-- Exact torsion-sensitive zero criterion. Clearing denominators retains
an actual power of X_j; no unjustified cancellation modulo I occurs. -/
lemma fraction_zero_iff(n:ℕ)(p:Equations (ι:=ι))(hp:p.IsHomogeneous n):
    quotientMap I j (fraction j n p hp)=0↔
      ∃k:ℕ,(MvPolynomial.X j)^k*p∈I:=by
  rw [fraction_value,IsLocalization.mk'_eq_zero_iff]
  constructor
  · rintro ⟨⟨m,⟨k,rfl⟩⟩,hk⟩
    refine ⟨k,Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
    simpa only [map_mul,map_pow] using hk
  · rintro ⟨k,hk⟩
    refine ⟨⟨Ideal.Quotient.mk I (MvPolynomial.X j)^k,⟨k,rfl⟩⟩,?_⟩
    simpa only [map_mul,map_pow] using (Ideal.Quotient.eq_zero_iff_mem.mpr hk)

@[expose] def chartQuotientEquiv:
    (Chart j⧸RingHom.ker (quotientMap I j))≃+*degreeZero I j:=
  RingHom.quotientKerEquivRange (quotientMap I j)
lemma kernel_radical(hI:I.IsRadical):(RingHom.ker (quotientMap I j)).IsRadical:=by
  haveI:I.IsRadical:=hI
  haveI:IsReduced (QuotientRing I):=inferInstance
  haveI:IsReduced (LocalizedQuotient I j):=inferInstance
  rw [RingHom.ker_eq_comap_bot]
  exact Ideal.isRadical_bot.comap _
end HomogeneousQuotientChart318
