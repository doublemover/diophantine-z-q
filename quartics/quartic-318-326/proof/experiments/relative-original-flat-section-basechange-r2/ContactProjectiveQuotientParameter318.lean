module
public import ContactQuotientTripleRotation318
public section
noncomputable section
namespace ContactProjectiveQuotientParameter318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactQuotientChart318 ContactQuotientOverlapOpen318
variable (c : Fin 4 → ℚˣ) (n : ℕ)
/-- Actual gluing data for the original projective-source quotient
parameter charts. Every triple arrow is on the categorical pullback. -/
@[expose] def data : Scheme.GlueData where
  J := Chart
  U a := VaryingWordChartGluing318.scheme ℚ (ring c a) (Fin n)
  V ab := ContactQuotientOverlapSchemeRule318.scheme c ab.1 ab.2 n
  f a b := (parameterOpen c a b n).ι
  f_id a := ContactQuotientOverlapSelf318.inclusion_iso c a n
  t a b := (ContactQuotientOverlapSchemeIso318.iso c a b n).hom
  t_id a := ContactQuotientOverlapSelf318.transition_identity c a n
  t' := ContactQuotientTripleRotation318.rotation c · · · n
  t_fac := ContactQuotientTripleRotation318.leg c · · · n
  cocycle := ContactQuotientTripleRotation318.cycle c · · · n
  f_open a b := inferInstance
/-- The ACTUAL glued parameter scheme, on the SAME original projective
source charts. Its full universal-family descent/classification is next. -/
abbrev scheme : Scheme := (data c n).glued
abbrev into (a : Chart) : VaryingWordChartGluing318.scheme ℚ (ring c a) (Fin n) ⟶ scheme c n :=
  (data c n).ι a
instance into_open (a : Chart) : IsOpenImmersion (into c n a) := inferInstance
abbrev cover : (scheme c n).OpenCover := (data c n).openCover
lemma jointly_surjective (x : scheme c n) : ∃ a y,into c n a y=x := (data c n).ι_jointly_surjective x
@[reassoc] lemma glue_condition (a b : Chart) :
    (ContactQuotientOverlapSchemeIso318.iso c a b n).hom ≫ (parameterOpen c b a n).ι ≫ into c n b=
      (parameterOpen c a b n).ι ≫ into c n a := (data c n).glue_condition a b
end ContactProjectiveQuotientParameter318
