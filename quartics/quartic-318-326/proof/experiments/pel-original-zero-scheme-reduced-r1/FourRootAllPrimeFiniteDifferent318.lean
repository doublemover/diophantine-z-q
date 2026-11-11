module
public import FourRootAllPrimeRelativeDifferent318
public import FourRootDerivativeFiniteIdeal318
public import FourRootActualFrameDenominatorCover318
public import Mathlib.RingTheory.LocalProperties.Basic
public section
noncomputable section
namespace FourRootAllPrimeFiniteDifferent318
open FourRootActualFiniteBranchChart318 FourRootActualFractionField318
open FourRootDerivativeZeroIdeals318
variable (b:Fin 4→ℂ)(hb:Function.Injective b)
local instance polyAlgebra:Algebra ℂ[X] (A b):=
  (Polynomial.aeval (FourRootAffineCoordinateRing318.coordinate b none)).toAlgebra
local instance affineDedekind:IsDedekindDomain (A b):=FourRootActualDedekind318.finite_dedekind b hb
local instance affineFinite:Module.Finite ℂ[X] (A b):=(FourRootActualOrderGalois318.finite_free b).1
local instance affineFree:Module.Free ℂ[X] (A b):=(FourRootActualOrderGalois318.finite_free b).2
abbrev Stalk(p:Ideal (A b))[p.IsPrime]:=Localization.AtPrime p
lemma ideal_unit_at(p:Ideal (A b))[p.IsPrime](J:Ideal (A b))(h:¬p∣J):
    J.map (algebraMap (A b) (Stalk b p))=⊤:=by
  have hn:¬J≤p:=by simpa only [Ideal.dvd_iff_le] using h
  obtain ⟨x,hx,hxp⟩:=SetLike.not_le_iff_exists.mp hn
  apply Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hx)
  exact IsLocalization.map_units (Stalk b p) ⟨x,hxp⟩
/-- Same trace-tower computation at EVERY affine prime in the genuine
principal chart. No closed-point realization or Nullstellensatz premise. -/
theorem local_trace(p:Ideal (A b))[p.IsPrime](i:Fin 4)(hp:denominator b i∉p):
    (differentIdeal ℂ[X] (A b)).map (algebraMap (A b) (Stalk b p))=
      Ideal.span {algebraMap (A b) (Stalk b p) (FourRootAffineCoordinateRing318.coordinate b (some i))}:=by
  letI:Algebra (BranchBase b i) (A b):=(FourRootActualDifferentTower318.branchMap b i).toAlgebra
  letI:IsDedekindDomain (BranchBase b i):=ActualLinearRootDifferent318.dedekind (b i)
  letI:Module.Free (BranchBase b i) (A b):=(FourRootActualDifferentTower318.relative_finite_free b i).2
  have hu:=ideal_unit_at b p (differentIdeal (BranchBase b i) (A b))
    (FourRootAllPrimeRelativeDifferent318.relative_trace_unit b hb i p hp)
  rw [FourRootActualDifferentTower318.actual_factorization b hb i,Ideal.map_mul,hu,
    Ideal.top_mul,Ideal.map_span]
  simp only [Set.image_singleton,map_mul,map_ofNat]
  have h2:IsUnit (2:Stalk b p):=by
    simpa only [map_ofNat] using (IsUnit.mk0 (2:ℂ) (by norm_num)).map (algebraMap ℂ (Stalk b p))
  rw [Ideal.span_singleton_mul_left_unit h2]
lemma local_zero_ideal(p:Ideal (A b))[p.IsPrime](i:Fin 4)(hp:denominator b i∉p):
    (finiteIdeal b).map (algebraMap (A b) (Stalk b p))=
      Ideal.span {algebraMap (A b) (Stalk b p) (FourRootAffineCoordinateRing318.coordinate b (some i))}:=by
  let f:FourRootActualBranchKaehler318.SourceRing b i→+*Stalk b p:=
    IsLocalization.Away.lift (denominator b i)
      (IsLocalization.map_units (Stalk b p) ⟨denominator b i,hp⟩)
  have hf:f.comp (algebraMap (A b) (FourRootActualBranchKaehler318.SourceRing b i))=
      algebraMap (A b) (Stalk b p):=by
    ext x
    exact IsLocalization.Away.lift_eq _ _ x
  have h:=congrArg (Ideal.map f) (FourRootDerivativeFiniteIdeal318.localized_ideal b i)
  rw [Ideal.map_map,hf,Ideal.map_span,Set.image_singleton,
    FourRootActualBranchKaehler318.source_coordinate_original] at h
  simpa only [←RingHom.comp_apply,hf] using h
/-- Equality of WHOLE actual affine ideals, not just supports or complex
point multiplicities. Every maximal prime is covered by a genuine root
chart and the exact localized ideal equality detects the original ideal. -/
theorem trace_equals_zero_ideal:differentIdeal ℂ[X] (A b)=finiteIdeal b:=by
  apply Ideal.eq_of_localization_maximal
  intro p hp
  letI:p.IsMaximal:=hp
  obtain ⟨i,hi⟩:=FourRootActualFrameDenominatorCover318.finite_cover b hb ⟨p,inferInstance⟩
  exact (local_trace b hb p i hi).trans (local_zero_ideal b p i hi).symm
end FourRootAllPrimeFiniteDifferent318
