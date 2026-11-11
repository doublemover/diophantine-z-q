module
public import Mathlib.AlgebraicGeometry.StructureSheaf
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.RingTheory.Localization.Away.Basic
public import LineFrameTopScalar318
public import OriginalOpenCoefficientSpecialization318
public section
noncomputable section
namespace AffineOpenRegularFraction318
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable (R : Type) [CommRing R]

/-- Every actual affine structure-sheaf section has a fixed rational
expression on a genuine principal neighborhood of the chosen prime. -/
theorem exists_equation (U : (Spec (CommRingCat.of R)).Opens) (s : Γ(Spec (CommRingCat.of R),U))
    (x : PrimeSpectrum R) (hx : x∈U) :
    ∃ b : R, ∃ hb : PrimeSpectrum.basicOpen b ≤ U, x∈PrimeSpectrum.basicOpen b ∧
      ∃ n : ℕ, ∃ a : R,
        (Spec (CommRingCat.of R)).presheaf.map (homOfLE hb).op s *
          algebraMap R Γ(Spec (CommRingCat.of R),PrimeSpectrum.basicOpen b) b ^ n=
        algebraMap R Γ(Spec (CommRingCat.of R),PrimeSpectrum.basicOpen b) a := by
  obtain ⟨_,⟨_,⟨b,rfl⟩,rfl⟩,hxb,hb : PrimeSpectrum.basicOpen _ ≤ U⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hx U.isOpen
  obtain ⟨n,a,he⟩ := IsLocalization.Away.surj b
    ((Spec (CommRingCat.of R)).presheaf.map (homOfLE hb).op s)
  exact ⟨b,hb,hxb,n,a,he⟩

/-- Exact pullback of a ring coefficient through an actual point of an
arbitrary affine open. The original section/scalar maps are explicit. -/
lemma coefficient_value (U : (Spec (CommRingCat.of R)).Opens)
    (p : Spec (CommRingCat.of ℂ) ⟶ U.toScheme) (f : R →+* ℂ)
    (hp : p≫U.ι=Spec.map (CommRingCat.ofHom f)) (a : R) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop
      ((LineFrameTopScalar318.ringTop U).inv (algebraMap R Γ(Spec (CommRingCat.of R),U) a)))=f a := by
  have hs : (LineFrameTopScalar318.ringTop U).inv
      (algebraMap R Γ(Spec (CommRingCat.of R),U) a)=
      U.ι.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a) := by
    rw [Scheme.Opens.ι_appTop]
    change (Spec (CommRingCat.of R)).presheaf.map _
      ((Spec (CommRingCat.of R)).presheaf.map _ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a))=_
    rw [←Functor.map_comp]
    rfl
  rw [hs]
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
    ((p≫U.ι).appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a))=_
  rw [hp]
  have h := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a)
  simpa only [Iso.inv_hom_id_apply] using h

/-- Specialize an actual local fraction through ANY genuine point
preserving the specified ring evaluation. No choice of a residue-field
identification or continuity of a gauge enters this identity. -/
lemma equation_value (U : (Spec (CommRingCat.of R)).Opens)
    (s : Γ(Spec (CommRingCat.of R),U)) (b a : R) (n : ℕ)
    (hb : PrimeSpectrum.basicOpen b ≤ U)
    (he : (Spec (CommRingCat.of R)).presheaf.map (homOfLE hb).op s *
        algebraMap R Γ(Spec (CommRingCat.of R),PrimeSpectrum.basicOpen b) b^n=
      algebraMap R Γ(Spec (CommRingCat.of R),PrimeSpectrum.basicOpen b) a)
    (p : Spec (CommRingCat.of ℂ) ⟶ (PrimeSpectrum.basicOpen b).toScheme)
    (f : R →+* ℂ) (hp : p≫(PrimeSpectrum.basicOpen b).ι=Spec.map (CommRingCat.ofHom f))
    (hfb : f b≠0) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      ((p≫(Spec (CommRingCat.of R)).homOfLE hb).appTop
        ((LineFrameTopScalar318.ringTop U).inv s))=f a/(f b)^n := by
  let ev : Γ(Spec (CommRingCat.of R),PrimeSpectrum.basicOpen b) →+* ℂ :=
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp p.appTop.hom).comp
      (LineFrameTopScalar318.ringTop (PrimeSpectrum.basicOpen b)).inv.hom
  have h := congrArg ev he
  simp only [map_mul,map_pow] at h
  have ha := coefficient_value R (PrimeSpectrum.basicOpen b) p f hp a
  have hbb := coefficient_value R (PrimeSpectrum.basicOpen b) p f hp b
  change ev ((Spec (CommRingCat.of R)).presheaf.map (homOfLE hb).op s) *
      ev (algebraMap R Γ(Spec (CommRingCat.of R),PrimeSpectrum.basicOpen b) b)^n=
    ev (algebraMap R Γ(Spec (CommRingCat.of R),PrimeSpectrum.basicOpen b) a) at h
  rw [hbb,ha] at h
  apply (eq_div_iff (pow_ne_zero n hfb)).mpr
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop
      (((Spec (CommRingCat.of R)).homOfLE hb).appTop
        ((LineFrameTopScalar318.ringTop U).inv s))) * (f b)^n=f a
  have hr := OriginalOpenCoefficientSpecialization318.coefficient_pullback U
    (PrimeSpectrum.basicOpen b) hb ((LineFrameTopScalar318.ringTop U).inv s)
  simp only [GlobalSectionFrameCoordinates318.coefficient,Iso.inv_hom_id_apply] at hr
  rw [←hr]
  exact h
end AffineOpenRegularFraction318
