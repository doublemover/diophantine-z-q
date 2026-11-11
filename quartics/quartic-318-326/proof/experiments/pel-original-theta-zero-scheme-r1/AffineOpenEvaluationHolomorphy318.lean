module
public import AffineOpenRegularFraction318
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public section
noncomputable section
namespace AffineOpenEvaluationHolomorphy318
open AlgebraicGeometry CategoryTheory Filter Set Topology
variable {R : Type} [CommRing R]

lemma basic_nonzero (f : R →+* ℂ) (b : R) :
    Spec.map (CommRingCat.ofHom f) (IsLocalRing.closedPoint ℂ)∈PrimeSpectrum.basicOpen b ↔ f b≠0 := by
  change (f b ∉ IsLocalRing.maximalIdeal ℂ) ↔ _
  rw [IsLocalRing.maximalIdeal_eq_bot]
  rfl

lemma exists_point (f : R →+* ℂ) (U : (Spec (CommRingCat.of R)).Opens)
    (h : Spec.map (CommRingCat.ofHom f) (IsLocalRing.closedPoint ℂ)∈U) :
    ∃ p : Spec (CommRingCat.of ℂ) ⟶ U.toScheme,p≫U.ι=Spec.map (CommRingCat.ofHom f) := by
  have hr : Set.range (Spec.map (CommRingCat.ofHom f)) ⊆ Set.range U.ι := by
    rintro _ ⟨x,rfl⟩
    have hx : x=IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
    subst x
    exact ⟨⟨_,h⟩,rfl⟩
  exact ⟨IsOpenImmersion.lift U.ι _ hr,IsOpenImmersion.lift_fac _ _ hr⟩

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Every regular function on an ARBITRARY affine open specializes
holomorphically in any holomorphic family of whole-ring evaluations.
Its local rational expression is produced from the actual structure
sheaf; no analytification or assumed local fraction is an input. -/
theorem differentiableAt (F : E → R →+* ℂ) (z : E)
    (hF : ∀ a : R,DifferentiableAt ℂ (fun w => F w a) z)
    (U : (Spec (CommRingCat.of R)).Opens) (s : Γ(Spec (CommRingCat.of R),U))
    (hz : Spec.map (CommRingCat.ofHom (F z)) (IsLocalRing.closedPoint ℂ)∈U)
    (G : E → ℂ)
    (hG : ∀ᶠ w in 𝓝 z, ∀ (p : Spec (CommRingCat.of ℂ) ⟶ U.toScheme),
      p≫U.ι=Spec.map (CommRingCat.ofHom (F w)) →
        G w=(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
          (p.appTop ((LineFrameTopScalar318.ringTop U).inv s))) :
    DifferentiableAt ℂ G z := by
  obtain ⟨b,hb,hzb,n,a,he⟩ := AffineOpenRegularFraction318.exists_equation R U s _ hz
  have hfb : F z b≠0 := (basic_nonzero (F z) b).mp hzb
  apply ((hF a).div ((hF b).pow n) (pow_ne_zero n hfb)).congr_of_eventuallyEq
  filter_upwards [(hF b).continuousAt.eventually_ne hfb,hG] with w hw hGw
  obtain ⟨p,hp⟩ := exists_point (F w) (PrimeSpectrum.basicOpen b) ((basic_nonzero (F w) b).mpr hw)
  rw [hGw (p≫(Spec (CommRingCat.of R)).homOfLE hb) (by
    simpa only [Category.assoc,Scheme.homOfLE_ι] using hp)]
  exact AffineOpenRegularFraction318.equation_value R U s b a n hb he p (F w) hp hw

/-- Local continuity of every ring evaluation already suffices for a
neighborhood lying in the arbitrary affine Zariski open. -/
theorem eventually_mem (F : E → R →+* ℂ) (z : E)
    (hF : ∀ a : R,ContinuousAt (fun w => F w a) z)
    (U : (Spec (CommRingCat.of R)).Opens)
    (hz : Spec.map (CommRingCat.ofHom (F z)) (IsLocalRing.closedPoint ℂ)∈U) :
    ∀ᶠ w in 𝓝 z,Spec.map (CommRingCat.ofHom (F w)) (IsLocalRing.closedPoint ℂ)∈U := by
  obtain ⟨_,⟨_,⟨b,rfl⟩,rfl⟩,hzb,hb : PrimeSpectrum.basicOpen _ ≤ U⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hz U.isOpen
  have hfb := (basic_nonzero (F z) b).mp hzb
  filter_upwards [(hF b).eventually_ne hfb] with w hw
  exact hb ((basic_nonzero (F w) b).mpr hw)

/-- The same local fraction neighborhood proves the inverse image of
EVERY affine Zariski open is analytically open in the evaluation family. -/
theorem isOpen_preimage (F : E → R →+* ℂ) (hF : ∀ a : R,Continuous (fun w => F w a))
    (U : (Spec (CommRingCat.of R)).Opens) :
    IsOpen {z | Spec.map (CommRingCat.ofHom (F z)) (IsLocalRing.closedPoint ℂ)∈U} := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  obtain ⟨_,⟨_,⟨b,rfl⟩,rfl⟩,hzb,hb : PrimeSpectrum.basicOpen _ ≤ U⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hz U.isOpen
  have hfb := (basic_nonzero (F z) b).mp hzb
  filter_upwards [(hF b).continuousAt.eventually_ne hfb] with w hw
  exact hb ((basic_nonzero (F w) b).mpr hw)
end AffineOpenEvaluationHolomorphy318
