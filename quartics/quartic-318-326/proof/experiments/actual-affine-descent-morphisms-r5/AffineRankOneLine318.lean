module
public import LineSheafClass318
public import FiniteTargetSheafFrame318
public section
noncomputable section
namespace AffineRankOneLine318
open AlgebraicGeometry CategoryTheory LineSheafClass318 TopologicalSpace
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : CommRingCat.{u}) (M : ModuleCat R)
  [Module.FinitePresentation R M] [Module.Flat R M]
  (rk : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = 1)

abbrev basic (a : R) : (Spec R).Opens := PrimeSpectrum.basicOpen a

include rk in
/-- Finite-flat rank one gives actual unit-sheaf frames on principal opens
covering every point of the actual affine scheme. The original tilde unit
identifies the modules used by the prior principal-frame construction. -/
lemma exists_frame (p : PrimeSpectrum R) : ∃ a : R,
    p ∈ PrimeSpectrum.basicOpen a ∧ Nonempty
      (SheafOfModules.unit (basic R a).toScheme.ringCatSheaf ≅
        (tilde M).restrict (basic R a).ι) := by
  let e : M ≃ₗ[R] moduleSpecΓFunctor.obj (tilde M) := (tilde.isoTop M).toLinearEquiv
  let : Module.FinitePresentation R (moduleSpecΓFunctor.obj (tilde M)) :=
    Module.FinitePresentation.of_equiv e
  let : Module.Flat R (moduleSpecΓFunctor.obj (tilde M)) :=
    Module.Flat.of_linearEquiv e.symm
  have hr : ∀ q : PrimeSpectrum R,
      Module.rankAtStalk (moduleSpecΓFunctor.obj (tilde M)) q = 1 := by
    intro q
    exact (congrFun (Module.rankAtStalk_eq_of_equiv e.symm) q).trans (rk q)
  simpa using FiniteTargetSheafFrame318.exists_frame R R (tilde M) hr p

@[expose] def basicElement (p : PrimeSpectrum R) : R := (exists_frame R M rk p).choose
lemma basicElement_mem (p : PrimeSpectrum R) :
    p ∈ PrimeSpectrum.basicOpen (basicElement R M rk p) :=
  (exists_frame R M rk p).choose_spec.1

/-- The descended sheaf is literally tilde of the original module. Only
its full principal-open frame presentation is chosen. -/
@[expose] def line : Line (Spec R) where
  object := tilde M
  Index := PrimeSpectrum R
  opens p := PrimeSpectrum.basicOpen (basicElement R M rk p)
  cover := by
    intro p _
    exact Opens.mem_iSup.mpr ⟨p, basicElement_mem R M rk p⟩
  frame p := (exists_frame R M rk p).choose_spec.2.some

lemma line_object : (line R M rk).object = tilde M := rfl
end AffineRankOneLine318
