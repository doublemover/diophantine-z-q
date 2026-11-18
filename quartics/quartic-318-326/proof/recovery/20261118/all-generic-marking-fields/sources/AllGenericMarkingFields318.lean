module
public import GenericMarkingOrbitField318
public import FiniteGeometricTorsionField318
public section
noncomputable section
namespace AllGenericMarkingFields318
open WeierstrassCurve.Affine PrimitiveDiamond318
open TranscendentalJGenericFiber318 GenericPrimitiveFiberBound318
open GenericMarkingOrbitField318
variable (N:ℕ) [NeZero N]
local instance : Algebra (K N) ℂ := (embedding N τ h ht).toAlgebra
local instance : CharZero (K N) := (embedding N τ h ht).charZero
abbrev T := FiniteGeometricTorsionField318.Points (Ω:=ℂ) (W N) N

/-- Every literal primitive analytic period label parametrizes an
actual mark on the arithmetic generic curve after the fixed embedding. -/
def periodLabels : Points N ≃ T N := by
  have he := congrArg WeierstrassCurve.toAffine (actual_curve N τ h ht)
  change (Points N ≃ {P:(((OpenJModel318.integralModel N).map
    (algebraMap _ (K N))).map (embedding N τ h ht)).toAffine.Point // addOrderOf P=N})
  rw [he]
  exact OpenJAnalyticPoints318.primitiveEquiv N τ h N

/-- One common finite Galois field realizes all analytic markings with
their actual coordinates. For each choice of H and each label the field
of moduli is the literal stabilizer field and satisfies the degree bound. -/
theorem simultaneous : ∃L:IntermediateField (K N) ℂ,
    ∃ (hd:FiniteDimensional (K N) L) (hg:IsGalois (K N) L),
    letI := hd; letI := hg
    ∀x:Points N, ∃ P:A N L, ∃hP:addOrderOf P=N,
      Point.map (W':=W N) L.val P=(periodLabels N x).val ∧
      ∀ H:Subgroup (ZMod N)ˣ, Module.finrank (K N)
        (orbitField N L P hP H)≤(GammaHGroup318.gammaH N H).index := by
  letI : Finite (T N) := Finite.of_equiv _ (periodLabels N)
  obtain ⟨L,hd,hg,hall⟩ := FiniteGeometricTorsionField318.exists_field (Ω:=ℂ) (W N) N
  refine ⟨L,hd,hg,?_⟩
  letI := hd;letI := hg
  intro x
  obtain ⟨P,hP,he⟩ := hall (periodLabels N x)
  exact ⟨P,hP,he,fun H=>GenericMarkingOrbitField318.degree N L P hP H⟩

end AllGenericMarkingFields318
