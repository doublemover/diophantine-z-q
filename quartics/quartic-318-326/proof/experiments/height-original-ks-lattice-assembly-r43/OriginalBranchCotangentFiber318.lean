module
public import IntegralBranchCotangentFiber318
public import ContactFiniteCoefficientIdentity318
public section
noncomputable section
namespace OriginalBranchCotangentFiber318
open Polynomial ContactBicanonicalCoefficients318 OriginalPointFinitePlaceRoots318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ) (t : ℚ)
  (hn : ∀ j, RationalContactPoint318.parameters c t j≠0) (i : Fin 4)
local instance evaluationAlgebra : Algebra (BranchRing c i) (K c t) :=
  (ContactBranchPoint318.branchPoint c t hn i).toAlgebra
abbrev Fiber := FramedCotangentFiber318.Fiber ℚ (BranchRing c i) (K c t)
@[expose] def frame : Fiber c t hn i ≃ₗ[K c t] K c t :=
  FramedCotangentFiber318.frame ℚ (BranchRing c i) (K c t)
    (ContactDifferentialFrames318.sourceLocalizationFrame c i)
@[expose] def dt : Fiber c t hn i :=
  FramedCotangentFiber318.differential ℚ (BranchRing c i) (K c t) (branchT c i)
@[expose] def coordinate : Fiber c t hn i :=
  FramedCotangentFiber318.differential ℚ (BranchRing c i) (K c t)
    (ContactFrameNormalization318.sourceCoordinate c i)
@[expose] def quarticValue : K c t :=
  ((Polynomial.aeval t ContactKummerOrder318.denominator:ℚ):K c t)

include hn in
theorem quartic_ne : quarticValue c t≠0 := by
  have h (j : Fin 4) : t-LinearContactSquareclass318.contacts j≠0 := by
    intro hz
    apply hn j
    rw [RationalContactPoint318.parameters_eq,hz,mul_zero]
  have hP : Polynomial.aeval t ContactKummerOrder318.denominator≠0 := by
    simpa only [ContactKummerOrder318.denominator,map_prod,map_sub,Polynomial.aeval_X,
      Polynomial.aeval_C] using Finset.prod_ne_zero_iff.mpr (fun j _ => h j)
  exact_mod_cast hP

theorem quartic_value : ContactBranchPoint318.branchPoint c t hn i
    (ContactFiniteCoefficientIdentity318.branchP c i)=quarticValue c t := by
  rw [ContactFiniteCoefficientIdentity318.branchP,SourceOpenFractionField318.d,
    ContactBranchPoint318.branchPoint_polynomial]
  exact map_ratCast _ _

theorem coordinate_value : frame c t hn i (coordinate c t hn i)=1 := by
  rw [frame,coordinate,FramedCotangentFiber318.frame_differential,
    ContactFrameNormalization318.source_coordinate_normalized,map_one]

theorem dt_ne : frame c t hn i (dt c t hn i)≠0 := by
  have h := congrArg (ContactBranchPoint318.branchPoint c t hn i)
    (ContactFiniteCoefficientIdentity318.finite_cleared_frame c i)
  simp only [map_mul,map_pow,quartic_value] at h
  have hc := ((branchQ0_unit c i).map (ContactBranchPoint318.branchPoint c t hn i)).ne_zero
  intro hz
  have hz' : ContactBranchPoint318.branchPoint c t hn i
      (ContactDifferentialFrames318.sourceLocalizationFrame c i
        (KaehlerDifferential.D ℚ (BranchRing c i) (branchT c i)))=0 := by
    simpa only [frame,dt,FramedCotangentFiber318.frame_differential] using hz
  rw [hz',zero_pow (by decide : (2:ℕ)≠0)] at h
  exact mul_ne_zero (quartic_ne c t hn) hc h

/-- The literal original evaluated global section, with no projective
rescaling, equals its actual squared-cotangent-fiber coefficient. -/
theorem original_value_zero : ContactBicanonicalPointHeight318.a0 c t hn i=
    (VerticalSection318.J:K c t)^2*
      ContactBranchPoint318.branchPoint c t hn i (branchQ0 c i) := by
  change ContactBicanonicalPointValue318.value c t hn i
    (ContactScaledBicanonicalPoint318.scaledQ0 c)=_
  rw [ContactScaledBicanonicalPoint318.scaledQ0,ContactScaledBicanonicalPoint318.value_nsmul,
    nsmul_eq_mul,ContactBicanonicalPointValue318.value_q0,Nat.cast_pow]
  have hJ : (ContactScaledBicanonicalPoint318.J:K c t)=(VerticalSection318.J:K c t) := by
    norm_num only [ContactScaledBicanonicalPoint318.J,VerticalSection318.J,Int.cast_ofNat]
  rw [hJ]

/-- Exact differential normalization of the original rational point value. -/
theorem cleared_original : quarticValue c t*ContactBicanonicalPointHeight318.a0 c t hn i=
    (VerticalSection318.J:K c t)^2*(frame c t hn i (dt c t hn i))^2 := by
  have h := congrArg (ContactBranchPoint318.branchPoint c t hn i)
    (ContactFiniteCoefficientIdentity318.finite_cleared_frame c i)
  simp only [map_mul,map_pow,quartic_value] at h
  rw [original_value_zero,frame,dt,FramedCotangentFiber318.frame_differential]
  change _=(VerticalSection318.J:K c t)^2*(ContactBranchPoint318.branchPoint c t hn i _ )^2
  calc
    _ = (VerticalSection318.J:K c t)^2*(quarticValue c t*
      ContactBranchPoint318.branchPoint c t hn i (branchQ0 c i)) := by ring
    _ = _ := by rw [h]
end OriginalBranchCotangentFiber318
