module
public import NormalizedWeierstrass318
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import CubicClosedImmersion318
public import WeierstrassXProjection318
public section
noncomputable section
namespace NormalizedLegendreProjectiveModel318
open AlgebraicGeometry CategoryTheory

@[expose] def A (l:ℂ) : ℂ:=-(l^2-l+1)/3
@[expose] def B (l:ℂ) : ℂ:=-(2*l-1)*(l+1)*(l-2)/27
@[expose] def shift (l:ℂ) : ℂ:=(l+1)/3

/-- Exact translation of the original Legendre polynomial. The native
short-Weierstrass x-coordinate is t-(lambda+1)/3, not t itself. -/
lemma translated_polynomial (l t:ℂ) :
    (t-shift l)^3+A l*(t-shift l)+B l=t*(t-1)*(t-l) := by
  dsimp [A,B,shift]
  ring
lemma discriminant (l:ℂ) : -16*(4*A l^3+27*B l^2)=16*l^2*(l-1)^2 := by
  dsimp [A,B]
  ring
lemma discriminant_ne (l:ℂ) (h0:l≠0) (h1:l≠1) : -16*(4*A l^3+27*B l^2)≠0 := by
  rw [discriminant]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 h0))
    (pow_ne_zero 2 (sub_ne_zero.mpr h1))

/-- Actual algebraic Weierstrass curve with the translated Legendre
coefficients. No original analytic double-cover identification is assumed. -/
@[expose] def curve (l:ℂ) : WeierstrassCurve ℂ:=
  NormalizedWeierstrass318.model (-48*A l) (-864*B l)
lemma curve_discriminant (l:ℂ) : (curve l).Δ=16*l^2*(l-1)^2 := by
  rw [curve,NormalizedWeierstrass318.model_discriminant]
  calc
    _ = -16*(4*A l^3+27*B l^2) := by ring
    _ = _ := discriminant l

lemma curve_elliptic (l:ℂ) (h0:l≠0) (h1:l≠1) : (curve l).IsElliptic := by
  refine ⟨isUnit_iff_ne_zero.mpr ?_⟩
  rw [curve_discriminant]
  simpa only [discriminant] using discriminant_ne l h0 h1

lemma curve_equation (l t y:ℂ) : (curve l).toAffine.Equation (t-shift l) y ↔
    y^2=t*(t-1)*(t-l) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  change y^2+0*(t-shift l)*y+0*y=
    (t-shift l)^3+0*(t-shift l)^2+(-(-48*A l)/48)*(t-shift l)+(-(-864*B l)/864) ↔ _
  have h: (t-shift l)^3+0*(t-shift l)^2+(-(-48*A l)/48)*(t-shift l)+(-(-864*B l)/864)=
      t*(t-1)*(t-l) := by
    calc
      _=(t-shift l)^3+A l*(t-shift l)+B l:=by ring
      _=_:=translated_polynomial l t
  rw [h]
  simp

lemma curve_j (l:ℂ) (h0:l≠0) (h1:l≠1) :
    letI := curve_elliptic l h0 h1
    (curve l).j=256*(l^2-l+1)^3/(l^2*(l-1)^2) := by
  letI := curve_elliptic l h0 h1
  rw [curve,NormalizedWeierstrass318.model_j]
  have hd:((-48*A l)^3-(-864*B l)^2)/1728=16*l^2*(l-1)^2 := by
    calc
      _ = -16*(4*A l^3+27*B l^2) := by ring
      _ = _ := discriminant l
  rw [hd]
  dsimp [A]
  field_simp [h0,sub_ne_zero.mpr h1]
  <;> ring

/-- A genuine smooth proper projective SCHEME with the actual translated
coefficients and a full original x-coordinate Scheme morphism. -/
abbrev model (l:ℂ):=WeierstrassGluing318.scheme (A l) (B l)
abbrev structure (l:ℂ):=WeierstrassGluing318.structureMap (A l) (B l)
abbrev nativeXMap (l:ℂ):=WeierstrassXProjection318.xMap (A l) (B l)
theorem smooth (l:ℂ) (h0:l≠0) (h1:l≠1) : Smooth (structure l):=
  WeierstrassGluing318.structure_smooth _ _ (isUnit_iff_ne_zero.mpr (discriminant_ne l h0 h1))
theorem proper (l:ℂ) : IsProper (structure l):=CubicClosedImmersion318.structure_proper _ _
theorem separated (l:ℂ) : IsSeparated (structure l):=CubicClosedImmersion318.structure_separated _ _
theorem projective (l:ℂ) : IsClosedImmersion (CubicProjectiveMap318.embedding (A l) (B l)):=
  CubicClosedImmersion318.embedding_closed _ _
end NormalizedLegendreProjectiveModel318
