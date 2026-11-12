module
public import NormalizedPointSigns318
public import ShortScaling318
public section
noncomputable section

/-! Injective additive normalization, retaining the original elliptic point. -/
namespace NormalizationInjection318
open ReciprocalDouble318 ShortCurveBaseChange318
open WeierstrassCurve.Affine
set_option maxHeartbeats 1000000

section General
variable {F L : Type*} [Field F] [Field L] [CharZero F] [CharZero L]
  [DecidableEq F] [DecidableEq L]

private instance short (d : L) : (E d).IsShortNF := ⟨rfl,rfl,rfl⟩

lemma elliptic (d : L) (hd : d≠0) : (E d).IsElliptic := by
  constructor
  apply isUnit_iff_ne_zero.mpr
  have he : (E d).Δ=64*d^3 := by
    rw [WeierstrassCurve.Δ_of_isShortNF]
    simp only [E]
    ring
  rw [he]
  exact mul_ne_zero (by norm_num) (pow_ne_zero 3 hd)

@[expose] def inverseUnit (r : L) (hr : r≠0) : Lˣ := (Units.mk0 r hr)⁻¹

lemma scale_four (r : L) (hr : r≠0) :
    (E (1:L)).a₄=(inverseUnit r hr:L)^4*(E (r^4)).a₄ := by
  change -(1:L)=(r⁻¹)^4* -(r^4)
  field_simp [hr]

lemma scale_six (r : L) (hr : r≠0) :
    (E (1:L)).a₆=(inverseUnit r hr:L)^6*(E (r^4)).a₆ := by
  simp only [E,mul_zero]

/-- Normalizing u by r scales reciprocal x by r^-2 and y by r^-3.
This equivalence preserves the actual chord-and-tangent addition. -/
@[expose] def scale (r : L) (hr : r≠0) : (E (r^4)).Point ≃+ (E (1:L)).Point := by
  letI : (E (r^4)).IsShortNF := ⟨rfl,rfl,rfl⟩
  letI : (E (1:L)).IsShortNF := ⟨rfl,rfl,rfl⟩
  letI := elliptic (r^4) (pow_ne_zero 4 hr)
  letI := elliptic (1:L) one_ne_zero
  exact ShortScaling318.pointAddEquiv (E (r^4)) (E 1) (inverseUnit r hr)
    (scale_four r hr) (scale_six r hr)

lemma scale_some (r : L) (hr : r≠0) (x y : L) (h : (E (r^4)).Nonsingular x y) :
    ∃ h' : (E (1:L)).Nonsingular (r⁻¹^2*x) (r⁻¹^3*y),
      scale r hr (Point.some x y h)=Point.some _ _ h' := by
  dsimp [scale,ShortScaling318.pointAddEquiv,ShortScaling318.pointEquiv,
    ShortScaling318.pointMap,Point.mk,inverseUnit]
  exact ⟨_,rfl⟩

/-- Original-field base change, explicit coefficient equality, then scaling.
There is no presumed additive law on the normalized quartic coordinates. -/
@[expose] def normalize (φ : F →+* L) (D : F) (r : L) (hr : r≠0)
    (hD : φ D=r^4) : (E D).Point →+ (E (1:L)).Point :=
  (scale r hr).toAddMonoidHom.comp
    ((transport (congrArg E hD)).toAddMonoidHom.comp (pointMap φ D))

theorem normalize_injective (φ : F →+* L) (D : F) (r : L) (hr : r≠0)
    (hD : φ D=r^4) : Function.Injective (normalize φ D r hr hD) :=
  (scale r hr).injective.comp ((transport (congrArg E hD)).injective.comp
    (pointMap_injective φ D))

lemma normalize_some (φ : F →+* L) (D : F) (r : L) (hr : r≠0)
    (hD : φ D=r^4) (x y : F) (h : (E D).Nonsingular x y) :
    ∃ h' : (E (1:L)).Nonsingular (r⁻¹^2*φ x) (r⁻¹^3*φ y),
      normalize φ D r hr hD (Point.some x y h)=Point.some _ _ h' := by
  change ∃ h', scale r hr
    (transport (congrArg E hD) (pointMap φ D (Point.some x y h)))=Point.some _ _ h'
  rw [pointMap_some,transport_some]
  exact scale_some r hr _ _ _

lemma normalized_curve (φ : F →+* L) (D : F) (r : L) (hD : φ D=r^4)
    (u v : F) (hc : v^2=1-D*u^4) :
    (φ v)^2=1-(1:L)*(r*φ u)^4 := by
  have he := congrArg φ hc
  simp only [map_pow,map_sub,map_one,map_mul,hD] at he
  simpa only [mul_pow,one_mul] using he

lemma normalize_reciprocal (φ : F →+* L) (D : F) (r : L) (hr : r≠0)
    (hD : φ D=r^4) (u v : F) (hv : v≠0) (hc : v^2=1-D*u^4) :
    normalize φ D r hr hD (point D u v hv hc)=
      point 1 (r*φ u) (φ v)
        (fun h => hv (φ.injective (h.trans φ.map_zero.symm)))
        (normalized_curve φ D r hD u v hc) := by
  by_cases hu : u=0
  · subst u
    simp only [point_zero,map_zero,mul_zero]
  · have hφu : φ u≠0 := fun h => hu (φ.injective (h.trans φ.map_zero.symm))
    have hru : r*φ u≠0 := mul_ne_zero hr hφu
    simp only [point,dite_eq_right hu,dite_eq_right hru]
    obtain ⟨h',he⟩ := normalize_some φ D r hr hD (1/u^2) (v/u^3) _
    rw [he,Point.some.injEq]
    constructor
    · simp only [map_div₀,map_one,map_pow,mul_pow]
      field_simp [hr,hφu]
    · simp only [map_div₀,map_pow,mul_pow]
      field_simp [hr,hφu]

/-- Nontorsion is carried from the original point by an injective additive
map. It is not deduced from affine-coordinate nonvanishing. -/
theorem normalize_nontorsion (φ : F →+* L) (D : F) (r : L) (hr : r≠0)
    (hD : φ D=r^4) (P : (E D).Point)
    (hP : ∀ n : ℤ, n • P=0 → n=0) :
    ∀ n : ℤ, n • normalize φ D r hr hD P=0 → n=0 := by
  intro n hn
  apply hP n
  apply normalize_injective φ D r hr hD
  simpa only [map_zsmul,map_zero] using hn

end General

section Concrete
open NormalizingRadicals318 NormalizedPointSigns318
open ConcreteG8Domain (K)
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Both := Classical.decEq Both

lemma firstRoot_ne : firstRoot≠0 := by
  intro hz
  have he := firstRoot_square
  rw [hz,zero_pow (by decide : 2≠0)] at he
  exact delta_ne_zero (base.injective (by simpa only [base,RingHom.comp_apply,map_zero] using he.symm))

lemma secondRoot_ne : secondRoot≠0 := by
  intro hz
  have he := secondRoot_square
  rw [hz,zero_pow (by decide : 2≠0)] at he
  have hd : deltaBar=0 := base.injective (by simpa only [base,RingHom.comp_apply,map_zero] using he.symm)
  have hre := congrArg QuadraticAlgebra.re hd
  norm_num [deltaBar,ConcreteG8Domain.pair] at hre

lemma first_coefficient : base ConcreteG8Domain.D=firstRoot^4 := by
  rw [show firstRoot^4=(firstRoot^2)^2 by ring,firstRoot_square]
  change base ConcreteG8Domain.D=(base delta)^2
  rw [←map_pow,delta_square]

lemma second_coefficient : base (deltaBar^2)=secondRoot^4 := by
  rw [show secondRoot^4=(secondRoot^2)^2 by ring,secondRoot_square]
  exact base.map_pow deltaBar 2

/-- The first normalized point is exactly the injective additive image of
the original reciprocal point, with D unchanged. -/
lemma firstPoint_image (u v : K) (hv : v≠0)
    (hc : v^2=1-ConcreteG8Domain.D*u^4) :
    normalize base ConcreteG8Domain.D firstRoot firstRoot_ne first_coefficient
      (point ConcreteG8Domain.D u v hv hc)=firstPoint u v hv hc :=
  normalize_reciprocal base _ _ _ _ u v hv hc

lemma secondPoint_image (u v : K) (hv : v≠0)
    (hc : v^2=1-deltaBar^2*u^4) :
    normalize base (deltaBar^2) secondRoot secondRoot_ne second_coefficient
      (point (deltaBar^2) u v hv hc)=secondPoint u v hv hc :=
  normalize_reciprocal base _ _ _ _ u v hv hc

/-- The relation theorem now consumes nontorsion only on the original two
source curves. The new normalization does not assume nontorsion downstream. -/
theorem original_relation_coefficients_zero
    (u v u' v' : K) (hv : v≠0) (hv' : v'≠0)
    (hc : v^2=1-ConcreteG8Domain.D*u^4) (hc' : v'^2=1-deltaBar^2*u'^4)
    (hfirst : ∀ n : ℤ, n • point ConcreteG8Domain.D u v hv hc=0 → n=0)
    (hsecond : ∀ n : ℤ, n • point (deltaBar^2) u' v' hv' hc'=0 → n=0)
    (m n : ℤ)
    (hrel : m • firstPoint u v hv hc+n • secondPoint u' v' hv' hc'=0) :
    m=0 ∧ n=0 := by
  apply normalized_relation_coefficients_zero u v u' v' hv hv' hc hc' _ _ m n hrel
  · have h := normalize_nontorsion base _ firstRoot firstRoot_ne first_coefficient
      _ hfirst
    simpa only [firstPoint_image] using h
  · have h := normalize_nontorsion base _ secondRoot secondRoot_ne second_coefficient
      _ hsecond
    simpa only [secondPoint_image] using h

end Concrete
end NormalizationInjection318
