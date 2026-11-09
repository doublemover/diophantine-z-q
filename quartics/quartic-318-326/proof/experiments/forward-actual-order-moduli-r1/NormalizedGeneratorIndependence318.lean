module
public import NormalizationInjection318
public import SourceContact318
public import GeneratorMultiplesTwo318
public section
noncomputable section

/-! Integer independence of the two normalized images of the literal source P.
This is an algebraic statement, with no real-density conclusion. -/
namespace NormalizedGeneratorIndependence318
open ConcreteG8Domain (K D)
open scoped QuadraticAlgebra
open NormalizingRadicals318 NormalizedPointSigns318 NormalizationInjection318
open ReciprocalDouble318 ShortCurveBaseChange318
open WeierstrassCurve.Affine
local instance : DecidableEq Both := Classical.decEq Both
set_option maxHeartbeats 1000000

@[expose] def conjugateBase : K →+* Both := base.comp SourceContact318.conj

lemma conjugate_coefficient : conjugateBase D=secondRoot^4 := by
  have hd : SourceContact318.conj D=deltaBar^2 := by
    ext <;> norm_num [D,ConcreteG8Domain.i,ConcreteG8Domain.pair,
      SourceContact318.conj,deltaBar,pow_succ]
  change base (SourceContact318.conj D)=secondRoot^4
  rw [hd,second_coefficient]

/-- The two images have the identical original source P as input. Only the
specified base embedding and its corresponding normalizing radical differ. -/
@[expose] def firstGenerator : (E (1:Both)).Point :=
  normalize base D firstRoot firstRoot_ne first_coefficient LocalGenerator318.P

@[expose] def secondGenerator : (E (1:Both)).Point :=
  normalize conjugateBase D secondRoot secondRoot_ne conjugate_coefficient LocalGenerator318.P

private lemma source_nontorsion :
    ∀ n : ℤ, n • LocalGenerator318.P=0 → n=0 := by
  intro n hn
  by_contra hne
  exact GeneratorMultiplesTwo318.generator_infinite_order n hne hn

theorem firstGenerator_nontorsion : ∀ n : ℤ, n • firstGenerator=0 → n=0 :=
  normalize_nontorsion base D firstRoot firstRoot_ne first_coefficient _ source_nontorsion

theorem secondGenerator_nontorsion : ∀ n : ℤ, n • secondGenerator=0 → n=0 :=
  normalize_nontorsion conjugateBase D secondRoot secondRoot_ne conjugate_coefficient
    _ source_nontorsion

private lemma flipPoint_some (x y : Both) (h : (E (1:Both)).Nonsingular x y) :
    ∃ h' : (E (1:Both)).Nonsingular (flipSecond x) (flipSecond y),
      flipPoint (Point.some x y h)=Point.some _ _ h' := by
  change ∃ h', transport (congrArg E flipSecond.toRingHom.map_one)
    (pointMap flipSecond.toRingHom 1 (Point.some x y h))=Point.some _ _ h'
  rw [pointMap_some,transport_some]
  exact ⟨_,rfl⟩

lemma flip_firstGenerator : flipPoint firstGenerator=firstGenerator := by
  obtain ⟨h,he⟩ := normalize_some base D firstRoot firstRoot_ne first_coefficient
    LocalGenerator318.xP LocalGenerator318.yP LocalGenerator318.nonsingularP
  change flipPoint (normalize base D firstRoot firstRoot_ne first_coefficient
    (Point.some _ _ _))=normalize base D firstRoot firstRoot_ne first_coefficient
      (Point.some _ _ _)
  rw [he]
  obtain ⟨h',he'⟩ := flipPoint_some _ _ h
  rw [he',Point.some.injEq]
  constructor <;> simp only [map_mul,map_pow,map_inv₀,flipSecond_firstRoot,flip_base]

lemma flip_secondGenerator : flipPoint secondGenerator= -secondGenerator := by
  obtain ⟨h,he⟩ := normalize_some conjugateBase D secondRoot secondRoot_ne conjugate_coefficient
    LocalGenerator318.xP LocalGenerator318.yP LocalGenerator318.nonsingularP
  change flipPoint (normalize conjugateBase D secondRoot secondRoot_ne conjugate_coefficient
    (Point.some _ _ _))= -normalize conjugateBase D secondRoot secondRoot_ne conjugate_coefficient
      (Point.some _ _ _)
  rw [he]
  obtain ⟨h',he'⟩ := flipPoint_some _ _ h
  rw [he',Point.neg_some,Point.some.injEq]
  constructor <;> simp [conjugateBase,map_mul,map_pow,map_inv₀,
    flipSecond_secondRoot,flip_base,negY,E] <;>
    simp only [show (-secondRoot)^3= -(secondRoot^3) by ring,inv_neg,neg_mul]

/-- No nontrivial integer relation exists between the two actual algebraic
normalized source generators. All nontorsion inputs are proved upstream. -/
theorem integer_relation (m n : ℤ)
    (h : m • firstGenerator+n • secondGenerator=0) : m=0 ∧ n=0 :=
  relation_coefficients_zero flipPoint firstGenerator secondGenerator
    flip_firstGenerator flip_secondGenerator firstGenerator_nontorsion
    secondGenerator_nontorsion m n h

end NormalizedGeneratorIndependence318
