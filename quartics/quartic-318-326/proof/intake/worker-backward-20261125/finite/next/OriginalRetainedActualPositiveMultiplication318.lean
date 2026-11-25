module

public import OriginalRetainedActualMultiplicationPower318
public import OriginalOriginUniversalThickRead318
public import OriginalRetainedActualAffineStalkSquare318
public import OriginalRetainedMultiplicationStalk318
public import OriginalActualMultiplicationGenericImage318
public import OriginalActualMultiplicationGeometricPoint318
public import Mathlib.RingTheory.Localization.Submodule

@[expose] public section
noncomputable section

namespace OriginalRetainedActualPositiveMultiplication318

open AlgebraicGeometry CategoryTheory MonoidalCategory
open OriginalAffineOriginCotangent318 OriginalAffineOriginFirstOrder318
open OriginalActualOriginAffineJet318 OriginalRetainedActualMultiplicationPower318
open OriginalOriginUniversalThickRead318 OriginalRetainedActualAffineStalkSquare318
open OriginalRetainedMultiplicationStalk318 OriginalActualMultiplicationGenericImage318
open OriginalActualMultiplicationGeometricPoint318
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

universe u
variable {k B : Type u} [Field k] [CommRing B] [Algebra k B]
local notation "Sk" => Spec (CommRingCat.of k)
local notation "SB" => Spec (CommRingCat.of B)
variable {A : Over Sk} [MonObj A] {e : B→ₐ[k]k}
variable (C : Chart k A e)
local notation "P" => originIdeal e
local notation "M" => Cot e
local notation "T" => Thick k M

def oldOrigin (e : B→ₐ[k]k) : SB := ⟨originIdeal e,RingHom.ker_isPrime e.toRingHom⟩

local notation "z" => oldOrigin e

def thickAffine (e : B→ₐ[k]k) : B→ₐ[k] (Thick k (Cot e)) :=
  (points (S:=k) e (LinearMap.id : Cot e→ₗ[k]Cot e)).val

theorem thickAffine_fst (x : B) : (thickAffine e x).fst=e x := by
  let p := points (S:=k) e (LinearMap.id : M→ₗ[k]M)
  exact congrArg (fun q : B→ₐ[k]k => q x) p.property

theorem thickAffine_snd (x : P) : (thickAffine e x.val).snd=(originIdeal e).toCotangent x := by
  simpa only [thickAffine,points_snd,LinearMap.id_apply,differential_ideal]

theorem oldOrigin_ViaAugmentation :
    sp e.toRingHom (⊥ : PrimeSpectrum k)=z := by
  apply PrimeSpectrum.ext
  rfl

theorem multiplier_fixes_old_origin (n : ℕ) :
    (installed (A:=A) n).left (C.incl z)=C.incl z := by
  have eq := congrArg Over.Hom.left (on_actual_origin (A:=A) n)
  rw [Over.comp_left,←C.origin] at eq
  have atClosedPoint := congrArg (fun m : Sk ⟶ A.left => m (⊥ : PrimeSpectrum k)) eq
  simp only [Scheme.Hom.comp_apply,oldOrigin_ViaAugmentation] at atClosedPoint
  exact atClosedPoint

theorem thickAffine_multiplied_is_named (n : ℕ) :
    (points (S:=k) e (n • (LinearMap.id : M→ₗ[k]M))).val =
      (multiplyNil e n).comp (thickAffine e) := by
  apply AlgHom.ext
  intro b
  apply TrivSqZeroExt.ext
  · have read := congrArg (fun q : B→ₐ[k]k => q b)
      (points (S:=k) e (n • (LinearMap.id : M→ₗ[k]M))).property
    change ((points (S:=k) e (n • (LinearMap.id : M→ₗ[k]M))).val b).fst =
      (multiplyNil e n (thickAffine e b)).fst
    rw [multiplyNil,TrivSqZeroExt.fst_map,thickAffine_fst]
    exact read
  · change ((points (S:=k) e (n • (LinearMap.id : M→ₗ[k]M))).val b).snd =
      (multiplyNil e n (thickAffine e b)).snd
    rw [points_snd,multiplyNil,TrivSqZeroExt.snd_map,thickAffine,points_snd]

/-- Exact whole square on the original affine universal test. The
algebra is the original chart's own cotangent module and augmentation. -/
theorem square_on_actual_old_germ (n : ℕ) :
    (sp (thickAffine e).toRingHom≫C.incl)≫(installed (A:=A) n).left=
      sp (((multiplyNil e n).comp (thickAffine e)).toRingHom)≫C.incl := by
  have eq := congrArg Over.Hom.left (original_universal_cotangent_point C n)
  simp only [Over.comp_left,actual_left,thickAffine_multiplied_is_named n] at eq
  exact eq

variable [CharZero k] [IsNoetherianRing B]

/-- Choose the true original chart stalk and compute the exact
congruences from the universal point constructed above. Thus the
actual Scheme [n], not just a similar linear map, has injective
pullback on the actual ambient identity stalk. -/
theorem actual_multiplier_stalk_injective (n : ℕ) (positive : 0<n) :
    Function.Injective ((installed (A:=A) n).left.stalkMap (C.incl z)).hom := by
  let f := (installed (A:=A) n).left
  have fixed : f (C.incl z)=C.incl z := multiplier_fixes_old_origin C n
  letI : (originIdeal e).IsPrime := RingHom.ker_isPrime e.toRingHom
  letI : Algebra B (affineStalk B z) := inferInstanceAs (Algebra (CommRingCat.of B) (affineStalk B z))
  letI : IsLocalization.AtPrime (affineStalk B z) P := inferInstanceAs
    (IsLocalization.AtPrime (affineStalk B z) (oldOrigin e).asIdeal)
  letI : IsNoetherianRing (affineStalk B z) :=
    IsLocalization.isNoetherianRing (originIdeal e).primeCompl (affineStalk B z) inferInstance
  let j := thickAffine e
  let τ : (affineStalk B z)→+*T := wholeJet e j (thickAffine_fst (e:=e))
  have readsBase : τ.comp (StructureSheaf.toStalk (CommRingCat.of B) z).hom=j.toRingHom :=
    RingHom.ext (wholeJet_read e j (thickAffine_fst (e:=e)))
  have whole := whole_square_to_ring C.incl z f fixed j.toRingHom τ readsBase
    (multiplyNil e n).toRingHom (square_on_actual_old_germ C n)
  have ker := wholeJet_ker (L:=affineStalk B z) e j (thickAffine_fst (e:=e)) (thickAffine_snd (e:=e))
  obtain ⟨res,lin⟩ := actual_germ_congruences e j (thickAffine_fst (e:=e))
    (actualEnd C.incl z f fixed).hom n whole ker
  have nunit : IsUnit (n:(affineStalk B z)) := by
    have inK : IsUnit (n:k) := isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 positive.ne')
    have u := IsUnit.map ((algebraMap B (affineStalk B z)).comp (algebraMap k B)) inK
    simpa only [RingHom.comp_apply,map_natCast] using u
  exact true_stalk_injective C.incl z f fixed
    (injective_from_cotangent_unit _ _ _ res lin (IsLocalRing.maximalIdeal.isMaximal _).ne_top nunit)

variable [IsIntegral A.left] [IsProper A.hom] [IsAlgClosed k]

/-- The installed true [n] is onto on the whole original field-point
group. This includes every positive n and does not use a period,
an exponential, or analytic divisibility. -/
theorem actual_group_points_divisible (n : ℕ) (positive : 0<n) :
    Function.Surjective (fun w : (Over.mk (𝟙 Sk) ⟶ A) => w^n) := by
  intro p
  let f := (installed (A:=A) n).left
  letI : IsProper f := actual_proper (A:=A) n
  letI : Surjective f := actual_scheme_surjective f (C.incl z)
    (actual_multiplier_stalk_injective C n positive)
  obtain ⟨q,hq⟩ := lift_actual_geometric_point f p.left
  let w : Over.mk (𝟙 Sk) ⟶ A := Over.homMk q (by
    rw [←(installed (A:=A) n).w,←Category.assoc,hq]
    exact p.w)
  refine ⟨w,?_⟩
  apply Over.OverMorphism.ext
  have read := congrArg Over.Hom.left (on_actual_points w n)
  rw [Over.comp_left] at read
  exact read.symm.trans hq

end OriginalRetainedActualPositiveMultiplication318
