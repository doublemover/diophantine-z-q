module
public import ActualGaussianWeberGaussLocalization318
public import Mathlib.RingTheory.Localization.Away.Basic
public section
noncomputable section

namespace ActualGaussianWeberTranslationChart318

open Polynomial
open ActualGaussianWeberQuadraticGenericChart318 ActualGaussianWeberGaussLocalization318

section Coordinates

variable (K : Type*) [CommRing K]

@[expose] def xChart : Chart K := AdjoinRoot.of (relation K) (X:K[X])
@[expose] def yChart : Chart K := AdjoinRoot.root (relation K)

theorem xChart_ne [Nontrivial K] : xChart K≠0 := by
  have hm : (relation K).Monic := monic_X_pow_sub_C _ (by decide)
  have hd : 0<(relation K).degree := by
    have e : (relation K).degree=2 := degree_X_pow_sub_C (by decide : 0<2) _
    rw [e]
    decide
  exact fun h => X_ne_zero
    (AdjoinRoot.of.injective_of_monic_of_degree_pos hm hd (h.trans (map_zero _).symm))

theorem equation_chart : (yChart K)^2=(xChart K)^3-xChart K := by
  have h : (((X : (K[X])[X])^2 - C ((X : K[X])^3 - X))).eval₂
      (AdjoinRoot.of (relation K)) (AdjoinRoot.root (relation K)) = 0 :=
    AdjoinRoot.eval₂_root (relation K)
  rw [eval₂_sub,eval₂_pow,eval₂_X,eval₂_C,map_sub,map_pow] at h
  change (yChart K)^2 - ((xChart K)^3 - xChart K) = 0 at h
  exact sub_eq_zero.mp h

theorem map_xChart {L : Type*} [CommRing L] (f : K→+*L) :
    mapChart f (xChart K)=xChart L := by
  simp only [xChart,mapChart,AdjoinRoot.map_of,coe_mapRingHom,map_X]

theorem map_yChart {L : Type*} [CommRing L] (f : K→+*L) :
    mapChart f (yChart K)=yChart L := by
  simp only [yChart,mapChart,AdjoinRoot.map_root]

end Coordinates

variable (K : Type*) [Field K]

abbrev XOpen := Localization.Away (xChart K)

@[expose] def chartMap : Chart K→+*XOpen K := algebraMap (Chart K) (XOpen K)
@[expose] def z : XOpen K := chartMap K (xChart K)
@[expose] def w : XOpen K := chartMap K (yChart K)
@[expose] def zi : XOpen K := IsLocalization.Away.invSelf (S:=XOpen K) (xChart K)

theorem zzi : z K*zi K=1 := IsLocalization.Away.mul_invSelf (S:=XOpen K) (xChart K)

theorem equation_open : (w K)^2=(z K)^3-z K := by
  have h := congrArg (chartMap K) (equation_chart K)
  simpa only [map_pow,map_sub,z,w] using h

/-- Literal regular coordinate substitution on the x-nonzero chart:
(X,Y) ↦ (−X⁻¹,Y X⁻²). -/
theorem equation_translated :
    (w K*(zi K)^2)^2=(-zi K)^3-(-zi K) := by
  calc
    _ = ((z K)^3-z K)*(zi K)^4 := by rw [mul_pow,equation_open K]; ring
    _ = (z K*zi K)^3*zi K-(z K*zi K)*(zi K)^3 := by ring
    _ = _ := by rw [zzi K]; ring

@[expose] def constants : K→+*XOpen K :=
  (chartMap K).comp ((AdjoinRoot.of (relation K)).comp C)

@[expose] def xMap : K[X]→+*XOpen K := eval₂RingHom (constants K) (-zi K)

theorem translated_root :
    (relation K).eval₂ (xMap K) (w K*(zi K)^2)=0 := by
  change (((X : (K[X])[X])^2 - C ((X : K[X])^3 - X))).eval₂
    (xMap K) (w K*(zi K)^2) = 0
  rw [eval₂_sub,eval₂_pow,eval₂_X,eval₂_C,map_sub,map_pow]
  rw [show xMap K X = -zi K from eval₂_X _ _]
  exact sub_eq_zero.mpr (equation_translated K)

@[expose] def preTranslate : Chart K→+*XOpen K :=
  AdjoinRoot.lift (xMap K) (w K*(zi K)^2) (translated_root K)

theorem preTranslate_x : preTranslate K (xChart K)= -zi K := by
  change AdjoinRoot.lift (xMap K) _ (translated_root K) (AdjoinRoot.of (relation K) X)=_
  rw [AdjoinRoot.lift_of]
  exact eval₂_X _ _

theorem preTranslate_y : preTranslate K (yChart K)=w K*(zi K)^2 :=
  AdjoinRoot.lift_root (translated_root K)

theorem preTranslate_constants (c : K) :
    preTranslate K (AdjoinRoot.of (relation K) (C c))=constants K c := by
  change AdjoinRoot.lift (xMap K) _ (translated_root K) (AdjoinRoot.of (relation K) (C c))=_
  rw [AdjoinRoot.lift_of]
  exact eval₂_C _ _

theorem preTranslate_unit : IsUnit (preTranslate K (xChart K)) := by
  rw [preTranslate_x K]
  refine ⟨⟨-zi K,-z K,?_,?_⟩,rfl⟩
  · rw [neg_mul_neg,mul_comm,zzi K]
  · rw [neg_mul_neg,zzi K]

@[expose] def translateOpen : XOpen K→+*XOpen K :=
  IsLocalization.Away.lift (S:=XOpen K) (xChart K) (preTranslate_unit K)

theorem translate_open_chart (a : Chart K) :
    translateOpen K (chartMap K a)=preTranslate K a :=
  IsLocalization.Away.lift_eq _ _ _

theorem translate_open_x : translateOpen K (z K)= -zi K :=
  (translate_open_chart K (xChart K)).trans (preTranslate_x K)

theorem translate_open_y : translateOpen K (w K)=w K*(zi K)^2 :=
  (translate_open_chart K (yChart K)).trans (preTranslate_y K)

theorem translate_open_const (c : K) : translateOpen K (constants K c)=constants K c :=
  (translate_open_chart K (AdjoinRoot.of (relation K) (C c))).trans
    (preTranslate_constants K c)

theorem translate_open_inv : translateOpen K (zi K)= -z K := by
  have h := congrArg (translateOpen K) (zzi K)
  simp only [map_mul,translate_open_x,map_one] at h
  calc
    _ = (z K*zi K)*translateOpen K (zi K) := by rw [zzi K,one_mul]
    _ = (-z K)*((-zi K)*translateOpen K (zi K)) := by ring
    _ = _ := by rw [h,mul_one]

/-- Exact involution on the full x-open coordinate ring. -/
theorem translate_open_twice :
    (translateOpen K).comp (translateOpen K)=RingHom.id (XOpen K) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (xChart K))
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext'
    · apply RingHom.ext
      intro c
      change translateOpen K (translateOpen K (constants K c))=constants K c
      rw [translate_open_const,translate_open_const]
    · change translateOpen K (translateOpen K (z K))=z K
      rw [translate_open_x,map_neg,translate_open_inv,neg_neg]
  · change translateOpen K (translateOpen K (w K))=w K
    rw [translate_open_y,map_mul,map_pow,translate_open_inv,translate_open_y]
    calc
      _ = w K*(z K*zi K)^2 := by ring
      _ = _ := by rw [zzi K,one_pow,mul_one]

theorem translateOpen_injective : Function.Injective (translateOpen K) := by
  intro a b h
  have e := congrArg (translateOpen K) h
  change (translateOpen K).comp (translateOpen K) a =
    (translateOpen K).comp (translateOpen K) b at e
  rwa [translate_open_twice,RingHom.id_apply,RingHom.id_apply] at e

end ActualGaussianWeberTranslationChart318
