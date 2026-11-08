module
public import BothMixedMaps318
public section
noncomputable section
namespace BothInfinitySymmetry318
open InfinityVietaAlgebra318 BothInfinityAlgebra318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxRecDepth 8192
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section Polynomial
variable {T:Type*} [CommRing T]
/-- The two regular divided differences give the same line, including equal inputs. -/
lemma cross_slope (A B u v t w:T) (h1:equation A B u v=0) (h2:equation A B t w=0) :
    s A u t v*q A B u w v=s A t u w*q A B t v w := by
  simp only [s,q,equation] at *
  linear_combination A*(v+w)*h1-A*(v+w)*h2
lemma slope_unique (A B u v t w a a':T) (h1:equation A B u v=0) (h2:equation A B t w=0)
    (hq:IsUnit (q A B t v w)) (hq':IsUnit (q A B u w v))
    (ha:a*q A B t v w=s A u t v) (ha':a'*q A B u w v=s A t u w) : a=a' := by
  apply (hq.mul hq').mul_right_cancel
  calc
    _=(a*q A B t v w)*q A B u w v := by ring
    _=s A u t v*q A B u w v := by rw [ha]
    _=s A t u w*q A B t v w := cross_slope A B u v t w h1 h2
    _=a'*(q A B t v w*q A B u w v) := by rw [←ha']; ring
end Polynomial

variable {R S:Type u} [CommRing R] [CommRing S] [Algebra R S]
lemma map_c (A B:R) (φ:OutputRing A B →ₐ[R] S) :
    φ (c (algebraMap R (OutputRing A B) A) (algebraMap R (OutputRing A B) B) (slope A B))=
      c (algebraMap R S A) (algebraMap R S B) (φ (slope A B)) := by
  have hm (r:OutputRing A B) (n:ℕ) : φ (r^n)=(φ r)^n := φ.toRingHom.map_pow r n
  have h1:φ 1=1:=φ.toRingHom.map_one
  simp only [c,map_add,map_mul,hm,h1,AlgHom.commutes]
lemma map_d (A B:R) (φ:OutputRing A B →ₐ[R] S) :
    φ (d (algebraMap R (OutputRing A B) A) (algebraMap R (OutputRing A B) B) (slope A B) (intercept A B))=
      d (algebraMap R S A) (algebraMap R S B) (φ (slope A B)) (φ (intercept A B)) := by
  have hm (r:OutputRing A B) (n:ℕ) : φ (r^n)=(φ r)^n := φ.toRingHom.map_pow r n
  simp only [d,map_add,map_mul,hm,map_ofNat,AlgHom.commutes]
lemma map_q (A B:R) (φ:OutputRing A B →ₐ[R] S) :
    φ (pairMap A B (Q A B))=q (algebraMap R S A) (algebraMap R S B)
      (φ (u2 A B)) (φ (v1 A B)) (φ (v2 A B)) := by
  rw [map_Q]
  have hm (r:OutputRing A B) (n:ℕ) : φ (r^n)=(φ r)^n := φ.toRingHom.map_pow r n
  have h1:φ 1=1:=φ.toRingHom.map_one
  simp only [q,map_add,map_sub,map_mul,hm,h1,AlgHom.commutes]
lemma map_s (A B:R) (φ:OutputRing A B →ₐ[R] S) :
    φ (pairMap A B (BothInfinityAlgebra318.S A B))=s (algebraMap R S A)
      (φ (u1 A B)) (φ (u2 A B)) (φ (v1 A B)) := by
  rw [map_S]
  have hm (r:OutputRing A B) (n:ℕ) : φ (r^n)=(φ r)^n := φ.toRingHom.map_pow r n
  simp only [s,map_add,map_mul,hm,AlgHom.commutes]

/-- Equality of regular both-infinity outputs on the actual reversed-input overlap. -/
theorem coordinates (A B:R) (φ ψ:OutputRing A B →ₐ[R] S)
    (hu:φ (u1 A B)=ψ (u2 A B)) (hv:φ (v1 A B)=ψ (v2 A B))
    (ht:φ (u2 A B)=ψ (u1 A B)) (hw:φ (v2 A B)=ψ (v1 A B)) :
    φ (outU A B)=ψ (outU A B) ∧ φ (outV A B)=ψ (outV A B) := by
  have hm (r:OutputRing A B) (n:ℕ) : φ (r^n)=(φ r)^n := φ.toRingHom.map_pow r n
  have h1:=congrArg φ (mapped_first A B)
  have h2:=congrArg φ (mapped_second A B)
  simp only [equation,map_sub,map_mul,hm,map_zero,AlgHom.commutes] at h1 h2
  have hq:IsUnit (q (algebraMap R S A) (algebraMap R S B) (φ (u2 A B)) (φ (v1 A B)) (φ (v2 A B))) := by
    rw [←map_q]
    exact (two_units A B).1.map φ
  have hq':IsUnit (q (algebraMap R S A) (algebraMap R S B) (φ (u1 A B)) (φ (v2 A B)) (φ (v1 A B))) := by
    rw [hu,hv,hw,←map_q]
    exact (two_units A B).1.map ψ
  have ha:=congrArg φ (slope_Q A B)
  have ha':=congrArg ψ (slope_Q A B)
  simp only [map_mul,map_q,map_s] at ha ha'
  rw [←hu,←hv,←ht,←hw] at ha'
  have hsl:φ (slope A B)=ψ (slope A B) :=
    slope_unique _ _ _ _ _ _ _ _ h1 h2 hq hq' ha ha'
  have hb:φ (intercept A B)=ψ (intercept A B) := by
    have hl:=congrArg φ (line_second A B)
    simp only [map_add,map_mul,ht,hw,hsl] at hl
    have hr:ψ (intercept A B)=ψ (v1 A B)-ψ (slope A B)*ψ (u1 A B) := by
      simp only [intercept,map_sub,map_mul]
    rw [hr]
    linear_combination -hl
  have hc:IsUnit (c (algebraMap R S A) (algebraMap R S B) (φ (slope A B))) := by
    rw [←map_c]
    exact (cubic_coefficient_unit A B).map φ
  have ho:=congrArg φ (BothMixedMaps318.outU_relation A B)
  have ho':=congrArg ψ (BothMixedMaps318.outU_relation A B)
  simp only [map_mul,map_sub,map_c,map_d] at ho ho'
  rw [←hu,←ht,←hsl,←hb] at ho'
  have hout:φ (outU A B)=ψ (outU A B) := by
    apply hc.mul_left_cancel
    linear_combination ho-ho'
  refine ⟨hout,?_⟩
  simp only [outV,map_sub,map_mul,hsl,hb,hout]

theorem scheme_agreement (A B:R) (φ ψ:OutputRing A B →ₐ[R] S)
    (hu:φ (u1 A B)=ψ (u2 A B)) (hv:φ (v1 A B)=ψ (v2 A B))
    (ht:φ (u2 A B)=ψ (u1 A B)) (hw:φ (v2 A B)=ψ (v1 A B)) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ BothInfinityScheme318.addition A B=
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ BothInfinityScheme318.addition A B := by
  have he:(φ.comp (outputMap A B))=(ψ.comp (outputMap A B)) := by
    apply InfinityChart318.hom_ext
    · simpa only [AlgHom.comp_apply,outputMap,InfinityChart318.lift_x] using (coordinates A B φ ψ hu hv ht hw).1
    · simpa only [AlgHom.comp_apply,outputMap,InfinityChart318.lift_z] using (coordinates A B φ ψ hu hv ht hw).2
  dsimp only [BothInfinityScheme318.addition,BothInfinityScheme318.chartAddition]
  rw [←Category.assoc,←Category.assoc,←Spec.map_comp,←Spec.map_comp]
  congr 2
  exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom he)
end BothInfinitySymmetry318
