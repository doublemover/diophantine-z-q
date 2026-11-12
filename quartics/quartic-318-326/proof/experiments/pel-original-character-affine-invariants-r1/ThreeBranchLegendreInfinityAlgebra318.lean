module
public import ThreeBranchLegendrePolynomial318
public import InfinityChart318
public section
noncomputable section
namespace ThreeBranchLegendreInfinityAlgebra318
open Polynomial ThreeBranchLegendrePolynomial318
set_option maxHeartbeats 800000

@[expose] def center (a b c:ℂ):ℂ:=
  a+(b-a)*NormalizedLegendreProjectiveModel318.shift (parameter a b c)
@[expose] def scale (a b:ℂ):ℂ:=rootScale a b/(b-a)

lemma scale_square (a b:ℂ) (hab:b≠a):scale a b^2=b-a:=by
  dsimp [scale]
  rw [div_pow,rootScale_square]
  field_simp [sub_ne_zero.mpr hab]
  <;> ring

lemma scale_cube (a b:ℂ) (hab:b≠a):scale a b^3=rootScale a b:=by
  calc
    scale a b^3=scale a b*scale a b^2:=by ring
    _=rootScale a b:=by
      rw [scale_square a b hab]
      exact div_mul_cancel₀ _ (sub_ne_zero.mpr hab)

/-- Homogeneous reciprocal form of the SAME affine Legendre substitution.
No inverse of the source infinity parameter is used. -/
lemma reciprocal_polynomial (a b c o:ℂ) (hab:b≠a):
    (1+C (o-a)*X^2)*(1+C (o-b)*X^2)*(1+C (o-c)*X^2)=
      (1+C (o-center a b c)*X^2)^3+
      C ((b-a)^2*NormalizedLegendreProjectiveModel318.A (parameter a b c))*
        (1+C (o-center a b c)*X^2)*X^4+
      C ((b-a)^3*NormalizedLegendreProjectiveModel318.B (parameter a b c))*X^6:=by
  apply Polynomial.funext
  intro u
  simp only [eval_mul,eval_add,eval_one,eval_C,eval_pow,eval_X]
  dsimp [center,parameter,NormalizedLegendreProjectiveModel318.A,
    NormalizedLegendreProjectiveModel318.B,NormalizedLegendreProjectiveModel318.shift]
  field_simp [sub_ne_zero.mpr hab]
  <;> ring

variable {S:Type*} [CommRing S] [Algebra ℂ S]

lemma reciprocal_identity (a b c o:ℂ) (hab:b≠a) (u:S):
    (1+algebraMap ℂ S (o-a)*u^2)*(1+algebraMap ℂ S (o-b)*u^2)*
      (1+algebraMap ℂ S (o-c)*u^2)=
      (1+algebraMap ℂ S (o-center a b c)*u^2)^3+
      algebraMap ℂ S (scale a b)^4*
        algebraMap ℂ S (NormalizedLegendreProjectiveModel318.A (parameter a b c))*
        (1+algebraMap ℂ S (o-center a b c)*u^2)*u^4+
      algebraMap ℂ S (scale a b)^6*
        algebraMap ℂ S (NormalizedLegendreProjectiveModel318.B (parameter a b c))*u^6:=by
  have h:=congrArg (Polynomial.aeval u) (reciprocal_polynomial a b c o hab)
  simp only [map_mul,map_add,map_one,map_pow,Polynomial.aeval_C,Polynomial.aeval_X] at h
  have h4:scale a b^4=(b-a)^2:=by
    calc
      scale a b^4=(scale a b^2)^2:=by ring
      _=(b-a)^2:=by rw [scale_square a b hab]
  have h6:scale a b^6=(b-a)^3:=by
    calc
      scale a b^6=(scale a b^2)^3:=by ring
      _=(b-a)^3:=by rw [scale_square a b hab]
  simpa only [map_mul,←map_pow,h4,h6] using h

/-- A ring-level infinity chart construction. The ordinate denominator is
an actual unit; the source parameter may vanish, including all infinity
points. This is not a calculation only in the generic function field. -/
lemma infinity_relation (q u w A B:S) (r:Sˣ)
    (hr:(r:S)^2=w^3+q^4*A*w*u^4+q^6*B*u^6):
    q^3*u^3*(↑r⁻¹:S)-(q*u*w*(↑r⁻¹:S))^3-
      A*(q*u*w*(↑r⁻¹:S))*(q^3*u^3*(↑r⁻¹:S))^2-
      B*(q^3*u^3*(↑r⁻¹:S))^3=0:=by
  have hu:(r:S)*(↑r⁻¹:S)=1:=by
    exact congrArg (fun v:Sˣ=>(v:S)) (mul_inv_cancel r)
  have hinv:(r:S)^2*(↑r⁻¹:S)^3=(↑r⁻¹:S):=by
    calc
      (r:S)^2*(↑r⁻¹:S)^3=((r:S)*(↑r⁻¹:S))^2*(↑r⁻¹:S):=by ring
      _=(↑r⁻¹:S):=by rw [hu];ring
  linear_combination -(q^3*u^3)*hinv + (q^3*u^3*(↑r⁻¹:S)^3)*hr

@[expose] def infinityMap (a b c o:ℂ) (hab:b≠a) (u:S) (r:Sˣ)
    (hr:(r:S)^2=
      (1+algebraMap ℂ S (o-a)*u^2)*(1+algebraMap ℂ S (o-b)*u^2)*
        (1+algebraMap ℂ S (o-c)*u^2)):
    InfinityChart318.Ring
      (NormalizedLegendreProjectiveModel318.A (parameter a b c))
      (NormalizedLegendreProjectiveModel318.B (parameter a b c))→ₐ[ℂ]S:=
  InfinityChart318.lift _ _
    (algebraMap ℂ S (scale a b)*u*
      (1+algebraMap ℂ S (o-center a b c)*u^2)*(↑r⁻¹:S))
    (algebraMap ℂ S (scale a b)^3*u^3*(↑r⁻¹:S))
    (infinity_relation _ _ _ _ _ r (hr.trans (reciprocal_identity a b c o hab u)))

/-- On the full zero-parameter fiber the map is the actual projective
origin, independently of the eight separate source sign choices. -/
lemma point_at_infinity (a b c o:ℂ) (hab:b≠a) (u:S) (r:Sˣ) (hr)
    (f:S→ₐ[ℂ]ℂ) (hu:f u=0):
    f.comp (infinityMap a b c o hab u r hr)=
      InfinityChart318.origin
        (NormalizedLegendreProjectiveModel318.A (parameter a b c))
        (NormalizedLegendreProjectiveModel318.B (parameter a b c)):=by
  apply InfinityChart318.hom_ext <;>
    simp [infinityMap,AlgHom.comp_apply,hu]
end ThreeBranchLegendreInfinityAlgebra318
