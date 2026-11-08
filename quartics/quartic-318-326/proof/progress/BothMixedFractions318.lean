module
public import BothMixedPolynomial318
public section
namespace BothMixedFractions318
open InfinityInputPolynomial318 InfinityVietaAlgebra318
set_option maxHeartbeats 700000
variable {R:Type*} [CommRing R]

/-- Denominator cancellation uses only the three displayed units. -/
theorem transition (A B u v x y a b U V i:R)
    (hf:y^2-x^3-A*x-B=0) (hg:v-u^3-A*u*v^2-B*v^3=0)
    (hl:v-a*u-b=0) (hm:1-a*x-b*y=0)
    (hc:IsUnit (c A B a)) (hy:IsUnit y)
    (hU:c A B a*y*U=(u*y+x)*c A B a+d A B a b*y)
    (hV:V=a*U-b)
    (hi:denominator (1-A*u*v-B*v^2) u x*i=1) :
    U*(numeratorY A B (1-A*u*v-B*v^2) u x y*i^3)=
      numeratorX A B (1-A*u*v-B*v^2) u x y*i^2 ∧
    V*(numeratorY A B (1-A*u*v-B*v^2) u x y*i^3)=1 := by
  let H:=denominator (1-A*u*v-B*v^2) u x
  let NX:=numeratorX A B (1-A*u*v-B*v^2) u x y
  let NY:=numeratorY A B (1-A*u*v-B*v^2) u x y
  have hx:U*NY=NX*H := by
    apply (hc.mul hy).mul_left_cancel
    calc
      _=(c A B a*y*U)*NY := by ring
      _=((u*y+x)*c A B a+d A B a b*y)*NY := by rw [hU]
      _=c A B a*y*(NX*H) := by
        simpa only [NX,NY,H,mul_assoc] using BothMixedPolynomial318.x_identity A B u v x y a b hf hg hl hm
  have hv:V*NY=H^3 := by
    apply (hc.mul hy).mul_left_cancel
    calc
      _=(a*(c A B a*y*U)-b*c A B a*y)*NY := by rw [hV]; ring
      _=(a*((u*y+x)*c A B a+d A B a b*y)-b*c A B a*y)*NY := by rw [hU]
      _=c A B a*y*H^3 := BothMixedPolynomial318.y_identity A B u v x y a b hf hg hl hm
  change U*(NY*i^3)=NX*i^2 ∧ V*(NY*i^3)=1
  constructor
  · calc
      _=(U*NY)*i^3 := by ring
      _=NX*(H*i)*i^2 := by rw [hx]; ring
      _=NX*i^2 := by rw [hi,mul_one]
  · calc
      _=(V*NY)*i^3 := by ring
      _=(H*i)^3 := by rw [hv]; ring
      _=1 := by rw [hi,one_pow]
end BothMixedFractions318
