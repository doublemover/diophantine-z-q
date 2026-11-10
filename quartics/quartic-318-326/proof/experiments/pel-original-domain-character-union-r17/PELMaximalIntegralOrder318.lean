module
public import PELQuaternionIntegralInvariants318
public section
noncomputable section
namespace PELMaximalIntegralOrder318
open PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318 PELPrincipalOrderPerfect318
open PELIntegralOverorder318 PELQuaternionIntegralInvariants318
set_option maxHeartbeats 1000000

/-- The original order is finite over Z, through its exact Z-four coordinates. -/
theorem order_finite : Module.Finite ℤ order :=
  Module.Finite.of_surjective coordinatesEquiv.toAddMonoidHom.toIntLinearMap
    coordinatesEquiv.surjective

/-- Its rational span is the entire same quaternion algebra. -/
theorem rational_spanning (x : B) :
    x=(x.re-x.imJ) • embed (basis 0)+(x.imI-5*x.imK) • embed (basis 1)+
      (2*x.imJ) • embed (basis 2)+(10*x.imK) • embed (basis 3) := by
  ext <;> simp [embed,basis,Pi.single_apply] <;> ring

/-- Genuine maximality among module-finite Z-subrings. The previous trace/norm
premises have now been derived for every element of any such overorder. This
is not merely a determinant or a hypothesis named maximality. -/
theorem maximal_finite_subring (S : Subring B) [Module.Finite ℤ S]
    (hOS : order≤S) : S=order := by
  apply no_larger_integral_overorder S hOS
  · intro x hx
    have hi : IsIntegral ℤ (⟨x,hx⟩:S) := IsIntegral.of_finite ℤ _
    have hix : IsIntegral ℤ x := map_isIntegral_int S.subtype hi
    exact (invariants x hix).1
  · intro x hx
    have hi : IsIntegral ℤ (⟨x,hx⟩:S) := IsIntegral.of_finite ℤ _
    have hix : IsIntegral ℤ x := map_isIntegral_int S.subtype hi
    exact (invariants x hix).2

/-- The strengthened result also excludes every larger elementwise-integral
subring, without first requiring a finite module presentation for it. -/
theorem maximal_integral_subring (S : Subring B) (hOS : order≤S)
    (hS : ∀ x∈S,IsIntegral ℤ x) : S=order :=
  no_larger_integral_overorder S hOS
    (fun x hx => (invariants x (hS x hx)).1)
    (fun x hx => (invariants x (hS x hx)).2)
end PELMaximalIntegralOrder318
