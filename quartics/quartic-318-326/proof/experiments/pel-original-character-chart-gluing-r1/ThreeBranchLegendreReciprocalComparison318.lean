module
public import ThreeBranchLegendreInfinityAlgebra318
public section
noncomputable section
namespace ThreeBranchLegendreReciprocalComparison318
open ThreeBranchLegendreInfinityAlgebra318 ThreeBranchLegendrePolynomial318
set_option maxHeartbeats 800000
variable {S:Type*} [CommRing S] [Algebra ℂ S]
variable (a b c o:ℂ) (hab:b≠a) (u r:Sˣ)

/-- Inverting the actual source parameter gives exactly the affine
coordinates of the SAME selected cubic change, not just some Legendre
equation with the same j-invariant. Both ordinate and abscissa are fixed. -/
theorem coordinate_identities:
    (algebraMap ℂ S (scale a b)*(u:S)*
      (1+algebraMap ℂ S (o-center a b c)*(u:S)^2)*(↑r⁻¹:S)=
      (algebraMap ℂ S (b-a)⁻¹*
        (algebraMap ℂ S o+(↑u⁻¹:S)^2-algebraMap ℂ S (center a b c)))*
      (algebraMap ℂ S (scale a b)^3*(u:S)^3*(↑r⁻¹:S))) ∧
    ((algebraMap ℂ S (rootScale a b)⁻¹*(r:S)*(↑u⁻¹:S)^3)*
      (algebraMap ℂ S (scale a b)^3*(u:S)^3*(↑r⁻¹:S))=1):=by
  have hu:(u:S)*(↑u⁻¹:S)=1:=congrArg (fun z:Sˣ=>(z:S)) (mul_inv_cancel u)
  have hr:(r:S)*(↑r⁻¹:S)=1:=congrArg (fun z:Sˣ=>(z:S)) (mul_inv_cancel r)
  have hd:algebraMap ℂ S (b-a)⁻¹*algebraMap ℂ S (scale a b)^2=1:=by
    rw [←map_pow,←map_mul,scale_square a b hab,inv_mul_cancel₀ (sub_ne_zero.mpr hab),map_one]
  have hv:algebraMap ℂ S (rootScale a b)⁻¹*algebraMap ℂ S (scale a b)^3=1:=by
    rw [←map_pow,←map_mul,scale_cube a b hab,
      inv_mul_cancel₀ (rootScale_ne_zero a b hab),map_one]
  constructor
  · symm
    calc
      _=algebraMap ℂ S (scale a b)*(u:S)*(↑r⁻¹:S)*
        (algebraMap ℂ S (b-a)⁻¹*algebraMap ℂ S (scale a b)^2)*
        ((algebraMap ℂ S o-algebraMap ℂ S (center a b c))*(u:S)^2+
          ((u:S)*(↑u⁻¹:S))^2):=by ring
      _=_:=by rw [hd,hu,map_sub];ring
  · calc
      _=(algebraMap ℂ S (rootScale a b)⁻¹*algebraMap ℂ S (scale a b)^3)*
        ((r:S)*(↑r⁻¹:S))*((u:S)*(↑u⁻¹:S))^3:=by ring
      _=1:=by rw [hv,hr,hu];ring
end ThreeBranchLegendreReciprocalComparison318
