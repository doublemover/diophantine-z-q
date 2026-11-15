module
public import PELOriginalRamifiedDivision318
public section
noncomputable section
namespace PELRamifiedPrimitiveCongruence318
open PELPrincipalOrderCoordinates318 PELPrimeNormalizerData318 PELLevelThreeSimilitudes318
open PELOriginalRamifiedDivision318 PELOriginalRamifiedSquare318 PELOriginalRamifiedResidues318
open PELOriginalRamifiedKernels318 PELPrimeLatticeResidues318
set_option maxHeartbeats 1800000

/-- Twice the original uniformizer depth forces every original order
coordinate divisible byp; the argument uses the actual P²=pO producer. -/
theorem square_norm_forces_coordinate_division (i : Fin 4) (a : Coordinates)
    (h : (prime i:ℤ)^2∣integralNorm a) : ∀ j : Fin 4,(prime i:ℤ)∣a j := by
  obtain ⟨y,hy⟩ := (actual_prime_power_division i 2 (coordinatesEquiv a)).mp
    (by simpa only [orderNorm,AddEquiv.symm_apply_apply] using h)
  have hx : reduction i (y*uniformizer i)=0 := by
    change rightMultiply i y∈(reduction i).toAddMonoidHom.ker
    rw [actual_kernel]
    exact ⟨y,rfl⟩
  have hn : reduction i (uniformizer i)=0 := by
    have hh : rightMultiply i 1∈(reduction i).toAddMonoidHom.ker := by
      rw [actual_kernel]
      exact ⟨1,rfl⟩
    change reduction i (1*uniformizer i)=0 at hh
    simpa only [one_mul] using hh
  obtain ⟨z,hz⟩ := kernel_product i (y*uniformizer i) (uniformizer i) hx hn
  have he : coordinatesEquiv a=(prime i) • z := by
    rw [←hy,pow_two,←mul_assoc]
    exact hz
  have hc : a=(prime i) • coordinatesEquiv.symm z := by
    apply coordinatesEquiv.injective
    rw [map_nsmul,AddEquiv.apply_symm_apply]
    exact he
  intro j
  refine ⟨coordinatesEquiv.symm z j,?_⟩
  simpa only [Pi.smul_apply,nsmul_eq_mul] using congrFun hc j

@[expose] def polynomial {R : Type*} [CommRing R] (a : Fin 4 → R) : R :=
  a 0^2+a 0*a 2+210*a 1^2+210*a 1*a 3-a 2^2+42*a 3^2

theorem polynomial_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a : Fin 4 → R) : f (polynomial a)=polynomial (fun j => f (a j)) := by
  simp [polynomial]

theorem polynomial_scale {R : Type*} [CommRing R] (q : R) (a : Fin 4 → R) :
    polynomial (fun j => q*a j)=q^2*polynomial a := by unfold polynomial; ring

/-- A zero of the ORIGINAL norm polynomial in any ring admitting the
actual mod-p² map cannot have a coordinate equal to1. All four coordinate
lifts are constructed; no p-adic anisotropy theorem is assumed. -/
theorem zero_has_no_one {R : Type*} [CommRing R] (i : Fin 4)
    (f : R →+* ZMod ((prime i)^2)) (a : Fin 4 → R)
    (ha : polynomial a=0) (j : Fin 4) : a j≠1 := by
  intro hj
  choose A hA using (fun k : Fin 4 => ZMod.intCast_surjective (f (a k)))
  have hzero : polynomial (fun k => (A k:ZMod ((prime i)^2)))=0 := by
    have hh := (polynomial_map f a).symm.trans ((congrArg f ha).trans (map_zero f))
    simpa only [hA] using hh
  have hN : (prime i:ℤ)^2∣integralNorm A := by
    have hh : (integralNorm A:ZMod ((prime i)^2))=0 :=
      (polynomial_map (Int.castRingHom _) A).trans hzero
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd (integralNorm A) ((prime i)^2)).mp hh
    simpa only [Nat.cast_pow] using hd
  have hdA := square_norm_forces_coordinate_division i A hN j
  have hdiff : (((prime i)^2:ℕ):ℤ)∣(A j-1) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (A j-1) ((prime i)^2)).mp
    push_cast
    rw [hA j,hj,map_one,sub_self]
  have hpdiff : (prime i:ℤ)∣A j-1 := by
    have hp2 : (prime i:ℤ)∣(prime i:ℤ)^2 := ⟨prime i,by ring⟩
    exact hp2.trans (by simpa only [Nat.cast_pow] using hdiff)
  have hone : (prime i:ℤ)∣1 := by
    have hh := hdA.sub hpdiff
    convert hh using 1 <;> ring
  fin_cases i <;> norm_num [prime] at hone
end PELRamifiedPrimitiveCongruence318
