module
public import FiniteCongruenceSwitchPairing318
public section
noncomputable section
namespace ActualOriginalCoordinateBump318
open QuadricCRTAssembly318
set_option maxHeartbeats 26000000

@[expose] def coordinate {R : Type*} (x : Coordinates R) (i : Fin 4) : R :=
  ![x.1.1,x.1.2,x.2.1.1,x.2.1.2] i
@[expose] def sign {R : Type*} [CommRing R] (i : Fin 4) : R := if i.val<2 then 1 else -1
@[expose] def bump {R : Type*} [CommRing R] (i : Fin 4) (d : R) (x : Coordinates R) : Coordinates R :=
  if i=0 then ((x.1.1+d,x.1.2),x.2.1,x.2.2)
  else if i=1 then ((x.1.1,x.1.2+d),x.2.1,x.2.2)
  else if i=2 then (x.1,(x.2.1.1+d,x.2.1.2),x.2.2)
  else (x.1,(x.2.1.1,x.2.1.2+d),x.2.2)

lemma original_bump_equation {R : Type*} [CommRing R] (κ : R) (i : Fin 4)
    (d : R) (x : Coordinates R) :
    equation κ (bump i d x)-equation κ x=sign i*(2*coordinate x i*d+d^2) := by
  fin_cases i <;> simp [bump,coordinate,sign,equation] <;> ring
lemma bump_add {R : Type*} [CommRing R] (i : Fin 4) (d e : R) (x : Coordinates R) :
    bump i e (bump i d x)=bump i (d+e) x := by
  fin_cases i <;> simp [bump,add_assoc]
lemma bump_zero {R : Type*} [CommRing R] (i : Fin 4) (x : Coordinates R) : bump i 0 x=x := by
  fin_cases i <;> simp [bump]
lemma bump_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (i : Fin 4) (d : R) (x : Coordinates R) :
    mapCoordinates f (bump i d x)=bump i (f d) (mapCoordinates f x) := by
  fin_cases i <;> simp [bump,mapCoordinates,map_add]
lemma coordinate_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (x : Coordinates R) (i : Fin 4) : coordinate (mapCoordinates f x) i=f (coordinate x i) := by
  fin_cases i <;> rfl

end ActualOriginalCoordinateBump318
