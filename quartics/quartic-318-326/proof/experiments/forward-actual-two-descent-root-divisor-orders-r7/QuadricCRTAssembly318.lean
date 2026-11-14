module
public import FixedSquarefreeCRT318
public section
noncomputable section
namespace QuadricCRTAssembly318
open scoped BigOperators
set_option maxHeartbeats 1000000

@[expose] def Coordinates (R : Type*) := (R×R)×(R×R)×R
@[expose] def equation {R : Type*} [CommRing R] (κ : R) (z : Coordinates R) : R :=
  z.1.1^2+z.1.2^2-(z.2.1.1^2+z.2.1.2^2)-κ*z.2.2^2
@[expose] def Quadric {R : Type*} [CommRing R] (κ : R) :=
  {z : Coordinates R // equation κ z=0}
@[expose] def mapCoordinates {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (z : Coordinates R) : Coordinates S :=
  ((f z.1.1,f z.1.2),(f z.2.1.1,f z.2.1.2),f z.2.2)
lemma equation_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (κ : R) (z : Coordinates R) :
    equation (f κ) (mapCoordinates f z)=f (equation κ z) := by
  simp only [equation,mapCoordinates,map_sub,map_add,map_pow,map_mul]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hd : Function.Injective p)

@[expose] def coordsEquiv : Coordinates (ZMod (FixedSquarefreeCRT318.modulus p)) ≃
    (∀ i : ι, Coordinates (ZMod (p i))) where
  toFun z i := mapCoordinates (FixedSquarefreeCRT318.component p i) z
  invFun z :=
    let e := FixedSquarefreeCRT318.ringEquiv p hp hd
    ((e.symm (fun i => (z i).1.1),e.symm (fun i => (z i).1.2)),
     (e.symm (fun i => (z i).2.1.1),e.symm (fun i => (z i).2.1.2)),
     e.symm (fun i => (z i).2.2))
  left_inv z := by
    rcases z with ⟨⟨a,b⟩,⟨c,d⟩,w⟩
    let e := FixedSquarefreeCRT318.ringEquiv p hp hd
    change ((e.symm (e a),e.symm (e b)),(e.symm (e c),e.symm (e d)),e.symm (e w))=
      ((a,b),(c,d),w)
    simp only [RingEquiv.symm_apply_apply]
  right_inv z := by
    funext i
    let e := FixedSquarefreeCRT318.ringEquiv p hp hd
    change ((e (e.symm (fun j => (z j).1.1)) i,e (e.symm (fun j => (z j).1.2)) i),
      (e (e.symm (fun j => (z j).2.1.1)) i,e (e.symm (fun j => (z j).2.1.2)) i),
      e (e.symm (fun j => (z j).2.2)) i)=z i
    simp only [RingEquiv.apply_symm_apply]

@[expose] def quadricEquiv (κ : ℤ) :
    Quadric (κ : ZMod (FixedSquarefreeCRT318.modulus p)) ≃
      (∀ i : ι, Quadric (κ : ZMod (p i))) where
  toFun z i := ⟨coordsEquiv p hp hd z.1 i,by
    change equation (κ : ZMod (p i)) (mapCoordinates (FixedSquarefreeCRT318.component p i) z.1)=0
    rw [←map_intCast (FixedSquarefreeCRT318.component p i) κ,equation_map,z.2,map_zero]⟩
  invFun z := ⟨(coordsEquiv p hp hd).symm (fun i => (z i).1),by
    apply (FixedSquarefreeCRT318.ringEquiv p hp hd).injective
    funext i
    change FixedSquarefreeCRT318.component p i (equation _ _)=0
    rw [←equation_map,map_intCast]
    change equation (κ : ZMod (p i))
      (coordsEquiv p hp hd ((coordsEquiv p hp hd).symm (fun j => (z j).1)) i)=0
    rw [Equiv.apply_symm_apply]
    exact (z i).2⟩
  left_inv z := by
    apply Subtype.ext
    exact (coordsEquiv p hp hd).symm_apply_apply z.1
  right_inv z := by
    funext i
    apply Subtype.ext
    exact congrFun ((coordsEquiv p hp hd).apply_symm_apply (fun j => (z j).1)) i

/-- Actual congruence conditions on the single original quadric modulo the
product, not an abstract product set substituted for the original source. -/
@[expose] def Admissible (κ : ℤ) (Ω : ∀ i, Set (Quadric (κ : ZMod (p i)))) :=
  {z : Quadric (κ : ZMod (FixedSquarefreeCRT318.modulus p)) //
    ∀ i, quadricEquiv p hp hd κ z i∈Ω i}

@[expose] def admissibleEquiv (κ : ℤ) (Ω : ∀ i, Set (Quadric (κ : ZMod (p i)))) :
    Admissible p hp hd κ Ω ≃ (∀ i, Ω i) where
  toFun z i := ⟨quadricEquiv p hp hd κ z.1 i,z.2 i⟩
  invFun z := ⟨(quadricEquiv p hp hd κ).symm (fun i => (z i).1),by
    intro i
    rw [Equiv.apply_symm_apply]
    exact (z i).2⟩
  left_inv z := by apply Subtype.ext; exact (quadricEquiv p hp hd κ).symm_apply_apply z.1
  right_inv z := by
    funext i
    apply Subtype.ext
    exact congrFun ((quadricEquiv p hp hd κ).apply_symm_apply (fun j => (z j).1)) i

/-- Exact multiplication of any prescribed local conditions, including
conditions that exclude the origin separately at every prime. -/
theorem admissible_card (κ : ℤ) (Ω : ∀ i, Set (Quadric (κ : ZMod (p i)))) :
    Nat.card (Admissible p hp hd κ Ω)=∏ i, Nat.card (Ω i) := by
  classical
  letI : ∀ i, NeZero (p i) := fun i => ⟨(hp i).ne_zero⟩
  letI : ∀ i, Fintype (Quadric (κ : ZMod (p i))) := fun i =>
    inferInstanceAs (Fintype {z : Coordinates (ZMod (p i)) // equation (κ : ZMod (p i)) z=0})
  rw [Nat.card_congr (admissibleEquiv p hp hd κ Ω)]
  simp only [Nat.card_eq_fintype_card,Fintype.card_pi]

end QuadricCRTAssembly318
