module
public import OriginalCofactorCoordinates318
public section
noncomputable section
namespace OriginalAnisotropicRectangle318
open scoped RealInnerProductSpace
open TernaryQuadraticLineCover318 LiteralTernaryReduction318 OriginalEuclideanLattice318
open OriginalControlledIntegralBasis318 OriginalWholeBasisCoordinates318
open OriginalCofactorCoordinates318 OriginalThirdMinimumTail318
set_option maxHeartbeats 3500000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def inverseRadius (a b : Vector ℤ) (D : ℤ) (R : ℝ) : ℕ :=
  floorRadius (R*(‖embed a‖*‖embed b‖)/|(D:ℝ)|)

/-- Three separately scaled inverse-coordinate bounds on the actual
whole-lattice inverse. The floor is applied to each INTEGER coefficient,
not to the Euclidean length. -/
theorem inverse_rectangle (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (κ : ℤ) (t : ∀ i, Option (ZMod (p i))) (u v z : Vector ℤ)
    (hb : IntegralBasisTriple p κ t u v z)
    (huv : ‖embed u‖≤‖embed v‖) (hip : |⟪embed u,embed v⟫|≤‖embed u‖^2/2)
    (R : ℝ) (hR : 0≤R) (y : literalLattice p κ t) (hy : ‖embed y.val‖≤R) :
    let c := (wholeEquiv p κ t u v z hb).symm y
    let D := determinant u v z
    |c.1|≤(inverseRadius v z D R:ℤ) ∧
    |c.2.1|≤(inverseRadius z u D R:ℤ) ∧
    |c.2.2|≤(inverseRadius u v D R:ℤ) := by
  dsimp only
  have hD := determinant_ne_zero p hp κ t u v z hb huv hip
  obtain ⟨h1,h2,h3⟩ := inverse_cofactor_identities p κ t u v z hb y
  have bound (a b : Vector ℤ) (c : ℤ)
      (hc : LiteralIntegerDuality318.dot (OriginalIntegerNormalProjection318.normal a b) y=
        determinant u v z*c) :
      |c|≤(inverseRadius a b (determinant u v z) R:ℤ) := by
    have hnum : R*‖embed (OriginalIntegerNormalProjection318.normal a b)‖≤
        R*(‖embed a‖*‖embed b‖) := mul_le_mul_of_nonneg_left (cross_norm_le a b) hR
    apply integral_coordinate_floor c _ (by positivity)
    exact (coefficient_bound _ _ _ _ hD hc R hy).trans
      (div_le_div_of_nonneg_right hnum (abs_nonneg _))
  exact ⟨bound v z _ h1,bound z u _ h2,bound u v _ h3⟩

@[expose] def coordinateCode (A : ℕ) (c : ℤ) (hc : |c|≤(A:ℤ)) : Fin (2*A+1) :=
  ⟨(c+(A:ℤ)).toNat,by obtain ⟨hlo,hhi⟩ := abs_le.mp hc; omega⟩

lemma coordinateCode_injective (A : ℕ) (c d : ℤ)
    (hc : |c|≤(A:ℤ)) (hd : |d|≤(A:ℤ))
    (he : coordinateCode A c hc=coordinateCode A d hd) : c=d := by
  have he' := congrArg Fin.val he
  change (c+(A:ℤ)).toNat=(d+(A:ℤ)).toNat at he'
  obtain ⟨hc0,hc1⟩ := abs_le.mp hc
  obtain ⟨hd0,hd1⟩ := abs_le.mp hd
  omega

@[expose] def NormPoints (p : ι → ℕ) (κ : ℤ) (t : ∀ i, Option (ZMod (p i))) (R : ℝ) :=
  {y : literalLattice p κ t // ‖embed y.val‖≤R}

/-- Quantitative point bound by the ACTUAL anisotropic inverse rectangle.
Every point has unique integer coefficients, so there is no discarded
multiplicity or unsupported passage from covolume alone to a count. -/
theorem original_norm_point_bound (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (κ : ℤ) (t : ∀ i, Option (ZMod (p i))) (u v z : Vector ℤ)
    (hb : IntegralBasisTriple p κ t u v z)
    (huv : ‖embed u‖≤‖embed v‖) (hip : |⟪embed u,embed v⟫|≤‖embed u‖^2/2)
    (R : ℝ) (hR : 0≤R) :
    let D := determinant u v z
    Nat.card (NormPoints p κ t R)≤
      (2*inverseRadius v z D R+1)*(2*inverseRadius z u D R+1)*(2*inverseRadius u v D R+1) := by
  classical
  let D := determinant u v z
  let A := inverseRadius v z D R
  let B := inverseRadius z u D R
  let C := inverseRadius u v D R
  let e := wholeEquiv p κ t u v z hb
  have hbds (y : NormPoints p κ t R) := inverse_rectangle p hp κ t u v z hb huv hip R hR y.1 y.2
  let f : NormPoints p κ t R → Fin (2*A+1)×Fin (2*B+1)×Fin (2*C+1) := fun y =>
    (coordinateCode A (e.symm y.1).1 (hbds y).1,
      coordinateCode B (e.symm y.1).2.1 (hbds y).2.1,
      coordinateCode C (e.symm y.1).2.2 (hbds y).2.2)
  have hi : Function.Injective f := by
    intro y y' he
    have h1 := congrArg Prod.fst he
    have h2 := congrArg (fun x : Fin (2*A+1)×Fin (2*B+1)×Fin (2*C+1) => x.2.1) he
    have h3 := congrArg (fun x : Fin (2*A+1)×Fin (2*B+1)×Fin (2*C+1) => x.2.2) he
    have hc : e.symm y.1=e.symm y'.1 := Prod.ext
      (coordinateCode_injective A _ _ _ _ h1)
      (Prod.ext (coordinateCode_injective B _ _ _ _ h2) (coordinateCode_injective C _ _ _ _ h3))
    exact Subtype.ext (e.symm.injective hc)
  have hh := Nat.card_le_card_of_injective f hi
  simpa only [Nat.card_eq_fintype_card,Fintype.card_prod,Fintype.card_fin,mul_assoc] using hh

/-- The entire inverse-rectangle construction is instantiated with the
constructed reduced whole basis, not a caller-supplied lattice basis. -/
theorem actual_inverse_rectangle (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (κ : ℤ) (t : ∀ i, Option (ZMod (p i))) :
    ∃ u v w z : Vector ℤ, IntegralBasisTriple p κ t u v z ∧
      ‖embed z‖≤2*‖embed w‖ ∧ determinant u v z≠0 ∧
      ∀ R : ℝ, 0≤R → Nat.card (NormPoints p κ t R)≤
        (2*inverseRadius v z (determinant u v z) R+1)*
        (2*inverseRadius z u (determinant u v z) R+1)*
        (2*inverseRadius u v (determinant u v z) R+1) := by
  obtain ⟨u,v,w,z,hi,hb,huv,hvw,hip,hz,humin,hvmin,hwmin⟩ := actual_controlled_basis p hp κ t
  exact ⟨u,v,w,z,hb,hz,determinant_ne_zero p hp κ t u v z hb huv hip,
    fun R hR => original_norm_point_bound p hp κ t u v z hb huv hip R hR⟩

end OriginalAnisotropicRectangle318
