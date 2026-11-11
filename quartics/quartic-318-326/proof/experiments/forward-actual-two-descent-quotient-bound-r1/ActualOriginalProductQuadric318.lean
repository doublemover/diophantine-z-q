module
public import ActualOriginalPeriodizationCoefficient318
public section
noncomputable section
namespace ActualOriginalProductQuadric318
open QuadricCRTAssembly318
set_option maxHeartbeats 16000000
variable {R S : Type*} [CommRing R] [CommRing S]

@[expose] def coordinateRingEquiv (e : R ≃+* S) : Coordinates R ≃ Coordinates S :=
  (e.toEquiv.prodCongr e.toEquiv).prodCongr
    ((e.toEquiv.prodCongr e.toEquiv).prodCongr e.toEquiv)

lemma coordinateRingEquiv_apply (e : R ≃+* S) (x : Coordinates R) :
    coordinateRingEquiv e x = mapCoordinates e.toRingHom x := rfl

/-- Transport of the EXACT original quadric along a ring equivalence,
with its coefficient identity supplied explicitly. -/
@[expose] def quadricRingEquiv (e : R ≃+* S) (κ : R) (λ : S) (h : e κ = λ) :
    Quadric κ ≃ Quadric λ :=
  (coordinateRingEquiv e).subtypeEquiv (fun x => by
    change equation κ x = 0 ↔ equation λ (mapCoordinates e.toRingHom x) = 0
    rw [←h,equation_map]
    constructor
    · intro hx
      rw [hx,map_zero]
    · intro hx
      apply e.injective
      simpa only [map_zero] using hx)

@[expose] def mergeCoordinates (x : Coordinates R) (y : Coordinates S) : Coordinates (R×S) :=
  (((x.1.1,y.1.1),(x.1.2,y.1.2)),((x.2.1.1,y.2.1.1),(x.2.1.2,y.2.1.2)),(x.2.2,y.2.2))

lemma actual_product_equation (κ : R) (λ : S) (x : Coordinates R) (y : Coordinates S) :
    equation (κ,λ) (mergeCoordinates x y) = (equation κ x,equation λ y) := rfl

/-- A solution over the literal product ring is exactly a pair of
solutions, with all five coordinates and both coefficient images retained. -/
@[expose] def productQuadricEquiv (κ : R) (λ : S) :
    Quadric (κ,λ) ≃ Quadric κ × Quadric λ where
  toFun x :=
    (⟨mapCoordinates (RingHom.fst R S) x.val,by
      have h := congrArg (RingHom.fst R S) x.property
      simpa only [←equation_map,map_zero] using h⟩,
     ⟨mapCoordinates (RingHom.snd R S) x.val,by
      have h := congrArg (RingHom.snd R S) x.property
      simpa only [←equation_map,map_zero] using h⟩)
  invFun xy := ⟨mergeCoordinates xy.1.val xy.2.val,by
    rw [actual_product_equation,xy.1.property,xy.2.property];rfl⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv xy := by apply Prod.ext <;> apply Subtype.ext <;> rfl

end ActualOriginalProductQuadric318
