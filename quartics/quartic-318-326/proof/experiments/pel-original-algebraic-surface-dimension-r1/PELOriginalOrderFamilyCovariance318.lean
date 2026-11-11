module
public import PELOriginalTwoOrderPairing318
public section
noncomputable section
namespace PELOriginalOrderFamilyCovariance318
open AlgebraicGeometry CategoryTheory LineSheafClass318 PELPrincipalOrderCoordinates318
open PELOriginalProductChartCover318 PELOriginalSchemePointGroup318
open PELOriginalNormalizedPolarizationFamily318 PELOriginalOrderHermitianAdjoint318
variable (τ : ℂ) (hτ : 0 < τ.im) (a b : order)
/-- The actual simultaneous order action on the complete scheme product. -/
@[expose] def map : Product τ hτ⟶Product τ hτ :=
  pairMap τ hτ (baseMap τ hτ)
    (PELOriginalUniversalOrderAction318.endomorphism τ hτ (baseMap τ hτ) a (firstPoint τ hτ))
    (PELOriginalUniversalOrderAction318.endomorphism τ hτ (baseMap τ hτ) b (secondPoint τ hτ))
@[expose] def leftLine : Line (Product τ hτ) :=
  LineSheafPullback318.line (map τ hτ a b) (family τ hτ)
@[expose] def rightLine : Line (Product τ hτ) :=
  LineSheafPullback318.line (map τ hτ 1 (adjoint a*b)) (family τ hτ)
lemma class_equation : classOf (leftLine τ hτ a b)=classOf (rightLine τ hτ a b) := by
  change classOf (LineSheafPullback318.line (map τ hτ a b) (family τ hτ))=
    classOf (LineSheafPullback318.line (map τ hτ 1 (adjoint a*b)) (family τ hτ))
  rw [map,map,pair_class,pair_class,PELOriginalTwoOrderPairing318.covariance]
  have h := map_one (PELOriginalUniversalOrderAction318.ringAction τ hτ (baseMap τ hτ))
  have he := congrArg (fun f : AddMonoid.End (Points τ hτ (Product τ hτ) (baseMap τ hτ)) =>
    f (firstPoint τ hτ)) h
  change PELOriginalUniversalOrderAction318.endomorphism τ hτ (baseMap τ hτ) 1
    (firstPoint τ hτ)=firstPoint τ hτ at he
  rw [he]
/-- Whole-product sheaf comparison, constructed from the actual
noncommutative action and the actual normalized polarization family. -/
@[expose] def iso : (leftLine τ hτ a b).object ≅ (rightLine τ hτ a b).object :=
  Classical.choice ((classOf_eq_iff _ _).mp (class_equation τ hτ a b))
lemma hom_inv : (iso τ hτ a b).hom≫(iso τ hτ a b).inv=𝟙 _ :=
  (iso τ hτ a b).hom_inv_id
lemma inv_hom : (iso τ hτ a b).inv≫(iso τ hτ a b).hom=𝟙 _ :=
  (iso τ hτ a b).inv_hom_id
end PELOriginalOrderFamilyCovariance318
