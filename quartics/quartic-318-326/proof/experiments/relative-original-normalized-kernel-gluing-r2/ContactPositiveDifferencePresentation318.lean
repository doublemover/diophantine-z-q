module
public import ContactPositiveDifferenceCover318
public section
noncomputable section
namespace ContactPositiveDifferencePresentation318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactPositiveDifferenceTwists318 RelativeClassSheafPoint318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
local notation "q" => ContactRelativeStructuralHOne318.projection R c
/-- Every original line on EVERY affine coefficient test is fppf-locally
the actual difference of TWO bounded effective Cartier families from
the constructed varying-divisor moduli. Both whole ideals and numerical
bounds are produced, and the original relative sheaf class is recovered.
This is a concrete local presentation, not representability of its quotient. -/
theorem exists_bounded_difference : ∃ (T : Scheme.{0}) (t : T ⟶ Spec R),
    Flat t ∧ Surjective t ∧ LocallyOfFinitePresentation t ∧
    ∃ (N M : ℕ) (D : ContactBoundedCartierEquiv318.Data c N (t ≫ baseMap R))
      (E : ContactBoundedCartierEquiv318.Data c M (t ≫ baseMap R)),
      value q t (OriginalLineAbelTransformation318.point q t
        (LineSheafPullback318.line (RelativeAmbientReassociation318.comparison p (baseMap R) t).hom
          (ContactCartierDifferenceLine318.line c N M (t ≫ baseMap R) D E)))=
        value q t (original q t (classOf L)) := by
  obtain ⟨n,hA,hB,hf,hs,hp⟩ := ContactPositiveDifferenceCover318.exists_cover R c L
  let A := numerator R c L n
  let B := denominator R c n
  let t := ContactNormalizedPairData318.projection R c A B hA hB
  refine ⟨ContactNormalizedPairData318.space R c A B hA hB,t,hf,hs,hp,
    ContactNormalizedPairData318.firstBound R c A hA,
    ContactNormalizedPairData318.secondBound R c B hB,
    ContactNormalizedPairData318.firstData R c A B hA hB,
    ContactNormalizedPairData318.secondData R c A B hA hB,?_⟩
  have he := congrArg (RelativeLineClassQuotient318.classMap (pullback.snd q t))
    (ContactNormalizedPairDifference318.absolute_class R c A B hA hB)
  change OriginalLineAbelTransformation318.point q t (ContactNormalizedPairClass318.line R c A B hA hB)=_ at he
  rw [←he,ContactNormalizedPairClass318.value_difference]
  rw [class_difference]
end ContactPositiveDifferencePresentation318
