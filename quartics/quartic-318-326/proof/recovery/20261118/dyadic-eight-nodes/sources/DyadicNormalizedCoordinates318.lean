module
public import FivePointBlowupEquations318
public section
noncomputable section
namespace DyadicNormalizedCoordinates318
open FivePointBlowupEquations318

/-- The proposed half-root differences live first in the original
characteristic-zero field. Their displayed monic equations, not the
inversion of 2 in the integral ring, justify adjoining them integrally. -/
theorem finite_relations {F : Type*} [Field F] [CharZero F] (g : H →+* F) :
    let u := g (r 0)
    let h := (g (r 1)-u)/2
    let k := (g (r 2)-u)/2
    let w := g (r 3)-u-1
    h^2 + u*h + 8 = 0 ∧ k^2 + u*k + 19208 = 0 ∧
    w^2 + 2*((u+1)*w+u-171) = 0 := by
  dsimp only
  obtain ⟨h0,h2,h3⟩ := mapped g
  constructor
  · linear_combination -(1/4:F)*h0
  constructor
  · linear_combination (1/4:F)*(h2-h0)
  · linear_combination h3 - h0

/-- At the reciprocal boundary the first two normalized ratios also
admit INTEGRAL half-ratio generators. The last translated ratio is not
divided by 2. These are algebraic identities, not blowup/regularity joins. -/
theorem reciprocal_relations {F : Type*} [Field F] [CharZero F]
    (x b c e : F) (hb : b^2=1-32*x^2) (hc : c^2=1-76832*x^2)
    (he : e^2=1+343*x^2) :
    let h := (b-1)/2
    let k := (c-1)/2
    let w := e-1-x
    h^2+h+8*x^2=0 ∧ k^2+k+19208*x^2=0 ∧
    w^2+2*((1+x)*w+x-171*x^2)=0 := by
  dsimp only
  constructor
  · linear_combination (1/4:F)*hb
  constructor
  · linear_combination (1/4:F)*hc
  · linear_combination he

end DyadicNormalizedCoordinates318
