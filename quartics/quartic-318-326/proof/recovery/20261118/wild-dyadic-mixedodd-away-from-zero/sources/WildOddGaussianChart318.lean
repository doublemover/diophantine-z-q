module
public import Mathlib.Tactic
public section
namespace WildOddGaussianChart318
variable {F : Type*} [Field F] [CharZero F]

theorem cleared_gaussian_coordinate (pi U Z a b : F) :
    (pi*Z+U+1)^2-(a*U^2+b) =
      pi^2*Z^2+2*pi*(U+1)*Z+(1-a)*U^2+2*U+(1-b) := by ring

theorem residue_square_shift (h : F) :
    (1+2*h)^2=1+4*(h^2+h) := by ring
end WildOddGaussianChart318
