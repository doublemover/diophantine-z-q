module
public import FramedLineTensorPower318
public section
noncomputable section
namespace OriginalTensorPowerCongruence318
open AlgebraicGeometry CategoryTheory
universe u
variable {X : Scheme.{u}} {M N : X.Modules}

/-- Functorial isomorphisms of the genuine iterated tensor sheaves. -/
def iso (e : M ≅ N) : (n : ℕ) →
    FramedLineTensorPower318.object M n ≅ FramedLineTensorPower318.object N n
  | 0 => Iso.refl _
  | n+1 => TensorSheafFunctor318.congr (iso e n) e

lemma zero (e : M ≅ N) : iso e 0 = Iso.refl _ := rfl
lemma succ (e : M ≅ N) (n : ℕ) :
    iso e (n+1) = TensorSheafFunctor318.congr (iso e n) e := rfl
end OriginalTensorPowerCongruence318
