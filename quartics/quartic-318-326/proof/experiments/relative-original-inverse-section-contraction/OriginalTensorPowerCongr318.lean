module
public import LineSheafTensorPower318
public import TensorSheafFunctor318
public section
noncomputable section
namespace OriginalTensorPowerCongr318
open AlgebraicGeometry CategoryTheory
universe u
variable {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
/-- Actual iterated tensor-sheaf comparison induced by a specified original
isomorphism, without changing any of the underlying tensor objects. -/
@[expose] def iso : ∀ n : ℕ,
    FramedLineTensorPower318.object M n ≅ FramedLineTensorPower318.object N n
  | 0 => Iso.refl _
  | n+1 => TensorSheafFunctor318.congr (iso e n) e
end OriginalTensorPowerCongr318
