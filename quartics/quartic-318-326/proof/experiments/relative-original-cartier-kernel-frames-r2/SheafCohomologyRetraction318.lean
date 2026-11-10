module
public import StructureAdditiveSheaf318
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Topology.Sheaves.Abelian

public section
noncomputable section
namespace SheafCohomologyRetraction318
open AlgebraicGeometry CategoryTheory
open StructureAdditiveSheaf318
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : Scheme} (f : X ⟶ Y)

/-- Genuine derived-functor sheaf cohomology of the original additive structure sheaf. -/
abbrev structureH (Y : Scheme) (n : ℕ) := Sheaf.H (sheaf Y) n

/-- Cohomology on Y with the actual direct image f_*O_X as coefficients.
This is not redefined to be H^n(X,O_X). -/
abbrev pushedH (n : ℕ) := Sheaf.H (pushed f) n

@[expose] def pullback (n : ℕ) : structureH Y n →+ pushedH f n :=
  Sheaf.H.map (StructureAdditiveSheaf318.pullback f) n

@[expose] def transfer (r : pushed f ⟶ sheaf Y) (n : ℕ) :
    pushedH f n →+ structureH Y n := Sheaf.H.map r n

/-- The full sheaf retraction induces a retraction in every cohomological degree. -/
theorem transfer_pullback (r : pushed f ⟶ sheaf Y)
    (h : StructureAdditiveSheaf318.pullback f ≫ r = 𝟙 (sheaf Y))
    (n : ℕ) (x : structureH Y n) : transfer f r n (pullback f n x) = x := by
  change Sheaf.H.map r n (Sheaf.H.map (StructureAdditiveSheaf318.pullback f) n x) = x
  rw [← Sheaf.H.map_comp_apply, h]
  exact Sheaf.H.map_id_apply x

theorem pullback_injective (r : pushed f ⟶ sheaf Y)
    (h : StructureAdditiveSheaf318.pullback f ≫ r = 𝟙 (sheaf Y)) (n : ℕ) :
    Function.Injective (pullback f n) :=
  Function.LeftInverse.injective (transfer_pullback f r h n)

theorem transfer_surjective (r : pushed f ⟶ sheaf Y)
    (h : StructureAdditiveSheaf318.pullback f ≫ r = 𝟙 (sheaf Y)) (n : ℕ) :
    Function.Surjective (transfer f r n) :=
  Function.RightInverse.surjective (transfer_pullback f r h n)

@[expose] def projection (r : pushed f ⟶ sheaf Y) (n : ℕ) : pushedH f n →+ pushedH f n :=
  (pullback f n).comp (transfer f r n)

theorem projection_twice (r : pushed f ⟶ sheaf Y)
    (h : StructureAdditiveSheaf318.pullback f ≫ r = 𝟙 (sheaf Y))
    (n : ℕ) (x : pushedH f n) : projection f r n (projection f r n x) = projection f r n x := by
  change pullback f n (transfer f r n (pullback f n (transfer f r n x))) = _
  rw [transfer_pullback f r h]
  rfl

/-- The usual degree-zero comparison with the original global regular functions. -/
@[expose] def structureHZero (Y : Scheme) : structureH Y 0 ≃+ Γ(Y, ⊤) :=
  Sheaf.H.equiv₀ (sheaf Y) CategoryTheory.Limits.isTerminalTop

@[expose] def pushedHZero : pushedH f 0 ≃+ Γ(X, f ⁻¹ᵁ ⊤) :=
  Sheaf.H.equiv₀ (pushed f) CategoryTheory.Limits.isTerminalTop

/-- In degree zero the cohomology map is exactly the original section pullback. -/
theorem pullback_HZero (x : structureH Y 0) :
    pushedHZero f (pullback f 0 x) = f.app ⊤ (structureHZero Y x) :=
  (Sheaf.H.equiv₀_naturality CategoryTheory.Limits.isTerminalTop
    (StructureAdditiveSheaf318.pullback f) x).symm

/-- The transferred cohomology map retains the precise actual sheaf component. -/
theorem transfer_HZero (r : pushed f ⟶ sheaf Y) (x : pushedH f 0) :
    structureHZero Y (transfer f r 0 x) = r.hom.app (Opposite.op ⊤) (pushedHZero f x) :=
  (Sheaf.H.equiv₀_naturality CategoryTheory.Limits.isTerminalTop r x).symm

end SheafCohomologyRetraction318
