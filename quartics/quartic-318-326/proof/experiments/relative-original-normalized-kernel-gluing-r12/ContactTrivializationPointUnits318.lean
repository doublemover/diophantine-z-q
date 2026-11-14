module
public import OriginalLineFrameUnitTorsor318
public import ContactTrivializationAffinePoints318
public section
noncomputable section
namespace ContactTrivializationPointUnits318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactCoefficientNativeSections318
open ContactTrivializationAffinePoints318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (S : CommRingCat.{0}) [Algebra ℚ S] (f : R →ₐ[ℚ] S)
local instance : Algebra R S := f.toAlgebra
local notation "N" => L' R S f c L

/-- Actual scheme points of the original trivialization open inherit the
literal unit action on their classified full frame, using both proven inverses. -/
@[expose] def act (u : Γ(curve S c,⊤)ˣ) (x : Points R c L S f) : Points R c L S f :=
  (equivalence R c L S f).symm
    (OriginalLineFrameUnitTorsor318.act N u (equivalence R c L S f x))
lemma frame_act (u : Γ(curve S c,⊤)ˣ) (x : Points R c L S f) :
    equivalence R c L S f (act R c L S f u x)=
      StructureLineAutomorphisms318.iso (curve S c) u ≪≫ equivalence R c L S f x :=
  (equivalence R c L S f).apply_symm_apply _

@[expose] def ratio (x y : Points R c L S f) : Γ(curve S c,⊤)ˣ :=
  OriginalLineFrameUnitTorsor318.ratio N (equivalence R c L S f x) (equivalence R c L S f y)

lemma existsUnique (x y : Points R c L S f) :
    ∃! u : Γ(curve S c,⊤)ˣ,act R c L S f u x=y := by
  obtain ⟨u,hu,uniq⟩ := OriginalLineFrameUnitTorsor318.existsUnique N
    (equivalence R c L S f x) (equivalence R c L S f y)
  refine ⟨u,?_,?_⟩
  · apply (equivalence R c L S f).injective
    rw [frame_act]
    exact hu
  · intro v hv
    apply uniq
    have he := congrArg (equivalence R c L S f) hv
    rw [frame_act] at he
    exact he

/-- Exact section-value action. These are units of the ORIGINAL curve's
full global-function ring, not unproved identifications with base units. -/
lemma value_act (u : Γ(curve S c,⊤)ˣ) (x : Points R c L S f) :
    (equivalence R c L S f (act R c L S f u x)).hom.app ⊤ 1=
      (u:Γ(curve S c,⊤)) • (equivalence R c L S f x).hom.app ⊤ 1 := by
  rw [frame_act]
  change (equivalence R c L S f x).hom.app ⊤
    ((ClutchedModule318.multiply (u:Γ(curve S c,⊤))).app ⊤ 1)=_
  rw [ClutchedModule318.multiply_top,one_mul]
  have h := Scheme.Modules.Hom.app_smul (equivalence R c L S f x).hom
    (u:Γ(curve S c,⊤)) (show Γ(curve S c,⊤) from 1)
  simpa only [smul_eq_mul,mul_one] using h
end ContactTrivializationPointUnits318
