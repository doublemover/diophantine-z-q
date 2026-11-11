module
public import ContactOriginalWholeRestriction318
public import OpenClutchedLocallyFree318
public import LineSheafTensorIsos318
public section
noncomputable section
namespace ContactOriginalTwistingLine318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalWholeRestriction318 ContactOriginalLaurentOverlap318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ)

/-- The actual Laurent base coordinate on the FULL original Contact
overlap, transported through its original open-immersion ring isomorphism. -/
@[expose] def scalar : LaurentPolynomial ℚ →+*
    Γ(ContactProjectiveModel318.model c,finiteOpen c ⊓ infinityOpen c) :=
  ((Scheme.ΓSpecIso (CommRingCat.of OriginalLaurentProjectiveOverlap318.Ring)).inv ≫
    (projection c).appTop ≫ ((into c).appIso ⊤).inv ≫
    (ContactProjectiveModel318.model c).presheaf.map (eqToHom (overlap_image c).symm).op).hom

def monomialUnit (d : ℤ) : (LaurentPolynomial ℚ)ˣ where
  val := LaurentPolynomial.T d
  inv := LaurentPolynomial.T (-d)
  val_inv := by rw [← LaurentPolynomial.T_add,add_neg_cancel,LaurentPolynomial.T_zero]
  inv_val := by rw [← LaurentPolynomial.T_add,neg_add_cancel,LaurentPolynomial.T_zero]

/-- A genuine invertible original regular function, not a formal symbol. -/
@[expose] def transitionUnit (d : ℤ) :
    Γ(ContactProjectiveModel318.model c,finiteOpen c ⊓ infinityOpen c)ˣ :=
  Units.map (scalar c).toMonoidHom (monomialUnit d)

lemma transitionUnit_val (d : ℤ) : (transitionUnit c d).val = scalar c (LaurentPolynomial.T d) := rfl

lemma transitionUnit_add (d e : ℤ) : transitionUnit c (d+e) = transitionUnit c d * transitionUnit c e := by
  apply Units.ext
  change scalar c (LaurentPolynomial.T (d+e)) =
    scalar c (LaurentPolynomial.T d) * scalar c (LaurentPolynomial.T e)
  rw [LaurentPolynomial.T_add,map_mul]

/-- The ACTUAL clutched line with original regular transition T^d on the
entire original two-open cover. Identification with projective O(d) is
not assumed or claimed by this construction. -/
@[expose] def line (d : ℤ) : Line (ContactProjectiveModel318.model c) where
  object := OpenClutchedLine318.line (finiteOpen c) (infinityOpen c) (transitionUnit c d)
  Index := ULift Bool
  opens := OpenClutchedLocallyFree318.cover (finiteOpen c) (infinityOpen c)
  cover := OpenClutchedLocallyFree318.cover_top (finiteOpen c) (infinityOpen c) (cover c)
  frame i := by
    rcases i with ⟨i⟩
    cases i
    · exact (OpenClutchedLine318.firstFrame (finiteOpen c) (infinityOpen c) (transitionUnit c d)).symm
    · exact (OpenClutchedLine318.secondFrame (finiteOpen c) (infinityOpen c) (transitionUnit c d)).symm

@[expose] def finiteFrame (d : ℤ) : (line c d).object.restrict (finiteOpen c).ι ≅
    SheafOfModules.unit (finiteOpen c).toScheme.ringCatSheaf :=
  OpenClutchedLine318.firstFrame (finiteOpen c) (infinityOpen c) (transitionUnit c d)

@[expose] def infinityFrame (d : ℤ) : (line c d).object.restrict (infinityOpen c).ι ≅
    SheafOfModules.unit (infinityOpen c).toScheme.ringCatSheaf :=
  OpenClutchedLine318.secondFrame (finiteOpen c) (infinityOpen c) (transitionUnit c d)

/-- Tensor the unchanged original line with this actual geometric twist. -/
def twist (L : Line (ContactProjectiveModel318.model c)) (d : ℤ) :
    Line (ContactProjectiveModel318.model c) := LineSheafTensor318.line L (line c d)
end ContactOriginalTwistingLine318
