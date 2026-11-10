module
public import ContactRelativeFppfLocalSections318
public section
noncomputable section
namespace ContactRelativeFppfSingleton318
open AlgebraicGeometry CategoryTheory Opposite
open OriginalRelativeSite318 OriginalRelativeOpenBaseChange318 ContactUniversalRigidifiedClass318
open ContactRelativeFppfLocalSections318
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (t : ℚ) {X Y : Scheme} (b : Y ⟶ FieldBase t) (b' : X ⟶ FieldBase t)
  (f : X ⟶ Y) (hf : f ≫ b = b') [Flat f] [Surjective f] [LocallyOfFinitePresentation f]

/-- Actual singleton fppf descent on every original relative test, with
no affine, reduced or quasi-compactness hypothesis on either original scheme.
The local affine solutions glue on whole intersections and recover the
original covering class on the entire original source. -/
theorem isSheafFor :
    Presieve.IsSheafFor (presheaf (q t)) (Presieve.singleton (arrow b b' f hf)) := by
  rw [Presieve.isSheafFor_singleton]
  intro x hx
  obtain ⟨y,hy,hyuniq⟩ := ContactZariskiClassDescent318.matching_unique t b
    (fun U : Y.affineOpens => U.1) (affine_cover (Y:=Y))
    (localSection t b b' f hf x hx) (matching t b b' f hf x hx)
  have hxy : (presheaf (q t)).map (arrow b b' f hf).op y = x := by
    apply (ContactRelativeOpenPresieve318.isSheafFor t b'
      (fun U : Y.affineOpens => f ⁻¹ᵁ U.1)
      (inverse_image_cover f (fun U : Y.affineOpens => U.1) (affine_cover (Y:=Y)))).isSeparatedFor.ext
    rintro Z a ⟨U⟩
    rw [← PresheafSingletonSquares318.map_square (presheaf (q t)) (arrow b b' f hf)
      (restrictedArrow b b' f hf U.1) (openArrow b U.1) (openArrow b' (f ⁻¹ᵁ U.1))
      (square b b' f hf U.1)]
    change (presheaf (q t)).map (restrictedArrow b b' f hf U.1).op
      (RelativeLineClassBaseChange318.testMap (q t) b (U.1.ι ≫ b) U.1.ι rfl y) = _
    rw [hy U,localSection_recovery]
  exact ⟨y,hxy,fun y' hy' => ContactRelativeFppfSeparated318.injective t b b' f hf
    (hy'.trans hxy.symm)⟩
end ContactRelativeFppfSingleton318
