module
public import ContactGeometricIsomInvariant318
public section
noncomputable section
namespace ContactWholeGeometricKernelDescent318
open AlgebraicGeometry CategoryTheory Opposite
variable (c : Fin 4 → ℚˣ)
local notation "Q" => Spec (CommRingCat.of ℚ)
local notation "J" => RelativeFppfLineSheaf318.topology Q
local notation "A" => ContactCartierDifferencePresheaf318.presheaf c
local notation "v" => ContactCartierDifferenceAbel318.transformation c
variable (F : Sheaf J (Type 1)) (a : A ⟶ F.obj)
/-- Geometric invariance ONLY on the constructed affine relation schemes
controls the actual Abel kernel on EVERY whole coefficient scheme.
The actual induced rational algebras and full affine cover are used. -/
lemma kernel (ha : ContactGeometricIsomInvariant318.Invariant c F a) (B : Over Q)
    (D E : A.obj (op B)) (he : v.app (op B) D=v.app (op B) E) :
    a.app (op B) D=a.app (op B) E := by
  apply OriginalAffineSheafElementExt318.ext F B
  intro i
  let f := OriginalAffineCoefficientCover318.arrow B.hom i
  have hvD := ConcreteCategory.congr_hom (v.naturality f.op) D
  have hvE := ConcreteCategory.congr_hom (v.naturality f.op) E
  have hei : v.app (op (OriginalAffineCoefficientCover318.object B.hom i)) (A.map f.op D)=
      v.app (op (OriginalAffineCoefficientCover318.object B.hom i)) (A.map f.op E) :=
    hvD.trans ((congrArg ((ContactDifferenceSheafEpimorphism318.target c).obj.map f.op) he).trans hvE.symm)
  have hi := ContactGeometricIsomInvariant318.affine_kernel c F a ha
    (OriginalAffineCoefficientCover318.ring B.hom i) (A.map f.op D) (A.map f.op E) hei
  have haD := ConcreteCategory.congr_hom (a.naturality f.op) D
  have haE := ConcreteCategory.congr_hom (a.naturality f.op) E
  exact haD.symm.trans (hi.trans haE)
end ContactWholeGeometricKernelDescent318
