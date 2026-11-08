module
public import AffineSpecNormalization318
public section
noncomputable section
namespace AffineIntrinsicNormalization318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

/-- The comparison datum retains the given algebra structure and its actual
universal differential, including the target's literal structural map. -/
structure Data (α : Algebra R S) where
  iso : tilde (R:=CommRingCat.of S) (IntrinsicEqualityTransport318.algebraModule α) ≅
    FamilyIntrinsicDifferentials318.omega (Spec.map (CommRingCat.ofHom α.algebraMap))
  fac (s : S) : moduleSpecΓFunctor.map iso.hom
      ((tilde.isoTop (R:=CommRingCat.of S) (IntrinsicEqualityTransport318.algebraModule α)).hom
        (IntrinsicEqualityTransport318.algebraD α s)) =
    (FamilyIntrinsicDifferentials318.D (Spec.map (CommRingCat.ofHom α.algebraMap))).d
      ((Scheme.ΓSpecIso (CommRingCat.of S)).inv s)

@[expose] def inducedData (α : Algebra R S) : Data α.algebraMap.toAlgebra :=
  ⟨AffineSpecNormalization318.specIso (CommRingCat.ofHom α.algebraMap),
    AffineSpecNormalization318.specMap_D (CommRingCat.ofHom α.algebraMap)⟩

@[expose] def algebraData (α : Algebra R S) : Data α := by
  letI := α
  have h : α.algebraMap.toAlgebra = α := toAlgebra_algebraMap (R:=R) (S:=S)
  exact h ▸ inducedData α

variable [Algebra R S]
@[expose] def algebraIso : AffineDifferentialSheaf318.differentialSheaf (R:=R) (S:=S) ≅
    FamilyIntrinsicDifferentials318.omega (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  (algebraData (inferInstance : Algebra R S)).iso

/-- The actual ordinary algebraic differential maps to the exact intrinsic one. -/
theorem algebra_D (s : S) :
    moduleSpecΓFunctor.map (algebraIso (R:=R) (S:=S)).hom
      ((tilde.isoTop (R:=CommRingCat.of S) (ModuleCat.of S (KaehlerDifferential R S))).hom
        (KaehlerDifferential.D R S s)) =
    (FamilyIntrinsicDifferentials318.D
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))).d
        ((Scheme.ΓSpecIso (CommRingCat.of S)).inv s) :=
  (algebraData (inferInstance : Algebra R S)).fac s
end AffineIntrinsicNormalization318
