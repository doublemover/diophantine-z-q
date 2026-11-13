module
public import GlobalInvariantCompatibility318
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import all WeierstrassGluing318
public section
noncomputable section
namespace IdentityCotangent318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R]

/-- Genuine pullback of the structure line along an arbitrary scheme morphism. -/
@[expose] def pullbackUnitIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf := by
  letI : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  letI : IsIso (SheafOfModules.pullbackObjUnitToUnit.{u,u,u,u,u} f.toRingCatSheafHom) := by
    infer_instance
  exact asIso (SheafOfModules.pullbackObjUnitToUnit.{u,u,u,u,u} f.toRingCatSheafHom)

/-- The actual identity point lies in the actual smooth infinity differential
chart, and its factorization is the previously constructed global identity. -/
theorem infinity_factorization (A B : R) :
    InfinityChart318.sectionAtInfinity A B ≫ InvariantChartCover318.infinityInto A B =
      WeierstrassGluing318.infinity A B := by
  unfold InvariantChartCover318.infinityInto WeierstrassGluing318.infinity
  rw [←Category.assoc]
  congr 1
  unfold InfinityChart318.sectionAtInfinity InfinitySmooth318.infinity
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact InfinityChart318.smoothOrigin_map A B

/-- The actual cotangent line at the identity, defined by pulling back the genuine
relative differential sheaf on its smooth infinity neighborhood. -/
@[expose] def cotangent (A B : R) : (Spec (CommRingCat.of R)).Modules :=
  (Scheme.Modules.pullback (InfinityChart318.sectionAtInfinity A B)).obj
    (AffineDifferentialSheaf318.differentialSheaf (R:=R) (S:=DifferentialChartMaps318.InfinityChart A B))

/-- Actual normalized invariant differential frame, pulled back to the identity.
No global Hodge pushforward comparison is assumed. -/
@[expose] def cotangentFrame (A B : R) :
    cotangent A B ≅ SheafOfModules.unit (Spec (CommRingCat.of R)).ringCatSheaf :=
  (Scheme.Modules.pullback (InfinityChart318.sectionAtInfinity A B)).mapIso
      (AffineDifferentialSheaf318.frameIso (InvariantNormalizedFrames318.infinityFrame A B)) ≪≫
    pullbackUnitIso (InfinityChart318.sectionAtInfinity A B)

/-- The pullback of the genuine global line is canonically identified with the
actual relative cotangent sheaf at the global identity, through its exact chart. -/
@[expose] def globalLineToCotangent (A B : R) :
    (Scheme.Modules.pullback (WeierstrassGluing318.infinity A B)).obj
      (GlobalInvariantLine318.line A B) ≅ cotangent A B :=
  ((Scheme.Modules.pullbackCongr (infinity_factorization A B)).app _).symm ≪≫
  ((Scheme.Modules.pullbackComp (InfinityChart318.sectionAtInfinity A B)
      (InvariantChartCover318.infinityInto A B)).app _).symm ≪≫
  (Scheme.Modules.pullback (InfinityChart318.sectionAtInfinity A B)).mapIso
    (((Scheme.Modules.restrictFunctorIsoPullback (InvariantChartCover318.infinityInto A B)).app _).symm ≪≫
      GlobalInvariantLine318.infinityIdentification A B)

/-- Literal actual identity-cotangent frame for the open-j family. -/
@[expose] def literalCotangentFrame (N : ℕ) :=
  cotangentFrame (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)
end IdentityCotangent318
