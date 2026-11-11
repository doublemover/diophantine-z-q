module
public import ProjectiveParameterNormalizedTest318
public import ProjectiveParameterSliceBase318
public section
noncomputable section
namespace ProjectiveParameterNormalizationNatural318
open AlgebraicGeometry CategoryTheory
variable (R : CommRingCat.{0}) (P : Type) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
local notation "A" => ProjectiveSectionParameter318.algebra R P
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "x" => ProjectiveParameterZeroCoordinates318.coordinate R P
variable (S T : CommRingCat.{0}) [Algebra R S] [Algebra R T]
  (g : S →ₐ[R] T) (a : A →ₐ[R] S) (i : Fin F.size) (u : Sˣ) (hi : a (x i)=(u:S))

lemma coordinate : (g.comp a) (x i)=((Units.map g.toMonoidHom u):T) := congrArg g hi

lemma sliceMap : g.comp (ProjectiveParameterNormalizedTest318.sliceMap R P S a i u hi)=
    ProjectiveParameterNormalizedTest318.sliceMap R P T (g.comp a) i
      (Units.map g.toMonoidHom u) (coordinate R P S T g a i u hi) := by
  apply Ideal.Quotient.algHom_ext
  apply AlgHom.ext
  intro z
  change g (Ideal.Quotient.lift _ _ _ (Ideal.Quotient.mk _ z))=
    Ideal.Quotient.lift _ _ _ (Ideal.Quotient.mk _ z)
  rw [Ideal.Quotient.lift_mk,Ideal.Quotient.lift_mk]
  exact DFunLike.congr_fun (ProjectiveParameterUnitAction318.pointScale_natural R P S g
    ((u⁻¹:Sˣ):S) a) z

/-- Naturality of the genuine normalized scheme map under EVERY
coefficient-algebra homomorphism, including nonflat/nilpotent tests. -/
lemma map_natural : Spec.map (CommRingCat.ofHom g.toRingHom) ≫
    ProjectiveParameterNormalizedTest318.map R P S a i u hi=
    ProjectiveParameterNormalizedTest318.map R P T (g.comp a) i
      (Units.map g.toMonoidHom u) (coordinate R P S T g a i u hi) := by
  rw [ProjectiveParameterNormalizedTest318.map,← Category.assoc,← Spec.map_comp]
  have h := congrArg (fun f => CommRingCat.ofHom f.toRingHom) (sliceMap R P S T g a i u hi)
  rw [h]
  rfl

/-- The same normalized map retains its original coefficient base map. -/
lemma over_base : ProjectiveParameterNormalizedTest318.map R P S a i u hi ≫
    ProjectiveParameterSliceBase318.projection R P=
    Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  rw [ProjectiveParameterNormalizedTest318.map,Category.assoc,
    ProjectiveParameterSliceBase318.into_projection,
    ProjectiveParameterSliceSchemes318.projection,← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (ProjectiveParameterNormalizedTest318.sliceMap R P S a i u hi).commutes r
end ProjectiveParameterNormalizationNatural318
