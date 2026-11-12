module
public import ProjectiveParameterNonzeroOpen318
public section
noncomputable section
namespace ProjectiveParameterUnitAction318
open scoped TensorProduct
universe u v w
variable (R : Type u) [CommRing R] (P : Type v) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
local notation "A" => ProjectiveSectionParameter318.algebra R P

/-- The actual scalar action on the symmetric parameter algebra, not a
permutation of names for its points. -/
@[expose] def scale (r : R) : A →ₐ[R] A :=
  SymmetricAlgebra.lift (r • SymmetricAlgebra.ι R (Module.Dual R P))
lemma scale_generator (r : R) (φ : Module.Dual R P) :
    scale R P r (SymmetricAlgebra.ι R _ φ)=r • SymmetricAlgebra.ι R _ φ := by
  rw [scale,SymmetricAlgebra.lift_ι_apply,LinearMap.smul_apply]
lemma scale_one : scale R P 1=AlgHom.id R A := by
  apply SymmetricAlgebra.algHom_ext
  ext φ
  change scale R P 1 (SymmetricAlgebra.ι R _ φ)=SymmetricAlgebra.ι R _ φ
  rw [scale_generator,one_smul]
lemma scale_comp (r t : R) : (scale R P r).comp (scale R P t)=scale R P (t*r) := by
  apply SymmetricAlgebra.algHom_ext
  ext φ
  change scale R P r (scale R P t (SymmetricAlgebra.ι R _ φ))=_
  rw [scale_generator,map_smul,scale_generator,scale_generator,mul_smul]

/-- Genuine coefficient units give inverse algebra automorphisms of the
SAME affine parameter algebra over the SAME coefficient ring. -/
@[expose] def equivalence (u : Rˣ) : A ≃ₐ[R] A where
  __ := scale R P (u:R)
  invFun := scale R P ((u⁻¹:Rˣ):R)
  left_inv x := by
    have h := scale_comp R P ((u⁻¹:Rˣ):R) (u:R)
    rw [Units.mul_inv,scale_one] at h
    exact DFunLike.congr_fun h x
  right_inv x := by
    have h := scale_comp R P (u:R) ((u⁻¹:Rˣ):R)
    rw [Units.inv_mul,scale_one] at h
    exact DFunLike.congr_fun h x

variable (S : Type w) [CommRing S] [Algebra R S]
/-- Pulling an actual affine parameter point through this automorphism
scales its classified tensor section by the original coefficient. -/
lemma points_scale (r : R) (a : A →ₐ[R] S) :
    ProjectiveSectionParameter318.points R P S (a.comp (scale R P r))=
      algebraMap R S r • ProjectiveSectionParameter318.points R P S a := by
  apply (FiniteProjectiveTensorDual318.equivalence R P S
    (FiniteProjectiveEvaluationFrame318.frame R P)).injective
  ext φ
  change FiniteProjectiveTensorDual318.pairing R P S
    (ProjectiveSectionParameter318.points R P S (a.comp (scale R P r))) φ=_
  rw [ProjectiveSectionParameter318.coordinate,map_smul,LinearMap.smul_apply,
    ProjectiveSectionParameter318.coordinate]
  change a (scale R P r (SymmetricAlgebra.ι R _ φ))=
    algebraMap R S r * a (SymmetricAlgebra.ι R _ φ)
  rw [scale_generator,map_smul,Algebra.smul_def]

/-- Scalar action on ALL affine coefficient tests. Units may belong to
S, rather than lift from R; this is essential for a relative Gm action. -/
@[expose] def pointScale (s : S) (a : A →ₐ[R] S) : A →ₐ[R] S :=
  SymmetricAlgebra.lift (s • (a.toLinearMap.comp (SymmetricAlgebra.ι R _)))
lemma pointScale_generator (s : S) (a : A →ₐ[R] S) (φ : Module.Dual R P) :
    pointScale R P S s a (SymmetricAlgebra.ι R _ φ)=s*a (SymmetricAlgebra.ι R _ φ) := by
  rw [pointScale,SymmetricAlgebra.lift_ι_apply,LinearMap.smul_apply,LinearMap.comp_apply]
  rfl
lemma points_pointScale (s : S) (a : A →ₐ[R] S) :
    ProjectiveSectionParameter318.points R P S (pointScale R P S s a)=
      s • ProjectiveSectionParameter318.points R P S a := by
  apply (FiniteProjectiveTensorDual318.equivalence R P S
    (FiniteProjectiveEvaluationFrame318.frame R P)).injective
  ext φ
  change FiniteProjectiveTensorDual318.pairing R P S
    (ProjectiveSectionParameter318.points R P S (pointScale R P S s a)) φ=
    FiniteProjectiveTensorDual318.pairing R P S
      (s • ProjectiveSectionParameter318.points R P S a) φ
  rw [ProjectiveSectionParameter318.coordinate,map_smul,LinearMap.smul_apply,
    ProjectiveSectionParameter318.coordinate,pointScale_generator]
  rfl
lemma pointScale_one (a : A →ₐ[R] S) : pointScale R P S 1 a=a := by
  apply (ProjectiveSectionParameter318.points R P S).injective
  rw [points_pointScale,one_smul]
lemma pointScale_mul (s t : S) (a : A →ₐ[R] S) :
    pointScale R P S s (pointScale R P S t a)=pointScale R P S (s*t) a := by
  apply (ProjectiveSectionParameter318.points R P S).injective
  rw [points_pointScale,points_pointScale,points_pointScale,mul_smul]
lemma pointScale_natural {T : Type*} [CommRing T] [Algebra R T] (g : S →ₐ[R] T)
    (s : S) (a : A →ₐ[R] S) :
    g.comp (pointScale R P S s a)=pointScale R P T (g s) (g.comp a) := by
  apply SymmetricAlgebra.algHom_ext
  ext φ
  change g (pointScale R P S s a (SymmetricAlgebra.ι R _ φ))=_
  rw [pointScale_generator,pointScale_generator,map_mul]
  rfl

/-- The ORIGINAL nonzero-parameter open is invariant at every actual
prime, not merely at field-valued points over the ground field. -/
lemma comap_mem_locus (u : Rˣ) (p : PrimeSpectrum A) :
    PrimeSpectrum.comap (scale R P (u:R)).toRingHom p ∈
      ProjectiveParameterNonzeroOpen318.locus R P ↔
    p ∈ ProjectiveParameterNonzeroOpen318.locus R P := by
  rw [ProjectiveParameterNonzeroOpen318.mem_locus,
    ProjectiveParameterNonzeroOpen318.mem_locus]
  apply not_congr
  simp only [ProjectiveParameterZeroCoordinates318.zeroIdeal,Ideal.span_le,Set.range_subset_iff]
  constructor
  · intro h i
    have hi := h i
    change scale R P (u:R) (ProjectiveParameterZeroCoordinates318.coordinate R P i)∈p.asIdeal at hi
    have he : scale R P (u:R) (ProjectiveParameterZeroCoordinates318.coordinate R P i)=
        (u:R) • ProjectiveParameterZeroCoordinates318.coordinate R P i :=
      scale_generator R P (u:R) _
    rw [he,Algebra.smul_def] at hi
    have hi' := p.asIdeal.mul_mem_left (algebraMap R A ((u⁻¹:Rˣ):R)) hi
    simpa only [← mul_assoc,← map_mul,Units.inv_mul,map_one,one_mul] using hi'
  · intro h i
    change scale R P (u:R) (ProjectiveParameterZeroCoordinates318.coordinate R P i)∈p.asIdeal
    rw [show scale R P (u:R) (ProjectiveParameterZeroCoordinates318.coordinate R P i)=
      (u:R) • ProjectiveParameterZeroCoordinates318.coordinate R P i from scale_generator R P (u:R) _,
      Algebra.smul_def]
    exact p.asIdeal.mul_mem_left _ (h i)
end ProjectiveParameterUnitAction318
