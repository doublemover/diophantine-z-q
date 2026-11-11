module
public import ThreeJEtaleCertificate318
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public section
noncomputable section
namespace ThreeJOriginalEtaleOpen318
open AlgebraicGeometry CategoryTheory Polynomial
open ThreeJMonicAlgebra318 ThreeJLaurentEquiv318 ThreeJEtaleCertificate318
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance : Algebra Base Laurent := ThreeJFiniteLaurentMap318.jAlgebra

/-- The scalar action is the restriction of the exact global j pullback. -/
@[expose,instance_reducible] def openAlgebra : Algebra Base ThreeJModuliOpen318.Ring := inferInstance
attribute [local instance] openAlgebra

lemma localizing_element :
    ThreeJFiniteLaurentMap318.baseCoordinateEquiv
      (AdjoinRoot.mk polynomial (C branchPolynomial))=ThreeJModuliOpen318.deleted := by
  rw [AdjoinRoot.mk_C]
  change ThreeJLaurentEquiv318.coordinateEquiv
    (algebraMap Base Model branchPolynomial)=_
  rw [coordinate_base]
  simp only [branchPolynomial,ThreeJLaurentEquiv318.baseMap,map_mul,map_sub,map_ofNat,
    Polynomial.aeval_X,ThreeJModuliOpen318.deleted]

lemma powers_map :
    (Submonoid.powers (AdjoinRoot.mk polynomial (C branchPolynomial))).map
      ThreeJFiniteLaurentMap318.baseCoordinateEquiv.toRingEquiv.toMonoidHom=
      Submonoid.powers ThreeJModuliOpen318.deleted := by
  rw [Submonoid.map_powers]
  congr 1
  exact localizing_element

/-- Actual coefficient-preserving equivalence of the standard-etale
localization and the original moduli source open, via the original Laurent map. -/
@[expose] def localizationEquiv : LocalModel ≃ₐ[Base] ThreeJModuliOpen318.Ring :=
  { IsLocalization.ringEquivOfRingEquiv LocalModel ThreeJModuliOpen318.Ring
      ThreeJFiniteLaurentMap318.baseCoordinateEquiv.toRingEquiv powers_map with
    commutes' := by
      intro a
      let E : LocalModel ≃+* ThreeJModuliOpen318.Ring :=
        IsLocalization.ringEquivOfRingEquiv LocalModel ThreeJModuliOpen318.Ring
          ThreeJFiniteLaurentMap318.baseCoordinateEquiv.toRingEquiv powers_map
      change E (algebraMap Base LocalModel a)=algebraMap Base ThreeJModuliOpen318.Ring a
      have hloc : E (algebraMap (AdjoinRoot polynomial) LocalModel
          (algebraMap Base (AdjoinRoot polynomial) a)) =
          algebraMap Laurent ThreeJModuliOpen318.Ring
            (ThreeJFiniteLaurentMap318.baseCoordinateEquiv (algebraMap Base Model a)) :=
        IsLocalization.ringEquivOfRingEquiv_eq
          (S:=LocalModel) (Q:=ThreeJModuliOpen318.Ring) powers_map
          (algebraMap Base (AdjoinRoot polynomial) a)
      calc
        _ = E (algebraMap Model LocalModel (algebraMap Base Model a)) :=
          congrArg E (IsScalarTower.algebraMap_apply Base Model LocalModel a)
        _ = algebraMap Laurent ThreeJModuliOpen318.Ring
            (ThreeJFiniteLaurentMap318.baseCoordinateEquiv (algebraMap Base Model a)) := hloc
        _ = algebraMap Laurent ThreeJModuliOpen318.Ring (algebraMap Base Laurent a) :=
          congrArg (algebraMap Laurent ThreeJModuliOpen318.Ring)
            (ThreeJFiniteLaurentMap318.baseCoordinateEquiv.commutes a)
        _ = _ := (IsScalarTower.algebraMap_apply Base Laurent ThreeJModuliOpen318.Ring a).symm }

lemma open_etale : Algebra.Etale Base ThreeJModuliOpen318.Ring := by
  letI := local_model_etale
  exact Algebra.Etale.of_equiv localizationEquiv

lemma actual_scalar_map : algebraMap Base ThreeJModuliOpen318.Ring=
    (Polynomial.aeval (R:=ℚ) ThreeJModuliOpen318.j).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro q
    change ThreeJModuliOpen318.inclusion (ThreeJLaurentEquiv318.baseMap (C q))=
      Polynomial.aeval (R:=ℚ) ThreeJModuliOpen318.j (C q)
    rw [ThreeJLaurentEquiv318.baseMap,Polynomial.aeval_C,AlgHom.commutes,Polynomial.aeval_C]
  · change ThreeJModuliOpen318.inclusion (ThreeJLaurentEquiv318.baseMap X)=
      Polynomial.aeval (R:=ℚ) ThreeJModuliOpen318.j X
    rw [ThreeJLaurentEquiv318.baseMap,Polynomial.aeval_X,Polynomial.aeval_X]
    rfl

/-- Algebraic etaleness of the original rational-open j map follows from
the monic presentation, not from analytic local orders or point bijectivity. -/
theorem rationalJ_etale : Etale ThreeJModuliScheme318.rationalJ := by
  letI := open_etale
  have h : Etale (Spec.algebraMap Base ThreeJModuliOpen318.Ring) :=
    (HasRingHomProperty.Spec_iff (P:=@Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)
  change Etale (Spec.map (CommRingCat.ofHom (algebraMap Base ThreeJModuliOpen318.Ring))) at h
  rw [actual_scalar_map] at h
  exact h

/-- The exact global scheme j map is etale on the unchanged arithmetic
source open, identified with the rationalized original diamond quotient. -/
theorem original_restriction_etale :
    Etale (ThreeJModuliScheme318.embedding ≫ ThreeProjectiveJMap318.map) := by
  rw [ThreeJModuliScheme318.global_j_square]
  letI := rationalJ_etale
  infer_instance

theorem arithmetic_restriction_etale :
    Etale (ThreeRationalModuliScheme318.rationalEmbedding ≫ ThreeProjectiveJMap318.map) := by
  rw [ThreeRationalModuliScheme318.rationalEmbedding,Category.assoc]
  letI := original_restriction_etale
  infer_instance

end ThreeJOriginalEtaleOpen318
