module

public import SelectedGreenLiteralWholeComplexField318
public import SelectedComplexGenericRatFunc318
public import SelectedActualComplexCompactOriginalDVR318
import all SelectedGreenLiteralWholeComplexField318
import Mathlib.Algebra.Field.Equiv

public section

noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial
open SelectedActualComplexOrdinaryScalar318
open SelectedComplexOrdinaryBase318 SelectedComplexOrdinaryOneField318 SelectedComplexGenericRatFunc318

namespace SelectedActualLiteralComplexCompactStalkDVR318

abbrev P (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X]) : Generic[X] :=
  genericPolynomial (p.map (toComplex N))

/-- The whole, not a factor, after installing the verified literal
complex coefficient equivalence into the actual C(J). -/
@[expose] def pJ (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X]) : (RatFunc ℂ)[X] :=
  letI : Algebra Base (RatFunc ℂ) := ratscalar
  (P N p).map ratEquiv.toRingEquiv.toRingHom

abbrev K (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X]) := AdjoinRoot (pJ N p)

private theorem pJ_associated (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X]) :
    letI : Algebra Base (RatFunc ℂ) := ratscalar
    Associated ((P N p).map ratEquiv.toRingEquiv.toRingHom) (pJ N p) := by
  letI : Algebra Base (RatFunc ℂ) := ratscalar
  unfold pJ
  exact Associated.refl _

/-- The two rings differ by the exact coefficient map, with the
same whole marked root. -/
def wholeRootEquiv (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X]) :
    AdjoinRoot (P N p) ≃+* K N p := by
  letI : Algebra Base (RatFunc ℂ) := ratscalar
  exact AdjoinRoot.mapRingEquiv ratEquiv.toRingEquiv (P N p) (pJ N p) (pJ_associated N p)

theorem wholeRootEquiv_root (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X]) :
    wholeRootEquiv N p (AdjoinRoot.root (P N p)) = AdjoinRoot.root (pJ N p) := by
  letI : Algebra Base (RatFunc ℂ) := ratscalar
  change AdjoinRoot.map ratEquiv.toRingEquiv.toRingHom (P N p) (pJ N p)
    (pJ_associated N p).symm.dvd (AdjoinRoot.root (P N p)) = _
  exact AdjoinRoot.map_root _ _ _ _

theorem wholeRootEquiv_j (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X]) :
    wholeRootEquiv N p
      (AdjoinRoot.of (P N p) (algebraMap Base Generic jCoord)) =
    AdjoinRoot.of (pJ N p) (RatFunc.X : RatFunc ℂ) := by
  letI : Algebra Base (RatFunc ℂ) := ratscalar
  have hp : ratEquiv (algebraMap Base Generic jCoord) = (RatFunc.X : RatFunc ℂ) :=
    ratEquiv_literal_j.trans RatFunc.algebraMap_X
  change AdjoinRoot.map ratEquiv.toRingEquiv.toRingHom (P N p) (pJ N p)
    (pJ_associated N p).symm.dvd (AdjoinRoot.of (P N p) (algebraMap Base Generic jCoord)) = _
  have he : AdjoinRoot.map ratEquiv.toRingEquiv.toRingHom (P N p) (pJ N p)
      (pJ_associated N p).symm.dvd (AdjoinRoot.of (P N p) (algebraMap Base Generic jCoord)) =
      AdjoinRoot.of (pJ N p) (ratEquiv (algebraMap Base Generic jCoord)) :=
    AdjoinRoot.map_of _ _ _ _ _
  exact he.trans (congrArg (AdjoinRoot.of (pJ N p)) hp)

theorem whole_isField (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X])
    (hf : IsField (AdjoinRoot (P N p))) : IsField (K N p) :=
  (wholeRootEquiv N p).toMulEquiv.isField_congr.mp hf

open SelectedActualComplexGenericChartClosures318 (JField)
open SelectedActualComplexGenericCompactNormal318 (model modelMap model_finite)
open SelectedActualComplexCompactOriginalDVR318 (complex_normalization_stalk_dvr)

/-- On the very whole marked root field and over its literal retained
j, the actual projective normalization is finite and its nongeneric
stalks are DVRs. The complex scalar tower is installed only once on
this model. -/
theorem literal_projective_normalization (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X])
    (hp : p.Monic) (hf : IsField (AdjoinRoot (P N p))) :
    letI : Field (K N p) := (whole_isField N p hf).toField
    IsFinite (modelMap (K N p)) ∧
      ∀ x : model (K N p), x ≠ genericPoint (model (K N p)) →
        IsDiscreteValuationRing ((model (K N p)).presheaf.stalk x) := by
  let T := K N p
  letI fT : Field T := (whole_isField N p hf).toField
  let aF : Algebra ℂ JField := RatFunc.instAlgebraOfPolynomial ℂ ℂ
  letI : Algebra ℂ JField := aF
  letI aJ : Algebra JField T := AdjoinRoot.instAlgebra (S := JField) (pJ N p)
  let aC : Algebra ℂ T := AdjoinRoot.instAlgebra (S := ℂ) (pJ N p)
  let tC : @IsScalarTower ℂ JField T aF.toSMul aJ.toSMul aC.toSMul :=
    @IsScalarTower.of_algebraMap_eq' ℂ JField T
      inferInstance inferInstance inferInstance aF aJ aC (by rfl)
  have hpC : (p.map (toComplex N)).Monic := hp.map (toComplex N)
  have hpG : (P N p).Monic := hpC.map (algebraMap Base Generic)
  have hpJ : (pJ N p).Monic := by
    unfold pJ
    letI : Algebra Base (RatFunc ℂ) := ratscalar
    exact hpG.map ratEquiv.toRingEquiv.toRingHom
  letI hFin : FiniteDimensional JField T := hpJ.finite_adjoinRoot
  let hSep : Algebra.IsSeparable JField T := inferInstance
  exact ⟨@model_finite T fT aJ aC tC hFin hSep,
    @complex_normalization_stalk_dvr T fT aJ aC tC hFin hSep⟩


open SelectedLiteralTorsionKernel318 SelectedPrimitiveOpen318 SelectedPrimitiveAffineSign318
open SelectedPrimitiveFixedX318 SelectedPrimitiveXCharacteristic318
open SelectedActualPrimitiveKernelAffine318 SelectedActualGreenSimpleChart318

/-- Select no new modular model: retain the exact original primitive
quotient and involution, its power-basis generator and its exact
characteristic polynomial, and compactify that whole complex field. -/
theorem literal_level_has_complex_normalization (N : ℕ) (hN : 2 < N) :
    letI : NeZero N := ⟨by omega⟩
    letI : IsFinite (kernelProjection N N) := (native_level_instances N).1
    letI : Etale (kernelProjection N N) := (native_level_instances N).2
    ∃ (I : Ideal (D N)) (e : PrimitiveScheme N N ≅ Spec (CommRingCat.of (D N ⧸ I))),
      intoAffine N N (Nat.lt_of_succ_lt hN) =
        e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ∧
      primitiveProjection N N = e.hom ≫ Spec.algebraMap (R N) (D N ⧸ I) ∧
      ∃ (σ : (D N ⧸ I) →ₐ[R N] (D N ⧸ I))
        (hσ : σ.comp (q N I) = (q N I).comp (sign N)),
        σ.comp σ = AlgHom.id (R N) (D N ⧸ I) ∧
        ∃ pb : PowerBasis (R N) (fixed N I σ),
          pb.gen = coordinate N I σ hσ ∧
          (letI : Module.Free (R N) (fixed N I σ) := Module.Free.of_basis pb.basis
           letI : Module.Finite (R N) (fixed N I σ) := pb.finite
           ∃ p : (R N)[X], p = charPolynomial N I σ hσ ∧ p.Monic ∧
            ∃ ep : AdjoinRoot p ≃ₐ[R N] fixed N I σ,
              ep (AdjoinRoot.root p) = coordinate N I σ hσ ∧
              IsUnit (AdjoinRoot.mk p p.derivative) ∧
              ∃ hf : IsField (AdjoinRoot (P N p)),
                letI : Field (K N p) := (whole_isField N p hf).toField
                IsFinite (modelMap (K N p)) ∧
                  ∀ x : model (K N p), x ≠ genericPoint (model (K N p)) →
                    IsDiscreteValuationRing ((model (K N p)).presheaf.stalk x)) := by
  letI : NeZero N := ⟨by omega⟩
  letI : IsFinite (kernelProjection N N) := (native_level_instances N).1
  letI : Etale (kernelProjection N N) := (native_level_instances N).2
  obtain ⟨I,e,he,hb,σ,hσ,hinv,pb,hpb,hchart⟩ :=
    SelectedGreenLiteralWholeComplexField318.literal_level_whole_field N hN
  letI : Module.Free (R N) (fixed N I σ) := Module.Free.of_basis pb.basis
  letI : Module.Finite (R N) (fixed N I σ) := pb.finite
  obtain ⟨p,hp,hm,ep,hep,hunit,hf⟩ := hchart
  exact ⟨I,e,he,hb,σ,hσ,hinv,pb,hpb,p,hp,hm,ep,hep,hunit,hf,
    literal_projective_normalization N p hm hf⟩

end SelectedActualLiteralComplexCompactStalkDVR318

#print axioms SelectedActualLiteralComplexCompactStalkDVR318.wholeRootEquiv_root
#print axioms SelectedActualLiteralComplexCompactStalkDVR318.wholeRootEquiv_j
#print axioms SelectedActualLiteralComplexCompactStalkDVR318.literal_projective_normalization
#print axioms SelectedActualLiteralComplexCompactStalkDVR318.literal_level_has_complex_normalization
