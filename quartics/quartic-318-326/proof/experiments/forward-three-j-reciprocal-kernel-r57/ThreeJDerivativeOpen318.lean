module
public import ThreeJOriginalEtaleOpen318
public section
noncomputable section
namespace ThreeJDerivativeOpen318
open AlgebraicGeometry CategoryTheory Polynomial
open ThreeJMonicAlgebra318 ThreeJLaurentEquiv318
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance : Algebra Base Laurent := ThreeJFiniteLaurentMap318.jAlgebra

@[expose] def derivativeImage : Laurent :=
  ThreeJFiniteLaurentMap318.baseCoordinateEquiv
    (AdjoinRoot.mk polynomial polynomial.derivative)
@[expose] def ellipticFactor : Laurent :=
  ProjectiveLineOverlap318.t^2-486*ProjectiveLineOverlap318.t-19683

lemma derivative_times_parameter :
    ProjectiveLineOverlap318.t*derivativeImage=
      (ProjectiveLineOverlap318.t+243)^2*ellipticFactor := by
  have hr := congrArg coordinateEquiv numerator_relation
  simp only [map_mul,map_add,map_pow,map_ofNat,coordinate_t,
    show coordinateEquiv j=jLaurent from forward_j] at hr
  have hd : derivativeImage=4*ProjectiveLineOverlap318.t^3+
      3*(756-jLaurent)*ProjectiveLineOverlap318.t^2+
      393660*ProjectiveLineOverlap318.t+19131876 := by
    have hderiv : polynomial.derivative =
        4*X^3+3*C (756-X)*X^2+393660*X+19131876 := by
      simp only [polynomial,derivative_add,derivative_mul,derivative_pow,
        derivative_X,derivative_C,derivative_ofNat,mul_zero,zero_mul,
        zero_add,add_zero,pow_zero,pow_one,mul_one,one_mul]
      norm_num only [Nat.reduceSub,map_ofNat] <;> ring
    let f : Base[X] →+* Laurent :=
      coordinateEquiv.toRingHom.comp (AdjoinRoot.mk polynomial)
    have hx : f X=ProjectiveLineOverlap318.t := by
      change coordinateEquiv (AdjoinRoot.mk polynomial X)=_
      rw [AdjoinRoot.mk_X]
      exact coordinate_t
    have hc (p:Base) : f (C p)=baseMap p := by
      change coordinateEquiv (AdjoinRoot.mk polynomial (C p))=_
      rw [AdjoinRoot.mk_C]
      exact coordinate_base p
    change f polynomial.derivative=_
    rw [hderiv]
    simp only [map_add,map_mul,map_pow,map_ofNat,hx,hc,map_sub,
      baseMap,Polynomial.aeval_X]
  rw [hd]
  unfold ellipticFactor
  linear_combination 3*hr

/-- The actual relative monic derivative differs from the original
ramification polynomial by exactly the invertible Laurent coordinate S. -/
theorem derivative_factorization : derivativeImage=
    ProjectiveLineOverlap318.s*(ProjectiveLineOverlap318.t+243)^2*ellipticFactor := by
  calc
    derivativeImage=(ProjectiveLineOverlap318.t*ProjectiveLineOverlap318.s)*
        derivativeImage := by rw [ProjectiveLineOverlap318.ts,one_mul]
    _ = ProjectiveLineOverlap318.s*(ProjectiveLineOverlap318.t*derivativeImage) := by ring
    _ = _ := by rw [derivative_times_parameter]; ring

/-- This standard-etale presentation removes only the derivative locus,
not the entire fibers above the elliptic values. -/
@[expose] def pair : StandardEtalePair Base where
  f := polynomial
  monic_f := monic
  g := polynomial.derivative
  cond := ⟨1,0,1,by simp⟩
abbrev LocalModel := Localization.Away (AdjoinRoot.mk polynomial polynomial.derivative)
abbrev Ring := Localization.Away derivativeImage

lemma powers_map :
    (Submonoid.powers (AdjoinRoot.mk polynomial polynomial.derivative)).map
      ThreeJFiniteLaurentMap318.baseCoordinateEquiv.toRingEquiv.toMonoidHom=
      Submonoid.powers derivativeImage := by
  rw [Submonoid.map_powers]
  rfl

@[expose] def localizationEquiv : LocalModel ≃ₐ[Base] Ring :=
  { IsLocalization.ringEquivOfRingEquiv LocalModel Ring
      ThreeJFiniteLaurentMap318.baseCoordinateEquiv.toRingEquiv powers_map with
    commutes' := by
      intro a
      let E : LocalModel ≃+* Ring :=
        IsLocalization.ringEquivOfRingEquiv LocalModel Ring
          ThreeJFiniteLaurentMap318.baseCoordinateEquiv.toRingEquiv powers_map
      change E (algebraMap Base LocalModel a)=algebraMap Base Ring a
      have hloc : E (algebraMap (AdjoinRoot polynomial) LocalModel
          (algebraMap Base (AdjoinRoot polynomial) a)) =
          algebraMap Laurent Ring
            (ThreeJFiniteLaurentMap318.baseCoordinateEquiv (algebraMap Base Model a)) :=
        IsLocalization.ringEquivOfRingEquiv_eq
          (S:=LocalModel) (Q:=Ring) powers_map
          (algebraMap Base (AdjoinRoot polynomial) a)
      calc
        _ = E (algebraMap Model LocalModel (algebraMap Base Model a)) :=
          congrArg E (IsScalarTower.algebraMap_apply Base Model LocalModel a)
        _ = algebraMap Laurent Ring
            (ThreeJFiniteLaurentMap318.baseCoordinateEquiv (algebraMap Base Model a)) := hloc
        _ = algebraMap Laurent Ring (algebraMap Base Laurent a) :=
          congrArg (algebraMap Laurent Ring)
            (ThreeJFiniteLaurentMap318.baseCoordinateEquiv.commutes a)
        _ = _ := (IsScalarTower.algebraMap_apply Base Laurent Ring a).symm }

lemma derivative_open_etale : Algebra.Etale Base Ring := by
  letI : Algebra.Etale Base LocalModel := Algebra.Etale.of_equiv pair.equivAwayAdjoinRoot
  exact Algebra.Etale.of_equiv localizationEquiv

@[expose] def toLaurent : Spec (CommRingCat.of Ring) ⟶ Spec (CommRingCat.of Laurent) :=
  Spec.map (CommRingCat.ofHom (algebraMap Laurent Ring))
instance toLaurent_open : IsOpenImmersion toLaurent := by unfold toLaurent; infer_instance
@[expose] def embedding : Spec (CommRingCat.of Ring) ⟶ ProjectiveJLine318.scheme ℚ :=
  toLaurent ≫ ProjectiveLineOverlap318.embedding
instance embedding_open : IsOpenImmersion embedding := by unfold embedding; infer_instance

theorem source_open_range : toLaurent.opensRange=PrimeSpectrum.basicOpen derivativeImage := by
  apply TopologicalSpace.Opens.ext
  exact PrimeSpectrum.localization_away_comap_range Ring derivativeImage

/-- Equality of opens on the entire rational prime spectrum, not merely
on complex closed points. The squared factor has the same open complement. -/
theorem source_open_exact : toLaurent.opensRange=
    PrimeSpectrum.basicOpen (ProjectiveLineOverlap318.t+243) ⊓
      PrimeSpectrum.basicOpen ellipticFactor := by
  have hs : PrimeSpectrum.basicOpen ProjectiveLineOverlap318.s=⊤ := by
    have h : PrimeSpectrum.basicOpen ProjectiveLineOverlap318.t ⊓
        PrimeSpectrum.basicOpen ProjectiveLineOverlap318.s=⊤ := by
      rw [←PrimeSpectrum.basicOpen_mul,ProjectiveLineOverlap318.ts,PrimeSpectrum.basicOpen_one]
    apply le_antisymm le_top
    rw [←h]
    exact inf_le_right
  rw [source_open_range,derivative_factorization,PrimeSpectrum.basicOpen_mul,
    PrimeSpectrum.basicOpen_mul,PrimeSpectrum.basicOpen_pow _ 2 (by decide),hs,top_inf_eq]

lemma actual_scalar_square :
    toLaurent ≫ ThreeJFiniteLaurentMap318.finiteTargetMap=Spec.algebraMap Base Ring := by
  rw [toLaurent,ThreeJFiniteLaurentMap318.finiteTargetMap,←Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    ((algebraMap Laurent Ring).comp (algebraMap Base Laurent)))=_
  rw [←IsScalarTower.algebraMap_eq Base Laurent Ring]

/-- Scheme-level etaleness on the exact derivative open of the original
projective j map, proved without any analytic-to-algebraic inference. -/
theorem original_restriction_etale : Etale (embedding ≫ ThreeProjectiveJMap318.map) := by
  rw [embedding,Category.assoc,ThreeJFiniteLaurentMap318.original_scheme_square,
    ←Category.assoc,actual_scalar_square]
  letI := derivative_open_etale
  haveI : Etale (Spec.algebraMap Base Ring) :=
    (HasRingHomProperty.Spec_iff (P:=@Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)
  infer_instance

end ThreeJDerivativeOpen318
