module
public import PELOriginalKernelDeterminantLine318
public section
noncomputable section
namespace PELOriginalDeterminantDescent318
open QuaternionicRealPeriod318 QuaternionicJointPeriodTopology318
open PELJointNormOneAction318 PELEffectiveNormOneAction318 PELPrincipalOrderCoordinates318
open PELOriginalKernelMonodromyCovariance318 PELOriginalFlatPeriodSquare318
open PELOriginalCentralSignTransport318 PELOriginalEvenTensorCocycle318
open PELOriginalEffectiveTensorDescent318 PELOriginalKernelDeterminantLine318

lemma wedge_neg (v : Fin 2 → ComplexVectors) :
    exteriorPower.ιMulti ℂ 2 (fun i => -v i)=exteriorPower.ιMulti ℂ 2 v := by
  have h := (exteriorPower.ιMulti ℂ 2 (M:=ComplexVectors)).toMultilinearMap.map_smul_univ
    (fun _ : Fin 2 => (-1:ℂ)) v
  simpa [Fin.prod_univ_two] using h
@[expose] def unitTransition (u : normOneUnits) (τ : ℂ) (hτ : 0<τ.im) :
    Coordinates ≃ₗ[ℂ] Coordinates := exteriorEquiv (coefficientEquiv u τ hτ)
lemma unitTransition_neg (u v : normOneUnits) (hu : u.val= -v.val)
    (τ : ℂ) (hτ : 0<τ.im) : unitTransition u τ hτ=unitTransition v τ hτ := by
  have hm : (unitTransition u τ hτ).toLinearMap=(unitTransition v τ hτ).toLinearMap := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro z
    change exteriorPower.map 2 (coefficientEquiv u τ hτ).toLinearMap (exteriorPower.ιMulti ℂ 2 z)=
      exteriorPower.map 2 (coefficientEquiv v τ hτ).toLinearMap (exteriorPower.ιMulti ℂ 2 z)
    simp only [exteriorPower.map_apply_ιMulti]
    change exteriorPower.ιMulti ℂ 2 (fun i => coefficientEquiv u τ hτ (z i))=
      exteriorPower.ιMulti ℂ 2 (fun i => coefficientEquiv v τ hτ (z i))
    simp_rw [coefficient_neg u v hu τ hτ]
    exact wedge_neg _
  apply LinearEquiv.ext
  intro x
  exact congrArg (fun f : Coordinates →ₗ[ℂ] Coordinates => f x) hm

lemma unitTransition_effective (u v : normOneUnits) (h : effectiveMap u=effectiveMap v)
    (τ : ℂ) (hτ : 0<τ.im) : unitTransition u τ hτ=unitTransition v τ hτ := by
  have hk : effectiveMap (u*v⁻¹)=1 := by rw [map_mul,map_inv,h,mul_inv_cancel]
  rcases (effectiveMap_eq_one_iff (u*v⁻¹)).mp hk with hp|hn
  · have huv : u.val=v.val := by
      have hv := congrArg (fun x : orderˣ => x*v.val) hp
      simpa [mul_assoc] using hv
    have he : u=v := Subtype.ext huv
    subst u
    rfl
  · have huv : u.val= -v.val := by
      have hv := congrArg (fun x : orderˣ => x*v.val) hn
      simpa [mul_assoc] using hv
    exact unitTransition_neg u v huv τ hτ

lemma unit_cocycle (u v : normOneUnits) (τ : ℂ) (hτ : 0<τ.im) :
    (unitTransition u (parameter v τ) (parameter_positive v τ hτ)).trans
      (unitTransition v τ hτ)=unitTransition (u*v) τ hτ := by
  have hm : ((unitTransition v τ hτ).toLinearMap.comp
      (unitTransition u (parameter v τ) (parameter_positive v τ hτ)).toLinearMap)=
      (unitTransition (u*v) τ hτ).toLinearMap := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro z
    change exteriorPower.map 2 (coefficientEquiv v τ hτ).toLinearMap
      (exteriorPower.map 2 (coefficientEquiv u (parameter v τ)
        (parameter_positive v τ hτ)).toLinearMap (exteriorPower.ιMulti ℂ 2 z))=
      exteriorPower.map 2 (coefficientEquiv (u*v) τ hτ).toLinearMap (exteriorPower.ιMulti ℂ 2 z)
    simp only [exteriorPower.map_apply_ιMulti]
    congr 1
    funext i
    exact coefficient_cocycle u v τ hτ (z i)
  apply LinearEquiv.ext
  intro x
  exact congrArg (fun f : Coordinates →ₗ[ℂ] Coordinates => f x) hm

lemma unit_one (τ : ℂ) (hτ : 0<τ.im) : unitTransition 1 τ hτ=LinearEquiv.refl ℂ Coordinates := by
  have he : coefficientEquiv 1 τ hτ=LinearEquiv.refl ℂ ComplexVectors := by
    ext z;exact coefficient_one τ hτ z
  unfold unitTransition
  rw [he]
  apply LinearEquiv.ext
  intro x
  change exteriorPower.map 2 (LinearMap.id : ComplexVectors →ₗ[ℂ] ComplexVectors) x=x
  rw [exteriorPower.map_id]
  rfl

/-- Actual top-exterior line transition on the effective original base.
Unlike the rank-two kernel, this full line is insensitive to the central sign. -/
@[expose] def transition (g : effectiveGroup) (τ : HalfPlane) : Coordinates ≃ₗ[ℂ] Coordinates :=
  unitTransition (unitLift g) τ τ.property
lemma transition_lift (g : effectiveGroup) (u : normOneUnits) (hu : effectiveMap u=g)
    (τ : HalfPlane) : transition g τ=unitTransition u τ τ.property :=
  unitTransition_effective _ _ ((unitLift_spec g).trans hu.symm) τ τ.property

theorem cocycle (g h : effectiveGroup) (τ : HalfPlane) :
    (transition g (h • τ)).trans (transition h τ)=transition (g*h) τ := by
  have hm : effectiveMap (unitLift g*unitLift h)=g*h := by
    rw [map_mul,unitLift_spec,unitLift_spec]
  rw [transition_lift g (unitLift g) (unitLift_spec g),
    transition_lift h (unitLift h) (unitLift_spec h),
    transition_lift (g*h) (unitLift g*unitLift h) hm]
  have hb := (actual_parameter h τ).symm
  simpa only [hb] using unit_cocycle (unitLift g) (unitLift h) τ τ.property
lemma identity (τ : HalfPlane) : transition 1 τ=LinearEquiv.refl ℂ Coordinates := by
  rw [transition_lift 1 1 (map_one effectiveMap)]
  exact unit_one τ τ.property
end PELOriginalDeterminantDescent318
