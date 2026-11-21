module
public import SelectedGeneralizedGluedCarrier318
public import SelectedGeneralizedInfinityCartier318
public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open SelectedGeneralizedAffineInfinity318 SelectedGeneralizedGluedCarrier318
open SelectedGeneralizedInfinityCartier318

namespace SelectedGeneralizedInstallOriginOpen318

variable {R : Type*} [CommRing R]

abbrev OriginOpen (d : Rˣ) := Spec (CommRingCat.of (OpenRing d))
@[expose] def intoYOpen (d : Rˣ) : OriginOpen d ⟶ Infinity d :=
  Spec.map (CommRingCat.ofHom (algebraMap (Chart d) (OpenRing d)))

instance intoYOpen_open (d : Rˣ) : IsOpenImmersion (intoYOpen d) :=
  IsOpenImmersion.of_isLocalization (den d)

/-- Install the exact identity-isolating chart as an actual open immersion
of the literal generalized glued carrier, not another model. -/
@[expose] def install (d : Rˣ) : OriginOpen d ⟶ Carrier d := intoYOpen d ≫ jY d

instance install_open (d : Rˣ) : IsOpenImmersion (install d) := by
  unfold install
  infer_instance

theorem install_over (d : Rˣ) :
    install d ≫ overBase d = Spec.algebraMap R (OpenRing d) := by
  rw [install,Category.assoc,jY_over]
  unfold intoYOpen Spec.algebraMap
  rw [← Spec.map_comp] <;> rfl

@[expose] def originLift (d : Rˣ) : Base R ⟶ OriginOpen d :=
  Spec.map (CommRingCat.ofHom (augmentation d).toRingHom)

theorem originLift_install (d : Rˣ) : originLift d ≫ install d = identitySection d := by
  unfold originLift install intoYOpen identitySection
  rw [← Category.assoc,← Spec.map_comp]
  have h : (augmentation d).toRingHom.comp (algebraMap (Chart d) (OpenRing d)) =
      (origin d).toRingHom := by
    apply RingHom.ext
    exact augmentation_map d
  change Spec.map (CommRingCat.ofHom ((augmentation d).toRingHom.comp
    (algebraMap (Chart d) (OpenRing d)))) ≫ jY d = _
  rw [h]

end SelectedGeneralizedInstallOriginOpen318

#print axioms SelectedGeneralizedInstallOriginOpen318.install_over
#print axioms SelectedGeneralizedInstallOriginOpen318.originLift_install
