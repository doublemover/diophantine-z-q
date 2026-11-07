module
public import HeightOneDVR318
public import ActualDVRCompletion318
public import CompletionDescent318
public import Mathlib.AlgebraicGeometry.Properties
public section
noncomputable section
namespace AffineHeightOneStalk318
set_option maxHeartbeats 600000
open AlgebraicGeometry
variable (R:Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]

/-- Actual prime-spectrum points of codimension one, not abstract local rings. -/
abbrev Point:={x:PrimeSpectrum R // x.asIdeal.height=1}

abbrev Stalk (x:Point R):=((Spec (CommRingCat.of R)).presheaf.stalk x.val)

/-- The coefficient map is the structure sheaf's actual canonical germ map. -/
instance stalk_algebra (x:Point R) : Algebra R (Stalk R x) :=
  inferInstanceAs (Algebra R ((Spec.structureSheaf (CommRingCat.of R)).presheaf.stalk x.val))

theorem coefficient_germ (x:Point R) (r:R) :
    algebraMap R (Stalk R x) r =
      StructureSheaf.toStalk (CommRingCat.of R) x.val r := rfl

@[expose] def stalkEquiv (x:Point R) : Stalk R x ≃+* Localization.AtPrime x.val.asIdeal :=
  (Spec.stalkIso (CommRingCat.of R) x.val).commRingCatIsoToRingEquiv

instance stalk_domain (x:Point R) : IsDomain (Stalk R x) :=
  (stalkEquiv R x).injective.isDomain (stalkEquiv R x).toRingHom

instance stalk_dvr (x:Point R) : IsDiscreteValuationRing (Stalk R x) := by
  letI:=HeightOneDVR318.localization x.val.asIdeal x.property
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing (stalkEquiv R x).symm

/-- The completed local ring is the actual completion of the actual Spec stalk. -/
abbrev CompletedStalk (x:Point R):=ActualDVRCompletion318.Completion (Stalk R x)

theorem completed_stalk_dvr (x:Point R) : IsDiscreteValuationRing (CompletedStalk R x) :=
  inferInstance

theorem completed_stalk_faithfullyFlat (x:Point R) :
    Module.FaithfullyFlat (Stalk R x) (CompletedStalk R x) :=
  CompletionDescent318.completion_faithfullyFlat (Stalk R x)

theorem completed_stalk_value (x:Point R) (a:Stalk R x) :
    IsDiscreteValuationRing.addVal (CompletedStalk R x)
      (algebraMap (Stalk R x) (CompletedStalk R x) a)=
        IsDiscreteValuationRing.addVal (Stalk R x) a :=
  ActualDVRCompletion318.completion_value (Stalk R x) a

end AffineHeightOneStalk318
