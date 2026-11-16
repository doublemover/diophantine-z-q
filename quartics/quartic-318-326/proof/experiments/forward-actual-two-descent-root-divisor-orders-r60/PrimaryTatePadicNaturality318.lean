module
public import PrimaryTatePadicModule318
public import PrueferTateResidueBridge318
import all PrueferTateResidueBridge318
import all DyadicResidueInverseLimit318
import all PrueferCanonicalTateTower318
import all PrueferBoundedCoordinates318
import all PrimaryTateTower318
public section
noncomputable section
namespace PrimaryTatePadicNaturality318
open PrimaryTateTower318 PrimaryTatePadicModule318
open ActualTwoDescentDyadicPrueferModel318 PrueferCanonicalTateTower318
open PrueferBoundedCoordinates318 PrueferTateResidueBridge318

/-- An actual ambient additive equivalence induces a linear equivalence
of the genuine compatible towers for their natural finite-residue actions. -/
def mapLinearEquiv {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) :
    letI := naturalModule G
    letI := naturalModule H
    tower G ≃ₗ[ℤ_[2]] tower H := by
  letI := naturalModule G
  letI := naturalModule H
  exact { mapEquiv e with
    map_smul' := by
      intro a x
      apply Subtype.ext
      funext n
      change e ((PadicInt.toZModPow n a).val • x.val n) =
        (PadicInt.toZModPow n a).val • e (x.val n)
      exact map_nsmul e _ _ }

/-- The explicit residue equivalence respects the independently defined
natural tower action, rather than defining it by transport. -/
theorem scalar_padicEquiv (a b : ℤ_[2]) :
    scalar a (padicEquiv b) = padicEquiv (a*b) := by
  apply Subtype.ext
  funext n
  apply Subtype.ext
  change (PadicInt.toZModPow n a).val • encode n (PadicInt.toZModPow n b).val =
    encode n (PadicInt.toZModPow n (a*b)).val
  rw [map_mul, ZMod.val_mul, encode_mod]
  rw [mul_nsmul']

/-- Linear Z2 identification for the natural module structure on the
literal actual Prüfer compatible tower. -/
def naturalPadicEquiv :
    letI := naturalModule (Additive PrueferTwo)
    ℤ_[2] ≃ₗ[ℤ_[2]] tower (Additive PrueferTwo) := by
  letI := naturalModule (Additive PrueferTwo)
  exact { padicEquiv with
    map_smul' := fun a b => (scalar_padicEquiv a b).symm }

theorem naturalPadicEquiv_one : naturalPadicEquiv 1 = canonicalTower :=
  padicEquiv_one

end PrimaryTatePadicNaturality318
