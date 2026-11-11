module
public import ContactRelativeTwistCoefficientIso318
public import ContactRelativeFixedPowerVanishing318
public section
noncomputable section
namespace ContactRelativePowerCoefficientIso318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactRelativeCoefficientChange318 ContactRelativeGeometricTwist318
variable (R S : CommRingCat.{0}) [Algebra ℚ R] [Algebra ℚ S]
  (f : R →ₐ[ℚ] S) (c : Fin 4 → ℚˣ)

/-- Actual pullback of each original fixed-relative-line power is the
power of the freshly constructed target relative line. The comparison
passes through the original geometric T^n twists and their original frames. -/
@[expose] def iso (n : ℕ) :
    (Scheme.Modules.pullback (curveMap R S f c)).obj
      (LineSheafTensorPower318.line (line R c 1) n).object ≅
        (LineSheafTensorPower318.line (line S c 1) n).object :=
  (Scheme.Modules.pullback (curveMap R S f c)).mapIso
    (ContactRelativeTwistPowers318.powerIso R c n) ≪≫
  ContactRelativeTwistCoefficientIso318.iso R S f c (n : ℤ) ≪≫
  (ContactRelativeTwistPowers318.powerIso S c n).symm

/-- The same genuine derived groups are identified by the actual
geometric power comparison, not by matching ranks or presentations. -/
@[expose] def cohomologyIso (n : ℕ) :
    NonreducedLineMayerVietoris318.H1
      (LineSheafPullback318.line (curveMap R S f c)
        (LineSheafTensorPower318.line (line R c 1) n)) ≃+
    NonreducedLineMayerVietoris318.H1
      (LineSheafTensorPower318.line (line S c 1) n) :=
  ((Sheaf.functorH _ 1).mapIso
    ((SheafOfModules.toSheaf (ContactOriginalRelativePolynomialCharts318.curve S c).ringCatSheaf).mapIso
      (iso R S f c n))).addCommGroupIsoToAddEquiv
end ContactRelativePowerCoefficientIso318
