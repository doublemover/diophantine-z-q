module
public import ActualTwoDescentFieldContinuousGaloisCocycles318
public section
noncomputable section
namespace ActualCasselsTateFirstCochainLift318

variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "Gal" => Field.absoluteGaloisGroup F
local instance : DecidableEq Qbar := Classical.decEq _
open ActualTwoDescentEllipticModel318 ActualTwoDescentFieldAlgebraicClosureHalving318
open ActualTwoDescentFieldGaloisPointAction318 ActualTwoDescentFieldGaloisTwoTorsion318
open ActualTwoDescentFieldContinuousGaloisCocycles318

/-- The original geometric value, not an independent binary-coordinate proxy. -/
def originalValue (n : F) (χ : continuousCocycles n) (σ : Gal) :
    Point (algebraMap F Qbar n) :=
  (((χ : Gal →* Multiplicative (closedTwoTorsion n)) σ).toAdd : Point (algebraMap F Qbar n))

lemma originalValue_mul (n : F) (χ : continuousCocycles n) (σ τ : Gal) :
    originalValue n χ (σ*τ)=originalValue n χ σ+originalValue n χ τ := by
  exact congrArg
    (fun T : Multiplicative (closedTwoTorsion n) => (T.toAdd : Point (algebraMap F Qbar n)))
    ((χ : Gal →* Multiplicative (closedTwoTorsion n)).map_mul σ τ)

lemma originalValue_two (n : F) (χ : continuousCocycles n) (σ : Gal) :
    2 • originalValue n χ σ=0 :=
  ((χ : Gal →* Multiplicative (closedTwoTorsion n)) σ).toAdd.property

/-- Pointwise geometric halves form a cochain, not in general a cocycle. -/
def halfCochain (n : F) (hn : n ≠ 0) (χ : continuousCocycles n) (σ : Gal) :
    Point (algebraMap F Qbar n) := actualHalf n hn (originalValue n χ σ)

lemma halfCochain_double (n : F) (hn : n ≠ 0) (χ : continuousCocycles n) (σ : Gal) :
    2 • halfCochain n hn χ σ=originalValue n χ σ := by
  rw [two_nsmul]
  exact actual_half_spec n hn (originalValue n χ σ)

lemma halfCochain_four (n : F) (hn : n ≠ 0) (χ : continuousCocycles n) (σ : Gal) :
    4 • halfCochain n hn χ σ=0 := by
  calc
    4 • halfCochain n hn χ σ=2 • (2 • halfCochain n hn χ σ) := by
      rw [←mul_smul]
    _=0 := by rw [halfCochain_double,originalValue_two]

lemma halfCochain_locally_constant (n : F) (hn : n ≠ 0) (χ : continuousCocycles n) :
    IsLocallyConstant (halfCochain n hn χ) :=
  χ.property.comp (fun T : Multiplicative (closedTwoTorsion n) =>
    actualHalf n hn (T.toAdd : Point (algebraMap F Qbar n)))

/-- The actual Galois coboundary of the chosen half cochain. -/
def halfDefect (n : F) (hn : n ≠ 0) (χ : continuousCocycles n) (σ τ : Gal) :
    Point (algebraMap F Qbar n) :=
  galoisPointHom σ n hn (halfCochain n hn χ τ)-halfCochain n hn χ (σ*τ)+halfCochain n hn χ σ

lemma halfDefect_two (n : F) (hn : n ≠ 0) (χ : continuousCocycles n) (σ τ : Gal) :
    2 • halfDefect n hn χ σ τ=0 := by
  simp only [halfDefect,nsmul_add,nsmul_sub,←map_nsmul,halfCochain_double]
  have hfix : galoisPointHom σ n hn (originalValue n χ τ)=originalValue n χ τ :=
    actual_two_torsion_fixed_subtype σ n hn
      ((χ : Gal →* Multiplicative (closedTwoTorsion n)) τ).toAdd
  rw [hfix,originalValue_mul]
  abel

/-- The defect really lands in the original geometric E[2]. -/
def torsionDefect (n : F) (hn : n ≠ 0) (χ : continuousCocycles n) (σ τ : Gal) :
    closedTwoTorsion n := ⟨halfDefect n hn χ σ τ,halfDefect_two n hn χ σ τ⟩

/-- The cocycle identity retains the actual geometric Galois action. -/
lemma halfDefect_cocycle (n : F) (hn : n ≠ 0) (χ : continuousCocycles n) (σ τ υ : Gal) :
    galoisPointHom σ n hn (halfDefect n hn χ τ υ)-halfDefect n hn χ (σ*τ) υ+
      halfDefect n hn χ σ (τ*υ)-halfDefect n hn χ σ τ=0 := by
  simp only [halfDefect,map_add,map_sub,actual_galois_mul,mul_assoc]
  abel

end ActualCasselsTateFirstCochainLift318
