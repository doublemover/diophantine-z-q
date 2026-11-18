module
public import ActualCasselsTateUnitDefect318
public section
noncomputable section
namespace ActualCasselsTateRealDetectionConsumer318
open ActualCasselsTateUnitCoefficients318 ActualCasselsTateUnitDefect318
open ActualCasselsTateDefectCup318 ActualCasselsTateEverywherePrimitive318
open ActualTwoDescentFieldContinuousGaloisCocycles318
open ActualTwoDescentContinuousEllipticCocycles318 ActualTwoDescentTorsionIntoFullCocycles318
open ActualTwoDescentActualShaDefinition318

local notation "G" => Field.absoluteGaloisGroup ℚ
local notation "GR" => Field.absoluteGaloisGroup ℝ
local notation "loc" => Field.absoluteGaloisGroup.map (algebraMap ℚ ℝ)
local notation "U" => (AlgebraicClosure ℚ)ˣ

/-- Explicit arithmetic input interface for the injective real restriction
in continuous H³(ℚ,ℤ/2). This is a proposition, NOT a theorem or an axiom. -/
def RealDetectsBinaryThree : Prop :=
  ∀ c : G → G → G → ZMod 2,
    IsLocallyConstant (fun t : G × G × G => c t.1 t.2.1 t.2.2) →
    (∀ x y z t, c y z t - c (x*y) z t + c x (y*z) t - c x y (z*t) + c x y z = 0) →
    (∃ b : GR → GR → ZMod 2,
      IsLocallyConstant (fun s : GR × GR => b s.1 s.2) ∧
      ∀ x y z, b y z - b (x*y) z + b x (y*z) - b x y = c (loc x) (loc y) (loc z)) →
    ∃ b : G → G → ZMod 2,
      IsLocallyConstant (fun s : G × G => b s.1 s.2) ∧
      ∀ x y z, b y z - b (x*y) z + b x (y*z) - b x y = c x y z

/-- Only real binary detection is imported as a premise. Sha supplies
the real binary primitive for the same cochain. The returned global unit
primitive uses the genuine action and the same binary lift pointwise. -/
theorem actual_global_primitive_of_real_detection
    (hdetect : RealDetectsBinaryThree) (n : ℚ) (hn : n ≠ 0)
    (χ ψ : continuousCocycles n)
    (hSha : fullClassHom n hn (torsionFullCocycle n hn χ) ∈ actualSha n hn) :
    ∃ b : G → G → ZMod 2,
      IsLocallyConstant (fun s : G × G => b s.1 s.2) ∧
      (∀ x y z, b y z - b (x*y) z + b x (y*z) - b x y = defectCup n hn χ ψ x y z) ∧
      IsLocallyConstant (fun s : G × G => (binaryUnit (b s.1 s.2) : U)) ∧
      ∀ x y z, unitDTwo (fun a t : G => binaryUnit (b a t)) x y z = unitDefect n hn χ ψ x y z := by
  obtain ⟨b,hb,hd⟩ := hdetect (defectCup n hn χ ψ)
    (defectCup_locally_constant n hn χ ψ) (defectCup_cocycle n hn χ ψ)
    (actual_sha_everywhere_primitive n hn χ ψ hSha).1
  refine ⟨b,hb,hd,hb.comp (fun a : ZMod 2 => (binaryUnit a : U)),?_⟩
  intro x y z
  simp only [unitDTwo_binary,hd,unitDefect]
end ActualCasselsTateRealDetectionConsumer318
