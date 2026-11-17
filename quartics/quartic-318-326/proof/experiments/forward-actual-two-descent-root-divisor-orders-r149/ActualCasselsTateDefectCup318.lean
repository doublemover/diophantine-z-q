module
public import ActualCasselsTateContinuousDefect318
public import ActualTwoDescentOriginalTorsionPairing318
public section
noncomputable section
namespace ActualCasselsTateDefectCup318

variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "Gal" => Field.absoluteGaloisGroup F
local instance : DecidableEq Qbar := Classical.decEq _
open ActualTwoDescentEllipticModel318 ActualTwoDescentFieldGaloisPointAction318
open ActualTwoDescentFieldGaloisTwoTorsion318 ActualTwoDescentFieldContinuousGaloisCocycles318
open ActualTwoDescentOriginalTorsionPairing318
open ActualCasselsTateFirstCochainLift318 ActualCasselsTateContinuousDefect318

/-- The original geometric torsion value of the given cocycle. -/
def torsionValue (n : F) (χ : continuousCocycles n) (σ : Gal) : closedTwoTorsion n :=
  ((χ : Gal →* Multiplicative (closedTwoTorsion n)) σ).toAdd

lemma torsionValue_mul (n : F) (χ : continuousCocycles n) (σ τ : Gal) :
    torsionValue n χ (σ*τ)=torsionValue n χ σ+torsionValue n χ τ :=
  congrArg Multiplicative.toAdd ((χ : Gal →* Multiplicative (closedTwoTorsion n)).map_mul σ τ)

lemma torsionDefect_add_cocycle (n : F) (hn : n ≠ 0) (χ : continuousCocycles n) (σ τ υ : Gal) :
    torsionDefect n hn χ (σ*τ) υ+torsionDefect n hn χ σ τ=
      torsionDefect n hn χ τ υ+torsionDefect n hn χ σ (τ*υ) := by
  apply Subtype.ext
  change halfDefect n hn χ (σ*τ) υ+halfDefect n hn χ σ τ=
    halfDefect n hn χ τ υ+halfDefect n hn χ σ (τ*υ)
  have h := halfDefect_cocycle n hn χ σ τ υ
  have hfix : galoisPointHom σ n hn (halfDefect n hn χ τ υ)=halfDefect n hn χ τ υ :=
    actual_two_torsion_fixed_subtype σ n hn (torsionDefect n hn χ τ υ)
  rw [hfix] at h
  apply sub_eq_zero.mp
  calc
    _ = -(halfDefect n hn χ τ υ-halfDefect n hn χ (σ*τ) υ+
      halfDefect n hn χ σ (τ*υ)-halfDefect n hn χ σ τ) := by abel
    _ = 0 := by rw [h,neg_zero]

/-- A continuous degree-three cochain from the ACTUAL half-defect and the
original geometric E[2] coordinate form. Geometric Weil identification is
not asserted, and no local invariant or Cassels-Tate value is defined. -/
def defectCup (n : F) (hn : n ≠ 0) (χ ψ : continuousCocycles n) (σ τ υ : Gal) : ZMod 2 :=
  originalTorsionPairing n hn (torsionDefect n hn χ σ τ) (torsionValue n ψ υ)

/-- The explicit degree-three cocycle identity, with the original trivial
Galois action on the coefficient F2. -/
lemma defectCup_cocycle (n : F) (hn : n ≠ 0) (χ ψ : continuousCocycles n) (σ τ υ ω : Gal) :
    defectCup n hn χ ψ τ υ ω-defectCup n hn χ ψ (σ*τ) υ ω+
      defectCup n hn χ ψ σ (τ*υ) ω-defectCup n hn χ ψ σ τ (υ*ω)+
      defectCup n hn χ ψ σ τ υ=0 := by
  have h := congrArg (fun T => originalTorsionPairing n hn T (torsionValue n ψ ω))
    (torsionDefect_add_cocycle n hn χ σ τ υ)
  simp only [actual_original_pairing_add_left] at h
  simp only [defectCup,torsionValue_mul,actual_original_pairing_add_right]
  calc
    _ = (originalTorsionPairing n hn (torsionDefect n hn χ τ υ) (torsionValue n ψ ω)+
      originalTorsionPairing n hn (torsionDefect n hn χ σ (τ*υ)) (torsionValue n ψ ω))-
      (originalTorsionPairing n hn (torsionDefect n hn χ (σ*τ) υ) (torsionValue n ψ ω)+
      originalTorsionPairing n hn (torsionDefect n hn χ σ τ) (torsionValue n ψ ω)) := by abel
    _ = 0 := by rw [h,sub_self]

lemma defectCup_locally_constant (n : F) (hn : n ≠ 0) (χ ψ : continuousCocycles n) :
    IsLocallyConstant (fun g : Gal × Gal × Gal => defectCup n hn χ ψ g.1 g.2.1 g.2.2) := by
  have hd : IsLocallyConstant (fun g : Gal × Gal × Gal => torsionDefect n hn χ g.1 g.2.1) :=
    (torsionDefect_locally_constant n hn χ).comp_continuous
      (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  have hp : IsLocallyConstant (torsionValue n ψ) :=
    ψ.property.comp (fun T : Multiplicative (closedTwoTorsion n) => T.toAdd)
  have ht : IsLocallyConstant (fun g : Gal × Gal × Gal => torsionValue n ψ g.2.2) :=
    hp.comp_continuous (continuous_snd.comp continuous_snd)
  exact (hd.prodMk ht).comp (fun z => originalTorsionPairing n hn z.1 z.2)

end ActualCasselsTateDefectCup318
