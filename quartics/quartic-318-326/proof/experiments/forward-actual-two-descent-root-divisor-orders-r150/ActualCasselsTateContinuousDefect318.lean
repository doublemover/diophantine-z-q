module
public import ActualCasselsTateFirstCochainLift318
public section
noncomputable section
namespace ActualCasselsTateContinuousDefect318

variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "Gal" => Field.absoluteGaloisGroup F
local instance : DecidableEq Qbar := Classical.decEq _
open ActualTwoDescentEllipticModel318 ActualTwoDescentFieldAlgebraicClosureHalving318
open ActualTwoDescentFieldGaloisPointAction318 ActualTwoDescentFieldGaloisTwoTorsion318
open ActualTwoDescentFieldGaloisLocallyConstant318 ActualTwoDescentFieldContinuousGaloisCocycles318
open ActualCasselsTateFirstCochainLift318

/-- Locally constant geometric values and their actual Galois translates vary
locally constantly jointly. This does not require an equivariant half choice. -/
lemma action_half_locally_constant (n : F) (hn : n ≠ 0) (χ : continuousCocycles n) :
    IsLocallyConstant (fun g : Gal × Gal => galoisPointHom g.1 n hn (halfCochain n hn χ g.2)) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  rintro ⟨σ,τ⟩
  obtain ⟨U,hU,hσ,hAct⟩ := (actual_galois_point_locally_constant n hn
    (halfCochain n hn χ τ)).exists_open σ
  obtain ⟨V,hV,hτ,hHalf⟩ := (halfCochain_locally_constant n hn χ).exists_open τ
  refine ⟨Set.prod U V,hU.prod hV,⟨hσ,hτ⟩,?_⟩
  rintro ⟨σ',τ'⟩ ⟨hσ',hτ'⟩
  change galoisPointHom σ' n hn (halfCochain n hn χ τ')=
    galoisPointHom σ n hn (halfCochain n hn χ τ)
  rw [hHalf τ' hτ']
  exact hAct σ' hσ'

lemma halfDefect_locally_constant (n : F) (hn : n ≠ 0) (χ : continuousCocycles n) :
    IsLocallyConstant (fun g : Gal × Gal => halfDefect n hn χ g.1 g.2) := by
  have hm : IsLocallyConstant (fun g : Gal × Gal => halfCochain n hn χ (g.1*g.2)) :=
    (halfCochain_locally_constant n hn χ).comp_continuous (continuous_fst.mul continuous_snd)
  have hf : IsLocallyConstant (fun g : Gal × Gal => halfCochain n hn χ g.1) :=
    (halfCochain_locally_constant n hn χ).comp_continuous continuous_fst
  exact ((action_half_locally_constant n hn χ).prodMk (hm.prodMk hf)).comp
    (fun z => z.1-z.2.1+z.2.2)

/-- The actual E[2]-valued defect is a locally constant two-cochain. -/
lemma torsionDefect_locally_constant (n : F) (hn : n ≠ 0) (χ : continuousCocycles n) :
    IsLocallyConstant (fun g : Gal × Gal => torsionDefect n hn χ g.1 g.2) := by
  apply IsLocallyConstant.desc _
    (fun T : closedTwoTorsion n => (T : Point (algebraMap F Qbar n)))
  · exact halfDefect_locally_constant n hn χ
  · intro a b h
    exact Subtype.ext h

end ActualCasselsTateContinuousDefect318
