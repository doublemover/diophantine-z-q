module
public import ActualPreparedDescentInterface318
public import SelectedPoleFullSource318
public section
noncomputable section
namespace ActualFourPolePreparation318
open ActualPreparedPoleMutualRoots318 ActualPreparedPoleSquarefreeClasses318
open ActualTwoDescentMordellWeilControl318 ActualTwoDescentEllipticModel318
open TwoTwistPointRealization318

/-- The three literal contact poles use their original common q, labels,
h and t. The preparation conjunction is consumed without replacing a pole. -/
def contact (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) (t : ℚ)
    (H : ThreeSelectedPolePreparation318.Prepared q labels h t) (j : Fin 3) :
    Preparation (ThreeDetectorUniformFamily318.witness q labels h t (190+51*j.val)) :=
  Preparation.of_conditions (H j)

/-- The original scalar support preparation supplies its exact depths
4,2,2 and local roots. Only the already-exported scalar-domain bounds are
used, at the SAME labels and index. -/
def scalar (a : ℤ) (labels : Fin 4 → ℤ) (h : ℕ)
    (H : AllScalarSupportPreparation318.Prepared a labels h)
    (hb : 0<PreparedIntegerSource318.scalarB (a:ℚ) labels (h:ℤ) ∧
      PreparedIntegerSource318.scalarB (a:ℚ) labels (h:ℤ)<17) :
    Preparation (PreparedIntegerSource318.scalarB (a:ℚ) labels (h:ℤ)) := by
  obtain ⟨hlocal,hden,_⟩ := H
  obtain ⟨_,_,_,_,v2,v3,v17,s2,s3,_⟩ := hlocal
  have hv2 : padicValRat 2 (PreparedIntegerSource318.scalarB (a:ℚ) labels (h:ℤ))=4 := v2
  have hv3 : padicValRat 3 (PreparedIntegerSource318.scalarB (a:ℚ) labels (h:ℤ))=2 := v3
  have hv17 : padicValRat 17 (PreparedIntegerSource318.scalarB (a:ℚ) labels (h:ℤ))=2 := v17
  refine ⟨hb.1,hb.2,hden,s2,?_,s3,?_,?_⟩
  · omega
  · omega
  · omega

/-- The original three stored contact slots and original scalar pole,
all at one index. This array is bookkeeping, not an existential new family. -/
def actualPoles (a : ℤ) (labels : Fin 4 → ℤ) (h : ℕ) (t : ℚ) : Fin 4 → ℚ :=
  ![ThreeDetectorUniformFamily318.witness (a:ℚ) labels (h:ℤ) t 190,
    ThreeDetectorUniformFamily318.witness (a:ℚ) labels (h:ℤ) t 241,
    ThreeDetectorUniformFamily318.witness (a:ℚ) labels (h:ℤ) t 292,
    PreparedIntegerSource318.scalarB (a:ℚ) labels (h:ℤ)]

theorem prepared_four (a : ℤ) (labels : Fin 4 → ℤ) (h : ℕ) (t : ℚ)
    (Hcontact : ThreeSelectedPolePreparation318.Prepared (a:ℚ) labels (h:ℤ) t)
    (Hscalar : AllScalarSupportPreparation318.Prepared a labels h)
    (hb : 0<PreparedIntegerSource318.scalarB (a:ℚ) labels (h:ℤ) ∧
      PreparedIntegerSource318.scalarB (a:ℚ) labels (h:ℤ)<17) :
    ∀ i, Preparation (actualPoles a labels h t i) := by
  intro i
  fin_cases i
  · exact contact (a:ℚ) labels (h:ℤ) t Hcontact 0
  · exact contact (a:ℚ) labels (h:ℤ) t Hcontact 1
  · exact contact (a:ℚ) labels (h:ℤ) t Hcontact 2
  · exact scalar a labels h Hscalar hb

/-- A literal actual-source interface to simultaneous finite descent.
No caller residue, support, mutual-symbol, prime-array or MW-control data
is required. Genuine infinitude of BOTH rational point groups for each
constructed twist remains explicit, rather than inferred from local data. -/
theorem actual_four_descent (a : ℤ) (labels : Fin 4 → ℤ) (h : ℕ) (t : ℚ)
    (Hcontact : ThreeSelectedPolePreparation318.Prepared (a:ℚ) labels (h:ℤ) t)
    (Hscalar : AllScalarSupportPreparation318.Prepared a labels h)
    (hb : 0<PreparedIntegerSource318.scalarB (a:ℚ) labels (h:ℤ) ∧
      PreparedIntegerSource318.scalarB (a:ℚ) labels (h:ℤ)<17) (N : ℕ) :
    ∃ (C : ∀ i, Classes (actualPoles a labels h t i)) (n : Fin 4 → ℕ),
      (∀ i, N<n i ∧ Squarefree (n i) ∧ Squarefree (n i*(C i).theta) ∧
        (n i:ZMod 12)=11 ∧ (n i*(C i).theta:ZMod 12)=11 ∧
        MordellWeilControl (n i) (C i).beta ∧
        MordellWeilControl (n i*(C i).theta) (C i).beta) ∧
      ((∀ i, Infinite (Point (n i:ℚ))) →
        (∀ i, Infinite (Point ((n i*(C i).theta:ℕ):ℚ))) →
        Nonempty (∀ i, Realization (actualPoles a labels h t i))) :=
  ActualPreparedDescentInterface318.actual_four_prepared_poles
    (actualPoles a labels h t) (prepared_four a labels h t Hcontact Hscalar hb) N

end ActualFourPolePreparation318
