module
public import ThreePoleCertificates318
public section
noncomputable section
namespace ThreeDetectorUniformFamily318
open Filter CircuitReplay ContactChainReal318 FixedDetectorScales318
open scoped Topology
set_option maxHeartbeats 0

@[expose] def c₁ (labels : Fin 4 → ℤ) : ℚ := (product labels).re+normProduct labels
@[expose] def c₂ (labels : Fin 4 → ℤ) : ℚ := normProduct labels
@[expose] def witness (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) (t : ℚ) : Assignment :=
  ThreeDetectorPrePole318.fill (DetectorGateWitness318.witness q labels h) (c₁ labels) (c₂ labels) t

@[expose] def contactParameter (labels : Fin 4 → ℤ) (t : ℚ) (j : Fin 3) : ℚ :=
  if j=0 then t else if j=1 then ScaledContactWeights318.parameter (c₁ labels) t
  else ScaledContactWeights318.parameter (c₂ labels) t
@[expose] def squareFactor (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) (t : ℚ) (j : Fin 3) : ℚ :=
  if j=0 then PoleInputWitness318.squareFactor (DetectorGateWitness318.witness q labels h) t
  else if j=1 then ScaledDetectorChain318.squareFactor (DetectorGateWitness318.witness q labels h) (c₁ labels) t
  else ScaledDetectorChain318.squareFactor (DetectorGateWitness318.witness q labels h) (c₂ labels) t

/-- The local prime contacts remain the exact three original rational
parameters, with explicit rational square factors at the same stored b's. -/
lemma witness_squareclass (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) (t : ℚ) (j : Fin 3) :
    witness q labels h t (190+51*j.val)=
      ContactWeightWitness318.contact (contactParameter labels t j)*(squareFactor q labels h t j)^2 := by
  fin_cases j
  · simpa [witness,contactParameter,squareFactor,ThreeDetectorPrePole318.fill190] using
      PoleInputWitness318.pole_squareclass (DetectorGateWitness318.witness q labels h) t
  · simpa [witness,contactParameter,squareFactor,ThreeDetectorPrePole318.fill241] using
      ScaledDetectorChain318.squareclass (DetectorGateWitness318.witness q labels h) (c₁ labels) t
  · simpa [witness,contactParameter,squareFactor,ThreeDetectorPrePole318.fill292] using
      ScaledDetectorChain318.squareclass (DetectorGateWitness318.witness q labels h) (c₂ labels) t

lemma squareFactor_ne (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) (t : ℚ) (j : Fin 3)
    (hb : 0<witness q labels h t (190+51*j.val)) : squareFactor q labels h t j≠0 := by
  intro hz
  rw [witness_squareclass,hz] at hb
  norm_num at hb

lemma pole_valuation (v : AddValuation ℚ (WithTop ℤ)) (q : ℚ) (labels : Fin 4 → ℤ)
    (h : ℤ) (t : ℚ) (j : Fin 3) :
    v (witness q labels h t (190+51*j.val))=
      v (ContactWeightWitness318.contact (contactParameter labels t j))+2•v (squareFactor q labels h t j) := by
  rw [witness_squareclass,v.map_mul,v.map_pow]

/-- The three contact scales and threshold precede h. Compact membership is
kept explicit here and discharged in the same mixed-CRT consumer below. -/
theorem uniform_family (S q : ℚ) (labels : Fin 4 → ℤ) (hn : ∀ j, labels j≠0)
    (K : Set Coeff) (hK : IsCompact K) :
    ∀ᶠ t : ℚ in atTop, ∀ h : ℤ, h≠0 → h≠1 →
      (∀ j, RealGuardTrace318.guardValue (labels j) (h • LocalGenerator318.P)≠0) →
      project (DetectorGateWitness318.witness q labels h)∈K →
      let pre := witness q labels h t
      pre 0=q ∧ Constraints (ThreeDetectorPrePole318.rows S) pre ∧
      (∀ j : Fin 3, 0<pre (190+51*j.val) ∧ pre (190+51*j.val)<17) ∧
      (∀ P₀ : NormalizedPolePoints318.PointPair (pre 190),
       ∀ P₁ : NormalizedPolePoints318.PointPair (pre 241),
       ∀ P₂ : NormalizedPolePoints318.PointPair (pre 292),
       ∃ out : Assignment, out 0=q ∧
         (∀ j : Fin 3, out (190+51*j.val)=pre (190+51*j.val)) ∧
         Constraints ((Raw318FinalReplay.stage0 S).take 263) out) := by
  have hc₁ : c₁ labels≠0 := sum_ne labels hn
  have hc₂ : c₂ labels≠0 := normProduct_ne labels hn
  filter_upwards [UniformPoleFamilies318.uniform_actual_family S q labels K hK,
    UniformScaledPoleDomain318.uniform_pole_domain (c₁ labels) hc₁ K hK,
    UniformScaledPoleDomain318.uniform_pole_domain (c₂ labels) hc₂ K hK,
    eventually_gt_atTop (2:ℚ)] with t hfirst hsecond hthird ht
  intro h h0 h1 hg hwK
  let w := DetectorGateWitness318.witness q labels h
  obtain ⟨hin,hrows,hpos,hsmall,hs,hclass⟩ := hfirst h h0 h1 hg hwK
  obtain ⟨hr₁,hpos₁,hsmall₁⟩ := hsecond.2 w hwK
  obtain ⟨hr₂,hpos₂,hsmall₂⟩ := hthird.2 w hwK
  have hs₁ : c₁ labels=w 143+w 145 := by
    have he := congrArg QuadraticAlgebra.re (actual_product q labels hn h hg)
    have hn' := actual_norm q labels hn h hg
    simpa only [ConcreteG8Domain.pair,c₁,w,hn'] using congrArg (fun a => a+normProduct labels) he.symm
  have hs₂ : c₂ labels=w 145 := (actual_norm q labels hn h hg).symm
  have hnp := ThreeDetectorPrePole318.nonpole_rows S w (c₁ labels) (c₂ labels) t hrows
    (by linarith) hc₁ hc₂ hs₁ hs₂
    (by unfold ScaledContactWeights318.delta; linarith [hsecond.1])
    (by unfold ScaledContactWeights318.delta; linarith [hthird.1])
    (ContactChainLimits318.contact_positive _ hsecond.1).ne'
    (ContactChainLimits318.contact_positive _ hthird.1).ne' hr₁ hr₂
  have hb : ∀ j : Fin 3, 0<witness q labels h t (190+51*j.val) ∧
      witness q labels h t (190+51*j.val)<17 := by
    intro j
    fin_cases j
    · simpa [witness,ThreeDetectorPrePole318.fill190,PoleInputWitness318.fill] using And.intro hpos hsmall
    · simpa [witness,ThreeDetectorPrePole318.fill241] using And.intro hpos₁ hsmall₁
    · simpa [witness,ThreeDetectorPrePole318.fill292] using And.intro hpos₂ hsmall₂
  refine ⟨?_,hnp,hb,?_⟩
  · rw [witness,ThreeDetectorPrePole318.fill_input,DetectorGateWitness318.witness_input]
  · intro P₀ P₁ P₂
    let pre := witness q labels h t
    let C₀ := P₀.certificate (ne_of_gt (hb 0).1)
    let C₁ := P₁.certificate (ne_of_gt (hb 1).1)
    let C₂ := P₂.certificate (ne_of_gt (hb 2).1)
    refine ⟨ThreePoleCertificates318.fill pre C₀ C₁ C₂,?_,?_,?_⟩
    · simp [ThreePoleCertificates318.fill,pre,witness,ThreeDetectorPrePole318.fill_input,
        DetectorGateWitness318.witness_input]
    · intro j
      fin_cases j <;> simp [ThreePoleCertificates318.fill, pre]
    · exact ThreePoleCertificates318.first263 S pre C₀ C₁ C₂ hnp

end ThreeDetectorUniformFamily318
