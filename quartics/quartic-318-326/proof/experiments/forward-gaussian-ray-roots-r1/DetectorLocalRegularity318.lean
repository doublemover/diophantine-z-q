module
public import PadeLocalRegularity318
public section
noncomputable section
namespace DetectorLocalRegularity318
open ArithmeticIndexRegularity318 DetectorGateWitness318
set_option maxHeartbeats 1000000
variable (p : ℕ) [Fact p.Prime] (h₀ : ℤ) (w : ℤ → CircuitReplay.Assignment)
  (hw : ∀ i, QRegular p h₀ (fun h => w h i))

include hw in
lemma value118_regular : QRegular p h₀ (fun h => value118 (w h)) := by
  unfold value118
  index_regularity

include hw in
lemma value119_regular : QRegular p h₀ (fun h => value119 (w h)) := by
  unfold value119
  index_regularity

include hw in
lemma value120_regular : QRegular p h₀ (fun h => value120 (w h)) := by
  unfold value120
  index_regularity

include hw in
lemma value121_regular : QRegular p h₀ (fun h => value121 (w h)) := by
  unfold value121
  index_regularity

include hw in
lemma value122_regular : QRegular p h₀ (fun h => value122 (w h)) := by
  unfold value122
  index_regularity

include hw in
lemma value123_regular : QRegular p h₀ (fun h => value123 (w h)) := by
  have h119 := value119_regular p h₀ w hw
  have h120 := value120_regular p h₀ w hw
  have h121 := value121_regular p h₀ w hw
  have h122 := value122_regular p h₀ w hw
  unfold value123
  index_regularity

include hw in
lemma value124_regular : QRegular p h₀ (fun h => value124 (w h)) := by
  have h119 := value119_regular p h₀ w hw
  have h120 := value120_regular p h₀ w hw
  have h121 := value121_regular p h₀ w hw
  have h122 := value122_regular p h₀ w hw
  unfold value124
  index_regularity

include hw in
lemma value125_regular : QRegular p h₀ (fun h => value125 (w h)) := by
  unfold value125
  index_regularity

include hw in
lemma value126_regular : QRegular p h₀ (fun h => value126 (w h)) := by
  unfold value126
  index_regularity

include hw in
lemma value127_regular : QRegular p h₀ (fun h => value127 (w h)) := by
  unfold value127
  index_regularity

include hw in
lemma value128_regular : QRegular p h₀ (fun h => value128 (w h)) := by
  unfold value128
  index_regularity

include hw in
lemma value129_regular : QRegular p h₀ (fun h => value129 (w h)) := by
  unfold value129
  index_regularity

include hw in
lemma value130_regular : QRegular p h₀ (fun h => value130 (w h)) := by
  unfold value130
  index_regularity

include hw in
lemma value131_regular : QRegular p h₀ (fun h => value131 (w h)) := by
  unfold value131
  index_regularity

include hw in
lemma value132_regular : QRegular p h₀ (fun h => value132 (w h)) := by
  unfold value132
  index_regularity

include hw in
lemma value133_regular : QRegular p h₀ (fun h => value133 (w h)) := by
  unfold value133
  index_regularity

include hw in
lemma value134_regular : QRegular p h₀ (fun h => value134 (w h)) := by
  unfold value134
  index_regularity

include hw in
lemma value135_regular : QRegular p h₀ (fun h => value135 (w h)) := by
  have h118 := value118_regular p h₀ w hw
  unfold value135
  index_regularity

include hw in
lemma value136_regular : QRegular p h₀ (fun h => value136 (w h)) := by
  have h118 := value118_regular p h₀ w hw
  unfold value136
  index_regularity

include hw in
lemma value137_regular : QRegular p h₀ (fun h => value137 (w h)) := by
  have h123 := value123_regular p h₀ w hw
  have h124 := value124_regular p h₀ w hw
  unfold value137
  index_regularity

include hw in
lemma value138_regular : QRegular p h₀ (fun h => value138 (w h)) := by
  have h123 := value123_regular p h₀ w hw
  have h124 := value124_regular p h₀ w hw
  unfold value138
  index_regularity

include hw in
lemma value139_regular : QRegular p h₀ (fun h => value139 (w h)) := by
  unfold value139
  index_regularity

include hw in
lemma value140_regular : QRegular p h₀ (fun h => value140 (w h)) := by
  unfold value140
  index_regularity

include hw in
lemma value141_regular : QRegular p h₀ (fun h => value141 (w h)) := by
  have h139 := value139_regular p h₀ w hw
  have h140 := value140_regular p h₀ w hw
  unfold value141
  index_regularity

include hw in
lemma value142_regular : QRegular p h₀ (fun h => value142 (w h)) := by
  have h139 := value139_regular p h₀ w hw
  have h140 := value140_regular p h₀ w hw
  unfold value142
  index_regularity

include hw in
lemma value143_regular : QRegular p h₀ (fun h => value143 (w h)) := by
  have h141 := value141_regular p h₀ w hw
  have h142 := value142_regular p h₀ w hw
  unfold value143
  index_regularity

include hw in
lemma value144_regular : QRegular p h₀ (fun h => value144 (w h)) := by
  have h141 := value141_regular p h₀ w hw
  have h142 := value142_regular p h₀ w hw
  unfold value144
  index_regularity

include hw in
lemma value145_regular : QRegular p h₀ (fun h => value145 (w h)) := by
  have h143 := value143_regular p h₀ w hw
  have h144 := value144_regular p h₀ w hw
  unfold value145
  index_regularity

include hw in
/-- All28 original detector/product gates preserve local regularity.
Their literal finite source order and coefficient formulas are unchanged. -/
lemma fill_regular (i : ℕ) : QRegular p h₀ (fun h => fill (w h) i) := by
  have h118 := value118_regular p h₀ w hw
  have h119 := value119_regular p h₀ w hw
  have h120 := value120_regular p h₀ w hw
  have h121 := value121_regular p h₀ w hw
  have h122 := value122_regular p h₀ w hw
  have h123 := value123_regular p h₀ w hw
  have h124 := value124_regular p h₀ w hw
  have h125 := value125_regular p h₀ w hw
  have h126 := value126_regular p h₀ w hw
  have h127 := value127_regular p h₀ w hw
  have h128 := value128_regular p h₀ w hw
  have h129 := value129_regular p h₀ w hw
  have h130 := value130_regular p h₀ w hw
  have h131 := value131_regular p h₀ w hw
  have h132 := value132_regular p h₀ w hw
  have h133 := value133_regular p h₀ w hw
  have h134 := value134_regular p h₀ w hw
  have h135 := value135_regular p h₀ w hw
  have h136 := value136_regular p h₀ w hw
  have h137 := value137_regular p h₀ w hw
  have h138 := value138_regular p h₀ w hw
  have h139 := value139_regular p h₀ w hw
  have h140 := value140_regular p h₀ w hw
  have h141 := value141_regular p h₀ w hw
  have h142 := value142_regular p h₀ w hw
  have h143 := value143_regular p h₀ w hw
  have h144 := value144_regular p h₀ w hw
  have h145 := value145_regular p h₀ w hw
  unfold fill
  split <;> index_regularity

/-- Actual full detector coefficients, not arbitrary continuous replacements.
Only the center's genuine compression and rational guard domains are inputs. -/
theorem actual
    (hb : ∀ a b h₀ : ℤ, LocalIndexRegularity318.Regular h₀
      (fun h => ActualOrbitLocalFilter318.error p (a+b*h)))
    (q : ℚ) (labels : Fin 4 → ℤ) (hzero : h₀≠0) (hone : h₀≠1)
    (hg : RealGuardWitness318.Guards (CoherentMultiplePrefix318.u labels h₀)) (i : ℕ) :
    QRegular p h₀ (fun h => witness q labels h i) :=
  fill_regular p h₀ (fun h => ActualPadeRatios318.witness q labels h)
    (PadeLocalRegularity318.actual p h₀ hb q labels hzero hone hg) i

/-- The entire exact Fin146 coefficient vector has one local exponent. -/
theorem project_regular
    (hb : ∀ a b h₀ : ℤ, LocalIndexRegularity318.Regular h₀
      (fun h => ActualOrbitLocalFilter318.error p (a+b*h)))
    (q : ℚ) (labels : Fin 4 → ℤ) (hzero : h₀≠0) (hone : h₀≠1)
    (hg : RealGuardWitness318.Guards (CoherentMultiplePrefix318.u labels h₀)) :
    LocalIndexRegularity318.Regular h₀
      (fun h => PadicDetectorCoefficients318.project p (witness q labels h)) := by
  change LocalIndexRegularity318.Regular h₀
    (fun h (i : Fin 146) => (witness q labels h i.val:ℚ_[p]))
  apply LocalIndexRegularity318.finite
  intro i
  exact actual p h₀ hb q labels hzero hone hg i.val

end DetectorLocalRegularity318
