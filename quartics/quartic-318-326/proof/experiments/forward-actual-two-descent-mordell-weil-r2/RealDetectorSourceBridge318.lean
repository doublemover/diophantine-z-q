module
public import RealPadeSourceBridge318
public section
noncomputable section
namespace RealDetectorSourceBridge318
open ActualCyclicClosure318 RealDetectorCoefficients318 RealPadeSourceBridge318
set_option maxHeartbeats 0
set_option maxRecDepth 100000
lemma value118_orbit (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) :
    value118 (raw q labels (pairOrbit h))=
      (DetectorGateWitness318.value118 (ActualPadeRatios318.witness q labels h):ℝ) := by
  simp only [value118,DetectorGateWitness318.value118]
  rw [raw_orbit q labels h ⟨0,by decide⟩]
  push_cast
  ring

lemma value119_orbit (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) :
    value119 (raw q labels (pairOrbit h))=
      (DetectorGateWitness318.value119 (ActualPadeRatios318.witness q labels h):ℝ) := by
  simp only [value119,DetectorGateWitness318.value119,value118_orbit]
  rw [raw_orbit q labels h ⟨106,by decide⟩]
  rw [raw_orbit q labels h ⟨107,by decide⟩]
  rw [raw_orbit q labels h ⟨114,by decide⟩]
  rw [raw_orbit q labels h ⟨115,by decide⟩]
  push_cast
  ring

lemma value120_orbit (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) :
    value120 (raw q labels (pairOrbit h))=
      (DetectorGateWitness318.value120 (ActualPadeRatios318.witness q labels h):ℝ) := by
  simp only [value120,DetectorGateWitness318.value120,value118_orbit,value119_orbit]
  rw [raw_orbit q labels h ⟨106,by decide⟩]
  rw [raw_orbit q labels h ⟨107,by decide⟩]
  rw [raw_orbit q labels h ⟨114,by decide⟩]
  rw [raw_orbit q labels h ⟨115,by decide⟩]
  push_cast
  ring

lemma value121_orbit (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) :
    value121 (raw q labels (pairOrbit h))=
      (DetectorGateWitness318.value121 (ActualPadeRatios318.witness q labels h):ℝ) := by
  simp only [value121,DetectorGateWitness318.value121,value118_orbit,value119_orbit,value120_orbit]
  rw [raw_orbit q labels h ⟨106,by decide⟩]
  rw [raw_orbit q labels h ⟨107,by decide⟩]
  rw [raw_orbit q labels h ⟨110,by decide⟩]
  rw [raw_orbit q labels h ⟨111,by decide⟩]
  push_cast
  ring

lemma value122_orbit (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) :
    value122 (raw q labels (pairOrbit h))=
      (DetectorGateWitness318.value122 (ActualPadeRatios318.witness q labels h):ℝ) := by
  simp only [value122,DetectorGateWitness318.value122,value118_orbit,value119_orbit,value120_orbit,value121_orbit]
  rw [raw_orbit q labels h ⟨106,by decide⟩]
  rw [raw_orbit q labels h ⟨107,by decide⟩]
  rw [raw_orbit q labels h ⟨110,by decide⟩]
  rw [raw_orbit q labels h ⟨111,by decide⟩]
  push_cast
  ring

lemma value123_orbit (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) :
    value123 (raw q labels (pairOrbit h))=
      (DetectorGateWitness318.value123 (ActualPadeRatios318.witness q labels h):ℝ) := by
  simp only [value123,DetectorGateWitness318.value123,value118_orbit,value119_orbit,value120_orbit,value121_orbit,value122_orbit]
  rw [raw_orbit q labels h ⟨110,by decide⟩]
  rw [raw_orbit q labels h ⟨111,by decide⟩]
  rw [raw_orbit q labels h ⟨114,by decide⟩]
  rw [raw_orbit q labels h ⟨115,by decide⟩]
  push_cast
  ring

lemma value124_orbit (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) :
    value124 (raw q labels (pairOrbit h))=
      (DetectorGateWitness318.value124 (ActualPadeRatios318.witness q labels h):ℝ) := by
  simp only [value124,DetectorGateWitness318.value124,value118_orbit,value119_orbit,value120_orbit,value121_orbit,value122_orbit,value123_orbit]
  rw [raw_orbit q labels h ⟨110,by decide⟩]
  rw [raw_orbit q labels h ⟨111,by decide⟩]
  rw [raw_orbit q labels h ⟨114,by decide⟩]
  rw [raw_orbit q labels h ⟨115,by decide⟩]
  push_cast
  ring

lemma value125_orbit (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) :
    value125 (raw q labels (pairOrbit h))=
      (DetectorGateWitness318.value125 (ActualPadeRatios318.witness q labels h):ℝ) := by
  simp only [value125,DetectorGateWitness318.value125,value118_orbit,value119_orbit,value120_orbit,value121_orbit,value122_orbit,value123_orbit,value124_orbit]
  rw [raw_orbit q labels h ⟨90,by decide⟩]
  rw [raw_orbit q labels h ⟨91,by decide⟩]
  push_cast
  ring

lemma value126_orbit (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) :
    value126 (raw q labels (pairOrbit h))=
      (DetectorGateWitness318.value126 (ActualPadeRatios318.witness q labels h):ℝ) := by
  simp only [value126,DetectorGateWitness318.value126,value118_orbit,value119_orbit,value120_orbit,value121_orbit,value122_orbit,value123_orbit,value124_orbit,value125_orbit]
  rw [raw_orbit q labels h ⟨37,by decide⟩]
  push_cast
  ring

lemma value127_orbit (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) :
    value127 (raw q labels (pairOrbit h))=
      (DetectorGateWitness318.value127 (ActualPadeRatios318.witness q labels h):ℝ) := by
  simp only [value127,DetectorGateWitness318.value127,value118_orbit,value119_orbit,value120_orbit,value121_orbit,value122_orbit,value123_orbit,value124_orbit,value125_orbit,value126_orbit]
  rw [raw_orbit q labels h ⟨102,by decide⟩]
  rw [raw_orbit q labels h ⟨103,by decide⟩]
  rw [raw_orbit q labels h ⟨104,by decide⟩]
  rw [raw_orbit q labels h ⟨105,by decide⟩]
  push_cast
  ring

lemma value128_orbit (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) :
    value128 (raw q labels (pairOrbit h))=
      (DetectorGateWitness318.value128 (ActualPadeRatios318.witness q labels h):ℝ) := by
  simp only [value128,DetectorGateWitness318.value128,value118_orbit,value119_orbit,value120_orbit,value121_orbit,value122_orbit,value123_orbit,value124_orbit,value125_orbit,value126_orbit,value127_orbit]
  rw [raw_orbit q labels h ⟨102,by decide⟩]
  rw [raw_orbit q labels h ⟨103,by decide⟩]
  rw [raw_orbit q labels h ⟨104,by decide⟩]
  rw [raw_orbit q labels h ⟨105,by decide⟩]
  push_cast
  ring

lemma value129_orbit (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) :
    value129 (raw q labels (pairOrbit h))=
      (DetectorGateWitness318.value129 (ActualPadeRatios318.witness q labels h):ℝ) := by
  simp only [value129,DetectorGateWitness318.value129,value118_orbit,value119_orbit,value120_orbit,value121_orbit,value122_orbit,value123_orbit,value124_orbit,value125_orbit,value126_orbit,value127_orbit,value128_orbit]
  rw [raw_orbit q labels h ⟨106,by decide⟩]
  rw [raw_orbit q labels h ⟨107,by decide⟩]
  rw [raw_orbit q labels h ⟨108,by decide⟩]
  rw [raw_orbit q labels h ⟨109,by decide⟩]
  push_cast
  ring

lemma value130_orbit (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) :
    value130 (raw q labels (pairOrbit h))=
      (DetectorGateWitness318.value130 (ActualPadeRatios318.witness q labels h):ℝ) := by
  simp only [value130,DetectorGateWitness318.value130,value118_orbit,value119_orbit,value120_orbit,value121_orbit,value122_orbit,value123_orbit,value124_orbit,value125_orbit,value126_orbit,value127_orbit,value128_orbit,value129_orbit]
  rw [raw_orbit q labels h ⟨106,by decide⟩]
  rw [raw_orbit q labels h ⟨107,by decide⟩]
  rw [raw_orbit q labels h ⟨108,by decide⟩]
  rw [raw_orbit q labels h ⟨109,by decide⟩]
  push_cast
  ring

lemma value131_orbit (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) :
    value131 (raw q labels (pairOrbit h))=
      (DetectorGateWitness318.value131 (ActualPadeRatios318.witness q labels h):ℝ) := by
  simp only [value131,DetectorGateWitness318.value131,value118_orbit,value119_orbit,value120_orbit,value121_orbit,value122_orbit,value123_orbit,value124_orbit,value125_orbit,value126_orbit,value127_orbit,value128_orbit,value129_orbit,value130_orbit]
  rw [raw_orbit q labels h ⟨110,by decide⟩]
  rw [raw_orbit q labels h ⟨111,by decide⟩]
  rw [raw_orbit q labels h ⟨112,by decide⟩]
  rw [raw_orbit q labels h ⟨113,by decide⟩]
  push_cast
  ring

lemma value132_orbit (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) :
    value132 (raw q labels (pairOrbit h))=
      (DetectorGateWitness318.value132 (ActualPadeRatios318.witness q labels h):ℝ) := by
  simp only [value132,DetectorGateWitness318.value132,value118_orbit,value119_orbit,value120_orbit,value121_orbit,value122_orbit,value123_orbit,value124_orbit,value125_orbit,value126_orbit,value127_orbit,value128_orbit,value129_orbit,value130_orbit,value131_orbit]
  rw [raw_orbit q labels h ⟨110,by decide⟩]
  rw [raw_orbit q labels h ⟨111,by decide⟩]
  rw [raw_orbit q labels h ⟨112,by decide⟩]
  rw [raw_orbit q labels h ⟨113,by decide⟩]
  push_cast
  ring

lemma value133_orbit (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) :
    value133 (raw q labels (pairOrbit h))=
      (DetectorGateWitness318.value133 (ActualPadeRatios318.witness q labels h):ℝ) := by
  simp only [value133,DetectorGateWitness318.value133,value118_orbit,value119_orbit,value120_orbit,value121_orbit,value122_orbit,value123_orbit,value124_orbit,value125_orbit,value126_orbit,value127_orbit,value128_orbit,value129_orbit,value130_orbit,value131_orbit,value132_orbit]
  rw [raw_orbit q labels h ⟨114,by decide⟩]
  rw [raw_orbit q labels h ⟨115,by decide⟩]
  rw [raw_orbit q labels h ⟨116,by decide⟩]
  rw [raw_orbit q labels h ⟨117,by decide⟩]
  push_cast
  ring

lemma value134_orbit (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) :
    value134 (raw q labels (pairOrbit h))=
      (DetectorGateWitness318.value134 (ActualPadeRatios318.witness q labels h):ℝ) := by
  simp only [value134,DetectorGateWitness318.value134,value118_orbit,value119_orbit,value120_orbit,value121_orbit,value122_orbit,value123_orbit,value124_orbit,value125_orbit,value126_orbit,value127_orbit,value128_orbit,value129_orbit,value130_orbit,value131_orbit,value132_orbit,value133_orbit]
  rw [raw_orbit q labels h ⟨114,by decide⟩]
  rw [raw_orbit q labels h ⟨115,by decide⟩]
  rw [raw_orbit q labels h ⟨116,by decide⟩]
  rw [raw_orbit q labels h ⟨117,by decide⟩]
  push_cast
  ring

lemma value135_orbit (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) :
    value135 (raw q labels (pairOrbit h))=
      (DetectorGateWitness318.value135 (ActualPadeRatios318.witness q labels h):ℝ) := by
  simp only [value135,DetectorGateWitness318.value135,value118_orbit,value119_orbit,value120_orbit,value121_orbit,value122_orbit,value123_orbit,value124_orbit,value125_orbit,value126_orbit,value127_orbit,value128_orbit,value129_orbit,value130_orbit,value131_orbit,value132_orbit,value133_orbit,value134_orbit]
  rw [raw_orbit q labels h ⟨0,by decide⟩]
  rw [raw_orbit q labels h ⟨102,by decide⟩]
  rw [raw_orbit q labels h ⟨103,by decide⟩]
  push_cast
  ring

lemma value136_orbit (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) :
    value136 (raw q labels (pairOrbit h))=
      (DetectorGateWitness318.value136 (ActualPadeRatios318.witness q labels h):ℝ) := by
  simp only [value136,DetectorGateWitness318.value136,value118_orbit,value119_orbit,value120_orbit,value121_orbit,value122_orbit,value123_orbit,value124_orbit,value125_orbit,value126_orbit,value127_orbit,value128_orbit,value129_orbit,value130_orbit,value131_orbit,value132_orbit,value133_orbit,value134_orbit,value135_orbit]
  rw [raw_orbit q labels h ⟨0,by decide⟩]
  rw [raw_orbit q labels h ⟨102,by decide⟩]
  rw [raw_orbit q labels h ⟨103,by decide⟩]
  push_cast
  ring

lemma value137_orbit (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) :
    value137 (raw q labels (pairOrbit h))=
      (DetectorGateWitness318.value137 (ActualPadeRatios318.witness q labels h):ℝ) := by
  simp only [value137,DetectorGateWitness318.value137,value118_orbit,value119_orbit,value120_orbit,value121_orbit,value122_orbit,value123_orbit,value124_orbit,value125_orbit,value126_orbit,value127_orbit,value128_orbit,value129_orbit,value130_orbit,value131_orbit,value132_orbit,value133_orbit,value134_orbit,value135_orbit,value136_orbit]
  push_cast
  ring

lemma value138_orbit (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) :
    value138 (raw q labels (pairOrbit h))=
      (DetectorGateWitness318.value138 (ActualPadeRatios318.witness q labels h):ℝ) := by
  simp only [value138,DetectorGateWitness318.value138,value118_orbit,value119_orbit,value120_orbit,value121_orbit,value122_orbit,value123_orbit,value124_orbit,value125_orbit,value126_orbit,value127_orbit,value128_orbit,value129_orbit,value130_orbit,value131_orbit,value132_orbit,value133_orbit,value134_orbit,value135_orbit,value136_orbit,value137_orbit]
  push_cast
  ring

lemma value139_orbit (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) :
    value139 (raw q labels (pairOrbit h))=
      (DetectorGateWitness318.value139 (ActualPadeRatios318.witness q labels h):ℝ) := by
  simp only [value139,DetectorGateWitness318.value139,value118_orbit,value119_orbit,value120_orbit,value121_orbit,value122_orbit,value123_orbit,value124_orbit,value125_orbit,value126_orbit,value127_orbit,value128_orbit,value129_orbit,value130_orbit,value131_orbit,value132_orbit,value133_orbit,value134_orbit,value135_orbit,value136_orbit,value137_orbit,value138_orbit]
  rw [raw_orbit q labels h ⟨79,by decide⟩]
  rw [raw_orbit q labels h ⟨80,by decide⟩]
  rw [raw_orbit q labels h ⟨82,by decide⟩]
  rw [raw_orbit q labels h ⟨83,by decide⟩]
  push_cast
  ring

lemma value140_orbit (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) :
    value140 (raw q labels (pairOrbit h))=
      (DetectorGateWitness318.value140 (ActualPadeRatios318.witness q labels h):ℝ) := by
  simp only [value140,DetectorGateWitness318.value140,value118_orbit,value119_orbit,value120_orbit,value121_orbit,value122_orbit,value123_orbit,value124_orbit,value125_orbit,value126_orbit,value127_orbit,value128_orbit,value129_orbit,value130_orbit,value131_orbit,value132_orbit,value133_orbit,value134_orbit,value135_orbit,value136_orbit,value137_orbit,value138_orbit,value139_orbit]
  rw [raw_orbit q labels h ⟨79,by decide⟩]
  rw [raw_orbit q labels h ⟨80,by decide⟩]
  rw [raw_orbit q labels h ⟨82,by decide⟩]
  rw [raw_orbit q labels h ⟨83,by decide⟩]
  push_cast
  ring

lemma value141_orbit (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) :
    value141 (raw q labels (pairOrbit h))=
      (DetectorGateWitness318.value141 (ActualPadeRatios318.witness q labels h):ℝ) := by
  simp only [value141,DetectorGateWitness318.value141,value118_orbit,value119_orbit,value120_orbit,value121_orbit,value122_orbit,value123_orbit,value124_orbit,value125_orbit,value126_orbit,value127_orbit,value128_orbit,value129_orbit,value130_orbit,value131_orbit,value132_orbit,value133_orbit,value134_orbit,value135_orbit,value136_orbit,value137_orbit,value138_orbit,value139_orbit,value140_orbit]
  rw [raw_orbit q labels h ⟨85,by decide⟩]
  rw [raw_orbit q labels h ⟨86,by decide⟩]
  push_cast
  ring

lemma value142_orbit (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) :
    value142 (raw q labels (pairOrbit h))=
      (DetectorGateWitness318.value142 (ActualPadeRatios318.witness q labels h):ℝ) := by
  simp only [value142,DetectorGateWitness318.value142,value118_orbit,value119_orbit,value120_orbit,value121_orbit,value122_orbit,value123_orbit,value124_orbit,value125_orbit,value126_orbit,value127_orbit,value128_orbit,value129_orbit,value130_orbit,value131_orbit,value132_orbit,value133_orbit,value134_orbit,value135_orbit,value136_orbit,value137_orbit,value138_orbit,value139_orbit,value140_orbit,value141_orbit]
  rw [raw_orbit q labels h ⟨85,by decide⟩]
  rw [raw_orbit q labels h ⟨86,by decide⟩]
  push_cast
  ring

lemma value143_orbit (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) :
    value143 (raw q labels (pairOrbit h))=
      (DetectorGateWitness318.value143 (ActualPadeRatios318.witness q labels h):ℝ) := by
  simp only [value143,DetectorGateWitness318.value143,value118_orbit,value119_orbit,value120_orbit,value121_orbit,value122_orbit,value123_orbit,value124_orbit,value125_orbit,value126_orbit,value127_orbit,value128_orbit,value129_orbit,value130_orbit,value131_orbit,value132_orbit,value133_orbit,value134_orbit,value135_orbit,value136_orbit,value137_orbit,value138_orbit,value139_orbit,value140_orbit,value141_orbit,value142_orbit]
  rw [raw_orbit q labels h ⟨88,by decide⟩]
  rw [raw_orbit q labels h ⟨89,by decide⟩]
  push_cast
  ring

lemma value144_orbit (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) :
    value144 (raw q labels (pairOrbit h))=
      (DetectorGateWitness318.value144 (ActualPadeRatios318.witness q labels h):ℝ) := by
  simp only [value144,DetectorGateWitness318.value144,value118_orbit,value119_orbit,value120_orbit,value121_orbit,value122_orbit,value123_orbit,value124_orbit,value125_orbit,value126_orbit,value127_orbit,value128_orbit,value129_orbit,value130_orbit,value131_orbit,value132_orbit,value133_orbit,value134_orbit,value135_orbit,value136_orbit,value137_orbit,value138_orbit,value139_orbit,value140_orbit,value141_orbit,value142_orbit,value143_orbit]
  rw [raw_orbit q labels h ⟨88,by decide⟩]
  rw [raw_orbit q labels h ⟨89,by decide⟩]
  push_cast
  ring

lemma value145_orbit (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) :
    value145 (raw q labels (pairOrbit h))=
      (DetectorGateWitness318.value145 (ActualPadeRatios318.witness q labels h):ℝ) := by
  simp only [value145,DetectorGateWitness318.value145,value118_orbit,value119_orbit,value120_orbit,value121_orbit,value122_orbit,value123_orbit,value124_orbit,value125_orbit,value126_orbit,value127_orbit,value128_orbit,value129_orbit,value130_orbit,value131_orbit,value132_orbit,value133_orbit,value134_orbit,value135_orbit,value136_orbit,value137_orbit,value138_orbit,value139_orbit,value140_orbit,value141_orbit,value142_orbit,value143_orbit,value144_orbit]
  push_cast
  ring

/-- The compactness candidate is the full exact146-coordinate projection
of the actual coherent source assignment, not a surrogate polynomial bound. -/
theorem coefficients_orbit (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) :
    coefficients q labels (pairOrbit h)=
      ContactChainReal318.project (DetectorGateWitness318.witness q labels h) := by
  funext i
  by_cases hi : i.val<118
  · have he : ∀ j ∈ (List.range 28).map (·+118), i.val≠j := by
      intro j hj
      simp only [List.mem_map,List.mem_range] at hj
      obtain ⟨k,hk,rfl⟩ := hj
      omega
    simp only [coefficients,ContactChainReal318.project,DetectorGateWitness318.witness]
    simp [RealDetectorCoefficients318.fill,DetectorGateWitness318.fill,
      show i.val≠118 by omega,show i.val≠119 by omega,show i.val≠120 by omega,
      show i.val≠121 by omega,      show i.val≠122 by omega,      show i.val≠123 by omega,      show i.val≠124 by omega,      show i.val≠125 by omega,      show i.val≠126 by omega,      show i.val≠127 by omega,      show i.val≠128 by omega,      show i.val≠129 by omega,      show i.val≠130 by omega,      show i.val≠131 by omega,      show i.val≠132 by omega,      show i.val≠133 by omega,      show i.val≠134 by omega,      show i.val≠135 by omega,      show i.val≠136 by omega,      show i.val≠137 by omega,      show i.val≠138 by omega,      show i.val≠139 by omega,      show i.val≠140 by omega,      show i.val≠141 by omega,      show i.val≠142 by omega,      show i.val≠143 by omega,      show i.val≠144 by omega,      show i.val≠145 by omega]
    exact raw_orbit q labels h ⟨i.val,hi⟩
  · have hi' : (118 : ℕ) ≤ i.val := by omega
    have hil : i.val<146 := i.isLt
    interval_cases hv : i.val <;>
      simp [coefficients,ContactChainReal318.project,DetectorGateWitness318.witness,
        RealDetectorCoefficients318.fill,DetectorGateWitness318.fill,hv,
value118_orbit,value119_orbit,value120_orbit,value121_orbit,value122_orbit,value123_orbit,value124_orbit,value125_orbit,value126_orbit,value127_orbit,value128_orbit,value129_orbit,value130_orbit,value131_orbit,value132_orbit,value133_orbit,value134_orbit,value135_orbit,value136_orbit,value137_orbit,value138_orbit,value139_orbit,value140_orbit,value141_orbit,value142_orbit,value143_orbit,value144_orbit,value145_orbit]

end RealDetectorSourceBridge318
