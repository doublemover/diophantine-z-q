module
public import UniformScaledPoleDomain318
public section
noncomputable section
namespace ChainInputInvariance318
open CircuitReplay ScaledDetectorChain318
set_option maxHeartbeats 0
set_option maxRecDepth 100000
lemma value159_first (w : Assignment) (t₀ c t : ℚ) :
      ContactChainWitness318.value159 (view (PoleInputWitness318.fill w t₀) c t)=
        ContactChainWitness318.value159 (view w c t) := by
  simp only [ContactChainWitness318.value159]
  simp [view,ContactChainLimits318.view,PoleInputWitness318.fill,ContactChainWitness318.fill,ContactWeightWitness318.fill]

lemma value160_first (w : Assignment) (t₀ c t : ℚ) :
      ContactChainWitness318.value160 (view (PoleInputWitness318.fill w t₀) c t)=
        ContactChainWitness318.value160 (view w c t) := by
  simp only [ContactChainWitness318.value160,value159_first]
  simp [view,ContactChainLimits318.view,PoleInputWitness318.fill,ContactChainWitness318.fill,ContactWeightWitness318.fill]

lemma value161_first (w : Assignment) (t₀ c t : ℚ) :
      ContactChainWitness318.value161 (view (PoleInputWitness318.fill w t₀) c t)=
        ContactChainWitness318.value161 (view w c t) := by
  simp only [ContactChainWitness318.value161,value159_first,value160_first]
  simp [view,ContactChainLimits318.view,PoleInputWitness318.fill,ContactChainWitness318.fill,ContactWeightWitness318.fill]

lemma value162_first (w : Assignment) (t₀ c t : ℚ) :
      ContactChainWitness318.value162 (view (PoleInputWitness318.fill w t₀) c t)=
        ContactChainWitness318.value162 (view w c t) := by
  simp only [ContactChainWitness318.value162,value159_first,value160_first,value161_first]
  simp [view,ContactChainLimits318.view,PoleInputWitness318.fill,ContactChainWitness318.fill,ContactWeightWitness318.fill]

lemma value163_first (w : Assignment) (t₀ c t : ℚ) :
      ContactChainWitness318.value163 (view (PoleInputWitness318.fill w t₀) c t)=
        ContactChainWitness318.value163 (view w c t) := by
  simp only [ContactChainWitness318.value163,value159_first,value160_first,value161_first,value162_first]
  simp [view,ContactChainLimits318.view,PoleInputWitness318.fill,ContactChainWitness318.fill,ContactWeightWitness318.fill]

lemma value164_first (w : Assignment) (t₀ c t : ℚ) :
      ContactChainWitness318.value164 (view (PoleInputWitness318.fill w t₀) c t)=
        ContactChainWitness318.value164 (view w c t) := by
  simp only [ContactChainWitness318.value164,value159_first,value160_first,value161_first,value162_first,value163_first]
  simp [view,ContactChainLimits318.view,PoleInputWitness318.fill,ContactChainWitness318.fill,ContactWeightWitness318.fill]

lemma value165_first (w : Assignment) (t₀ c t : ℚ) :
      ContactChainWitness318.value165 (view (PoleInputWitness318.fill w t₀) c t)=
        ContactChainWitness318.value165 (view w c t) := by
  simp only [ContactChainWitness318.value165,value159_first,value160_first,value161_first,value162_first,value163_first,value164_first]
  simp [view,ContactChainLimits318.view,PoleInputWitness318.fill,ContactChainWitness318.fill,ContactWeightWitness318.fill]

lemma value166_first (w : Assignment) (t₀ c t : ℚ) :
      ContactChainWitness318.value166 (view (PoleInputWitness318.fill w t₀) c t)=
        ContactChainWitness318.value166 (view w c t) := by
  simp only [ContactChainWitness318.value166,value159_first,value160_first,value161_first,value162_first,value163_first,value164_first,value165_first]
  simp [view,ContactChainLimits318.view,PoleInputWitness318.fill,ContactChainWitness318.fill,ContactWeightWitness318.fill]

lemma value167_first (w : Assignment) (t₀ c t : ℚ) :
      ContactChainWitness318.value167 (view (PoleInputWitness318.fill w t₀) c t)=
        ContactChainWitness318.value167 (view w c t) := by
  simp only [ContactChainWitness318.value167,value159_first,value160_first,value161_first,value162_first,value163_first,value164_first,value165_first,value166_first]
  simp [view,ContactChainLimits318.view,PoleInputWitness318.fill,ContactChainWitness318.fill,ContactWeightWitness318.fill]

lemma value168_first (w : Assignment) (t₀ c t : ℚ) :
      ContactChainWitness318.value168 (view (PoleInputWitness318.fill w t₀) c t)=
        ContactChainWitness318.value168 (view w c t) := by
  simp only [ContactChainWitness318.value168,value159_first,value160_first,value161_first,value162_first,value163_first,value164_first,value165_first,value166_first,value167_first]
  simp [view,ContactChainLimits318.view,PoleInputWitness318.fill,ContactChainWitness318.fill,ContactWeightWitness318.fill]

lemma value169_first (w : Assignment) (t₀ c t : ℚ) :
      ContactChainWitness318.value169 (view (PoleInputWitness318.fill w t₀) c t)=
        ContactChainWitness318.value169 (view w c t) := by
  simp only [ContactChainWitness318.value169,value159_first,value160_first,value161_first,value162_first,value163_first,value164_first,value165_first,value166_first,value167_first,value168_first]
  simp [view,ContactChainLimits318.view,PoleInputWitness318.fill,ContactChainWitness318.fill,ContactWeightWitness318.fill]

lemma value170_first (w : Assignment) (t₀ c t : ℚ) :
      ContactChainWitness318.value170 (view (PoleInputWitness318.fill w t₀) c t)=
        ContactChainWitness318.value170 (view w c t) := by
  simp only [ContactChainWitness318.value170,value159_first,value160_first,value161_first,value162_first,value163_first,value164_first,value165_first,value166_first,value167_first,value168_first,value169_first]
  simp [view,ContactChainLimits318.view,PoleInputWitness318.fill,ContactChainWitness318.fill,ContactWeightWitness318.fill]

lemma value171_first (w : Assignment) (t₀ c t : ℚ) :
      ContactChainWitness318.value171 (view (PoleInputWitness318.fill w t₀) c t)=
        ContactChainWitness318.value171 (view w c t) := by
  simp only [ContactChainWitness318.value171,value159_first,value160_first,value161_first,value162_first,value163_first,value164_first,value165_first,value166_first,value167_first,value168_first,value169_first,value170_first]
  simp [view,ContactChainLimits318.view,PoleInputWitness318.fill,ContactChainWitness318.fill,ContactWeightWitness318.fill]

lemma value172_first (w : Assignment) (t₀ c t : ℚ) :
      ContactChainWitness318.value172 (view (PoleInputWitness318.fill w t₀) c t)=
        ContactChainWitness318.value172 (view w c t) := by
  simp only [ContactChainWitness318.value172,value159_first,value160_first,value161_first,value162_first,value163_first,value164_first,value165_first,value166_first,value167_first,value168_first,value169_first,value170_first,value171_first]
  simp [view,ContactChainLimits318.view,PoleInputWitness318.fill,ContactChainWitness318.fill,ContactWeightWitness318.fill]

lemma value173_first (w : Assignment) (t₀ c t : ℚ) :
      ContactChainWitness318.value173 (view (PoleInputWitness318.fill w t₀) c t)=
        ContactChainWitness318.value173 (view w c t) := by
  simp only [ContactChainWitness318.value173,value159_first,value160_first,value161_first,value162_first,value163_first,value164_first,value165_first,value166_first,value167_first,value168_first,value169_first,value170_first,value171_first,value172_first]
  simp [view,ContactChainLimits318.view,PoleInputWitness318.fill,ContactChainWitness318.fill,ContactWeightWitness318.fill]

lemma value174_first (w : Assignment) (t₀ c t : ℚ) :
      ContactChainWitness318.value174 (view (PoleInputWitness318.fill w t₀) c t)=
        ContactChainWitness318.value174 (view w c t) := by
  simp only [ContactChainWitness318.value174,value159_first,value160_first,value161_first,value162_first,value163_first,value164_first,value165_first,value166_first,value167_first,value168_first,value169_first,value170_first,value171_first,value172_first,value173_first]
  simp [view,ContactChainLimits318.view,PoleInputWitness318.fill,ContactChainWitness318.fill,ContactWeightWitness318.fill]

lemma value175_first (w : Assignment) (t₀ c t : ℚ) :
      ContactChainWitness318.value175 (view (PoleInputWitness318.fill w t₀) c t)=
        ContactChainWitness318.value175 (view w c t) := by
  simp only [ContactChainWitness318.value175,value159_first,value160_first,value161_first,value162_first,value163_first,value164_first,value165_first,value166_first,value167_first,value168_first,value169_first,value170_first,value171_first,value172_first,value173_first,value174_first]
  simp [view,ContactChainLimits318.view,PoleInputWitness318.fill,ContactChainWitness318.fill,ContactWeightWitness318.fill]

lemma value176_first (w : Assignment) (t₀ c t : ℚ) :
      ContactChainWitness318.value176 (view (PoleInputWitness318.fill w t₀) c t)=
        ContactChainWitness318.value176 (view w c t) := by
  simp only [ContactChainWitness318.value176,value159_first,value160_first,value161_first,value162_first,value163_first,value164_first,value165_first,value166_first,value167_first,value168_first,value169_first,value170_first,value171_first,value172_first,value173_first,value174_first,value175_first]
  simp [view,ContactChainLimits318.view,PoleInputWitness318.fill,ContactChainWitness318.fill,ContactWeightWitness318.fill]

lemma value177_first (w : Assignment) (t₀ c t : ℚ) :
      ContactChainWitness318.value177 (view (PoleInputWitness318.fill w t₀) c t)=
        ContactChainWitness318.value177 (view w c t) := by
  simp only [ContactChainWitness318.value177,value159_first,value160_first,value161_first,value162_first,value163_first,value164_first,value165_first,value166_first,value167_first,value168_first,value169_first,value170_first,value171_first,value172_first,value173_first,value174_first,value175_first,value176_first]
  simp [view,ContactChainLimits318.view,PoleInputWitness318.fill,ContactChainWitness318.fill,ContactWeightWitness318.fill]

lemma value178_first (w : Assignment) (t₀ c t : ℚ) :
      ContactChainWitness318.value178 (view (PoleInputWitness318.fill w t₀) c t)=
        ContactChainWitness318.value178 (view w c t) := by
  simp only [ContactChainWitness318.value178,value159_first,value160_first,value161_first,value162_first,value163_first,value164_first,value165_first,value166_first,value167_first,value168_first,value169_first,value170_first,value171_first,value172_first,value173_first,value174_first,value175_first,value176_first,value177_first]
  simp [view,ContactChainLimits318.view,PoleInputWitness318.fill,ContactChainWitness318.fill,ContactWeightWitness318.fill]

lemma value179_first (w : Assignment) (t₀ c t : ℚ) :
      ContactChainWitness318.value179 (view (PoleInputWitness318.fill w t₀) c t)=
        ContactChainWitness318.value179 (view w c t) := by
  simp only [ContactChainWitness318.value179,value159_first,value160_first,value161_first,value162_first,value163_first,value164_first,value165_first,value166_first,value167_first,value168_first,value169_first,value170_first,value171_first,value172_first,value173_first,value174_first,value175_first,value176_first,value177_first,value178_first]
  simp [view,ContactChainLimits318.view,PoleInputWitness318.fill,ContactChainWitness318.fill,ContactWeightWitness318.fill]

lemma value180_first (w : Assignment) (t₀ c t : ℚ) :
      ContactChainWitness318.value180 (view (PoleInputWitness318.fill w t₀) c t)=
        ContactChainWitness318.value180 (view w c t) := by
  simp only [ContactChainWitness318.value180,value159_first,value160_first,value161_first,value162_first,value163_first,value164_first,value165_first,value166_first,value167_first,value168_first,value169_first,value170_first,value171_first,value172_first,value173_first,value174_first,value175_first,value176_first,value177_first,value178_first,value179_first]
  simp [view,ContactChainLimits318.view,PoleInputWitness318.fill,ContactChainWitness318.fill,ContactWeightWitness318.fill]

lemma value181_first (w : Assignment) (t₀ c t : ℚ) :
      ContactChainWitness318.value181 (view (PoleInputWitness318.fill w t₀) c t)=
        ContactChainWitness318.value181 (view w c t) := by
  simp only [ContactChainWitness318.value181,value159_first,value160_first,value161_first,value162_first,value163_first,value164_first,value165_first,value166_first,value167_first,value168_first,value169_first,value170_first,value171_first,value172_first,value173_first,value174_first,value175_first,value176_first,value177_first,value178_first,value179_first,value180_first]
  simp [view,ContactChainLimits318.view,PoleInputWitness318.fill,ContactChainWitness318.fill,ContactWeightWitness318.fill]

lemma value182_first (w : Assignment) (t₀ c t : ℚ) :
      ContactChainWitness318.value182 (view (PoleInputWitness318.fill w t₀) c t)=
        ContactChainWitness318.value182 (view w c t) := by
  simp only [ContactChainWitness318.value182,value159_first,value160_first,value161_first,value162_first,value163_first,value164_first,value165_first,value166_first,value167_first,value168_first,value169_first,value170_first,value171_first,value172_first,value173_first,value174_first,value175_first,value176_first,value177_first,value178_first,value179_first,value180_first,value181_first]
  simp [view,ContactChainLimits318.view,PoleInputWitness318.fill,ContactChainWitness318.fill,ContactWeightWitness318.fill]

lemma value183_first (w : Assignment) (t₀ c t : ℚ) :
      ContactChainWitness318.value183 (view (PoleInputWitness318.fill w t₀) c t)=
        ContactChainWitness318.value183 (view w c t) := by
  simp only [ContactChainWitness318.value183,value159_first,value160_first,value161_first,value162_first,value163_first,value164_first,value165_first,value166_first,value167_first,value168_first,value169_first,value170_first,value171_first,value172_first,value173_first,value174_first,value175_first,value176_first,value177_first,value178_first,value179_first,value180_first,value181_first,value182_first]
  simp [view,ContactChainLimits318.view,PoleInputWitness318.fill,ContactChainWitness318.fill,ContactWeightWitness318.fill]

lemma value184_first (w : Assignment) (t₀ c t : ℚ) :
      ContactChainWitness318.value184 (view (PoleInputWitness318.fill w t₀) c t)=
        ContactChainWitness318.value184 (view w c t) := by
  simp only [ContactChainWitness318.value184,value159_first,value160_first,value161_first,value162_first,value163_first,value164_first,value165_first,value166_first,value167_first,value168_first,value169_first,value170_first,value171_first,value172_first,value173_first,value174_first,value175_first,value176_first,value177_first,value178_first,value179_first,value180_first,value181_first,value182_first,value183_first]
  simp [view,ContactChainLimits318.view,PoleInputWitness318.fill,ContactChainWitness318.fill,ContactWeightWitness318.fill]

lemma value185_first (w : Assignment) (t₀ c t : ℚ) :
      ContactChainWitness318.value185 (view (PoleInputWitness318.fill w t₀) c t)=
        ContactChainWitness318.value185 (view w c t) := by
  simp only [ContactChainWitness318.value185,value159_first,value160_first,value161_first,value162_first,value163_first,value164_first,value165_first,value166_first,value167_first,value168_first,value169_first,value170_first,value171_first,value172_first,value173_first,value174_first,value175_first,value176_first,value177_first,value178_first,value179_first,value180_first,value181_first,value182_first,value183_first,value184_first]
  simp [view,ContactChainLimits318.view,PoleInputWitness318.fill,ContactChainWitness318.fill,ContactWeightWitness318.fill]

lemma value186_first (w : Assignment) (t₀ c t : ℚ) :
      ContactChainWitness318.value186 (view (PoleInputWitness318.fill w t₀) c t)=
        ContactChainWitness318.value186 (view w c t) := by
  simp only [ContactChainWitness318.value186,value159_first,value160_first,value161_first,value162_first,value163_first,value164_first,value165_first,value166_first,value167_first,value168_first,value169_first,value170_first,value171_first,value172_first,value173_first,value174_first,value175_first,value176_first,value177_first,value178_first,value179_first,value180_first,value181_first,value182_first,value183_first,value184_first,value185_first]
  simp [view,ContactChainLimits318.view,PoleInputWitness318.fill,ContactChainWitness318.fill,ContactWeightWitness318.fill]

lemma value187_first (w : Assignment) (t₀ c t : ℚ) :
      ContactChainWitness318.value187 (view (PoleInputWitness318.fill w t₀) c t)=
        ContactChainWitness318.value187 (view w c t) := by
  simp only [ContactChainWitness318.value187,value159_first,value160_first,value161_first,value162_first,value163_first,value164_first,value165_first,value166_first,value167_first,value168_first,value169_first,value170_first,value171_first,value172_first,value173_first,value174_first,value175_first,value176_first,value177_first,value178_first,value179_first,value180_first,value181_first,value182_first,value183_first,value184_first,value185_first,value186_first]
  simp [view,ContactChainLimits318.view,PoleInputWitness318.fill,ContactChainWitness318.fill,ContactWeightWitness318.fill]

lemma value188_first (w : Assignment) (t₀ c t : ℚ) :
      ContactChainWitness318.value188 (view (PoleInputWitness318.fill w t₀) c t)=
        ContactChainWitness318.value188 (view w c t) := by
  simp only [ContactChainWitness318.value188,value159_first,value160_first,value161_first,value162_first,value163_first,value164_first,value165_first,value166_first,value167_first,value168_first,value169_first,value170_first,value171_first,value172_first,value173_first,value174_first,value175_first,value176_first,value177_first,value178_first,value179_first,value180_first,value181_first,value182_first,value183_first,value184_first,value185_first,value186_first,value187_first]
  simp [view,ContactChainLimits318.view,PoleInputWitness318.fill,ContactChainWitness318.fill,ContactWeightWitness318.fill]

lemma realChain_first (w : Assignment) (t₀ c t : ℚ) :
      realChain (PoleInputWitness318.fill w t₀) c t=realChain w c t :=
    value187_first w t₀ c t

lemma imagChain_first (w : Assignment) (t₀ c t : ℚ) :
      imagChain (PoleInputWitness318.fill w t₀) c t=imagChain w c t :=
    value188_first w t₀ c t

lemma traceQuotient_first (w : Assignment) (t₀ c t : ℚ) :
      traceQuotient (PoleInputWitness318.fill w t₀) c t=traceQuotient w c t := by
  simp only [traceQuotient,realChain_first,imagChain_first]

lemma poleInput_first (w : Assignment) (t₀ c t : ℚ) :
      poleInput (PoleInputWitness318.fill w t₀) c t=poleInput w c t := by
  simp only [poleInput,traceQuotient_first,realChain_first,imagChain_first]

lemma squareFactor_first (w : Assignment) (t₀ c t : ℚ) :
      squareFactor (PoleInputWitness318.fill w t₀) c t=squareFactor w c t := by
  simp only [squareFactor,traceQuotient_first,realChain_first,imagChain_first]

lemma value159_second (w : Assignment) (c₀ t₀ c t : ℚ) :
      ContactChainWitness318.value159 (view (ScaledDetectorChain318.fill 0 w c₀ t₀) c t)=
        ContactChainWitness318.value159 (view w c t) := by
  simp only [ContactChainWitness318.value159]
  simp [view,ContactChainLimits318.view,ScaledDetectorChain318.fill,ScaledContactWeights318.fill]

lemma value160_second (w : Assignment) (c₀ t₀ c t : ℚ) :
      ContactChainWitness318.value160 (view (ScaledDetectorChain318.fill 0 w c₀ t₀) c t)=
        ContactChainWitness318.value160 (view w c t) := by
  simp only [ContactChainWitness318.value160,value159_second]
  simp [view,ContactChainLimits318.view,ScaledDetectorChain318.fill,ScaledContactWeights318.fill]

lemma value161_second (w : Assignment) (c₀ t₀ c t : ℚ) :
      ContactChainWitness318.value161 (view (ScaledDetectorChain318.fill 0 w c₀ t₀) c t)=
        ContactChainWitness318.value161 (view w c t) := by
  simp only [ContactChainWitness318.value161,value159_second,value160_second]
  simp [view,ContactChainLimits318.view,ScaledDetectorChain318.fill,ScaledContactWeights318.fill]

lemma value162_second (w : Assignment) (c₀ t₀ c t : ℚ) :
      ContactChainWitness318.value162 (view (ScaledDetectorChain318.fill 0 w c₀ t₀) c t)=
        ContactChainWitness318.value162 (view w c t) := by
  simp only [ContactChainWitness318.value162,value159_second,value160_second,value161_second]
  simp [view,ContactChainLimits318.view,ScaledDetectorChain318.fill,ScaledContactWeights318.fill]

lemma value163_second (w : Assignment) (c₀ t₀ c t : ℚ) :
      ContactChainWitness318.value163 (view (ScaledDetectorChain318.fill 0 w c₀ t₀) c t)=
        ContactChainWitness318.value163 (view w c t) := by
  simp only [ContactChainWitness318.value163,value159_second,value160_second,value161_second,value162_second]
  simp [view,ContactChainLimits318.view,ScaledDetectorChain318.fill,ScaledContactWeights318.fill]

lemma value164_second (w : Assignment) (c₀ t₀ c t : ℚ) :
      ContactChainWitness318.value164 (view (ScaledDetectorChain318.fill 0 w c₀ t₀) c t)=
        ContactChainWitness318.value164 (view w c t) := by
  simp only [ContactChainWitness318.value164,value159_second,value160_second,value161_second,value162_second,value163_second]
  simp [view,ContactChainLimits318.view,ScaledDetectorChain318.fill,ScaledContactWeights318.fill]

lemma value165_second (w : Assignment) (c₀ t₀ c t : ℚ) :
      ContactChainWitness318.value165 (view (ScaledDetectorChain318.fill 0 w c₀ t₀) c t)=
        ContactChainWitness318.value165 (view w c t) := by
  simp only [ContactChainWitness318.value165,value159_second,value160_second,value161_second,value162_second,value163_second,value164_second]
  simp [view,ContactChainLimits318.view,ScaledDetectorChain318.fill,ScaledContactWeights318.fill]

lemma value166_second (w : Assignment) (c₀ t₀ c t : ℚ) :
      ContactChainWitness318.value166 (view (ScaledDetectorChain318.fill 0 w c₀ t₀) c t)=
        ContactChainWitness318.value166 (view w c t) := by
  simp only [ContactChainWitness318.value166,value159_second,value160_second,value161_second,value162_second,value163_second,value164_second,value165_second]
  simp [view,ContactChainLimits318.view,ScaledDetectorChain318.fill,ScaledContactWeights318.fill]

lemma value167_second (w : Assignment) (c₀ t₀ c t : ℚ) :
      ContactChainWitness318.value167 (view (ScaledDetectorChain318.fill 0 w c₀ t₀) c t)=
        ContactChainWitness318.value167 (view w c t) := by
  simp only [ContactChainWitness318.value167,value159_second,value160_second,value161_second,value162_second,value163_second,value164_second,value165_second,value166_second]
  simp [view,ContactChainLimits318.view,ScaledDetectorChain318.fill,ScaledContactWeights318.fill]

lemma value168_second (w : Assignment) (c₀ t₀ c t : ℚ) :
      ContactChainWitness318.value168 (view (ScaledDetectorChain318.fill 0 w c₀ t₀) c t)=
        ContactChainWitness318.value168 (view w c t) := by
  simp only [ContactChainWitness318.value168,value159_second,value160_second,value161_second,value162_second,value163_second,value164_second,value165_second,value166_second,value167_second]
  simp [view,ContactChainLimits318.view,ScaledDetectorChain318.fill,ScaledContactWeights318.fill]

lemma value169_second (w : Assignment) (c₀ t₀ c t : ℚ) :
      ContactChainWitness318.value169 (view (ScaledDetectorChain318.fill 0 w c₀ t₀) c t)=
        ContactChainWitness318.value169 (view w c t) := by
  simp only [ContactChainWitness318.value169,value159_second,value160_second,value161_second,value162_second,value163_second,value164_second,value165_second,value166_second,value167_second,value168_second]
  simp [view,ContactChainLimits318.view,ScaledDetectorChain318.fill,ScaledContactWeights318.fill]

lemma value170_second (w : Assignment) (c₀ t₀ c t : ℚ) :
      ContactChainWitness318.value170 (view (ScaledDetectorChain318.fill 0 w c₀ t₀) c t)=
        ContactChainWitness318.value170 (view w c t) := by
  simp only [ContactChainWitness318.value170,value159_second,value160_second,value161_second,value162_second,value163_second,value164_second,value165_second,value166_second,value167_second,value168_second,value169_second]
  simp [view,ContactChainLimits318.view,ScaledDetectorChain318.fill,ScaledContactWeights318.fill]

lemma value171_second (w : Assignment) (c₀ t₀ c t : ℚ) :
      ContactChainWitness318.value171 (view (ScaledDetectorChain318.fill 0 w c₀ t₀) c t)=
        ContactChainWitness318.value171 (view w c t) := by
  simp only [ContactChainWitness318.value171,value159_second,value160_second,value161_second,value162_second,value163_second,value164_second,value165_second,value166_second,value167_second,value168_second,value169_second,value170_second]
  simp [view,ContactChainLimits318.view,ScaledDetectorChain318.fill,ScaledContactWeights318.fill]

lemma value172_second (w : Assignment) (c₀ t₀ c t : ℚ) :
      ContactChainWitness318.value172 (view (ScaledDetectorChain318.fill 0 w c₀ t₀) c t)=
        ContactChainWitness318.value172 (view w c t) := by
  simp only [ContactChainWitness318.value172,value159_second,value160_second,value161_second,value162_second,value163_second,value164_second,value165_second,value166_second,value167_second,value168_second,value169_second,value170_second,value171_second]
  simp [view,ContactChainLimits318.view,ScaledDetectorChain318.fill,ScaledContactWeights318.fill]

lemma value173_second (w : Assignment) (c₀ t₀ c t : ℚ) :
      ContactChainWitness318.value173 (view (ScaledDetectorChain318.fill 0 w c₀ t₀) c t)=
        ContactChainWitness318.value173 (view w c t) := by
  simp only [ContactChainWitness318.value173,value159_second,value160_second,value161_second,value162_second,value163_second,value164_second,value165_second,value166_second,value167_second,value168_second,value169_second,value170_second,value171_second,value172_second]
  simp [view,ContactChainLimits318.view,ScaledDetectorChain318.fill,ScaledContactWeights318.fill]

lemma value174_second (w : Assignment) (c₀ t₀ c t : ℚ) :
      ContactChainWitness318.value174 (view (ScaledDetectorChain318.fill 0 w c₀ t₀) c t)=
        ContactChainWitness318.value174 (view w c t) := by
  simp only [ContactChainWitness318.value174,value159_second,value160_second,value161_second,value162_second,value163_second,value164_second,value165_second,value166_second,value167_second,value168_second,value169_second,value170_second,value171_second,value172_second,value173_second]
  simp [view,ContactChainLimits318.view,ScaledDetectorChain318.fill,ScaledContactWeights318.fill]

lemma value175_second (w : Assignment) (c₀ t₀ c t : ℚ) :
      ContactChainWitness318.value175 (view (ScaledDetectorChain318.fill 0 w c₀ t₀) c t)=
        ContactChainWitness318.value175 (view w c t) := by
  simp only [ContactChainWitness318.value175,value159_second,value160_second,value161_second,value162_second,value163_second,value164_second,value165_second,value166_second,value167_second,value168_second,value169_second,value170_second,value171_second,value172_second,value173_second,value174_second]
  simp [view,ContactChainLimits318.view,ScaledDetectorChain318.fill,ScaledContactWeights318.fill]

lemma value176_second (w : Assignment) (c₀ t₀ c t : ℚ) :
      ContactChainWitness318.value176 (view (ScaledDetectorChain318.fill 0 w c₀ t₀) c t)=
        ContactChainWitness318.value176 (view w c t) := by
  simp only [ContactChainWitness318.value176,value159_second,value160_second,value161_second,value162_second,value163_second,value164_second,value165_second,value166_second,value167_second,value168_second,value169_second,value170_second,value171_second,value172_second,value173_second,value174_second,value175_second]
  simp [view,ContactChainLimits318.view,ScaledDetectorChain318.fill,ScaledContactWeights318.fill]

lemma value177_second (w : Assignment) (c₀ t₀ c t : ℚ) :
      ContactChainWitness318.value177 (view (ScaledDetectorChain318.fill 0 w c₀ t₀) c t)=
        ContactChainWitness318.value177 (view w c t) := by
  simp only [ContactChainWitness318.value177,value159_second,value160_second,value161_second,value162_second,value163_second,value164_second,value165_second,value166_second,value167_second,value168_second,value169_second,value170_second,value171_second,value172_second,value173_second,value174_second,value175_second,value176_second]
  simp [view,ContactChainLimits318.view,ScaledDetectorChain318.fill,ScaledContactWeights318.fill]

lemma value178_second (w : Assignment) (c₀ t₀ c t : ℚ) :
      ContactChainWitness318.value178 (view (ScaledDetectorChain318.fill 0 w c₀ t₀) c t)=
        ContactChainWitness318.value178 (view w c t) := by
  simp only [ContactChainWitness318.value178,value159_second,value160_second,value161_second,value162_second,value163_second,value164_second,value165_second,value166_second,value167_second,value168_second,value169_second,value170_second,value171_second,value172_second,value173_second,value174_second,value175_second,value176_second,value177_second]
  simp [view,ContactChainLimits318.view,ScaledDetectorChain318.fill,ScaledContactWeights318.fill]

lemma value179_second (w : Assignment) (c₀ t₀ c t : ℚ) :
      ContactChainWitness318.value179 (view (ScaledDetectorChain318.fill 0 w c₀ t₀) c t)=
        ContactChainWitness318.value179 (view w c t) := by
  simp only [ContactChainWitness318.value179,value159_second,value160_second,value161_second,value162_second,value163_second,value164_second,value165_second,value166_second,value167_second,value168_second,value169_second,value170_second,value171_second,value172_second,value173_second,value174_second,value175_second,value176_second,value177_second,value178_second]
  simp [view,ContactChainLimits318.view,ScaledDetectorChain318.fill,ScaledContactWeights318.fill]

lemma value180_second (w : Assignment) (c₀ t₀ c t : ℚ) :
      ContactChainWitness318.value180 (view (ScaledDetectorChain318.fill 0 w c₀ t₀) c t)=
        ContactChainWitness318.value180 (view w c t) := by
  simp only [ContactChainWitness318.value180,value159_second,value160_second,value161_second,value162_second,value163_second,value164_second,value165_second,value166_second,value167_second,value168_second,value169_second,value170_second,value171_second,value172_second,value173_second,value174_second,value175_second,value176_second,value177_second,value178_second,value179_second]
  simp [view,ContactChainLimits318.view,ScaledDetectorChain318.fill,ScaledContactWeights318.fill]

lemma value181_second (w : Assignment) (c₀ t₀ c t : ℚ) :
      ContactChainWitness318.value181 (view (ScaledDetectorChain318.fill 0 w c₀ t₀) c t)=
        ContactChainWitness318.value181 (view w c t) := by
  simp only [ContactChainWitness318.value181,value159_second,value160_second,value161_second,value162_second,value163_second,value164_second,value165_second,value166_second,value167_second,value168_second,value169_second,value170_second,value171_second,value172_second,value173_second,value174_second,value175_second,value176_second,value177_second,value178_second,value179_second,value180_second]
  simp [view,ContactChainLimits318.view,ScaledDetectorChain318.fill,ScaledContactWeights318.fill]

lemma value182_second (w : Assignment) (c₀ t₀ c t : ℚ) :
      ContactChainWitness318.value182 (view (ScaledDetectorChain318.fill 0 w c₀ t₀) c t)=
        ContactChainWitness318.value182 (view w c t) := by
  simp only [ContactChainWitness318.value182,value159_second,value160_second,value161_second,value162_second,value163_second,value164_second,value165_second,value166_second,value167_second,value168_second,value169_second,value170_second,value171_second,value172_second,value173_second,value174_second,value175_second,value176_second,value177_second,value178_second,value179_second,value180_second,value181_second]
  simp [view,ContactChainLimits318.view,ScaledDetectorChain318.fill,ScaledContactWeights318.fill]

lemma value183_second (w : Assignment) (c₀ t₀ c t : ℚ) :
      ContactChainWitness318.value183 (view (ScaledDetectorChain318.fill 0 w c₀ t₀) c t)=
        ContactChainWitness318.value183 (view w c t) := by
  simp only [ContactChainWitness318.value183,value159_second,value160_second,value161_second,value162_second,value163_second,value164_second,value165_second,value166_second,value167_second,value168_second,value169_second,value170_second,value171_second,value172_second,value173_second,value174_second,value175_second,value176_second,value177_second,value178_second,value179_second,value180_second,value181_second,value182_second]
  simp [view,ContactChainLimits318.view,ScaledDetectorChain318.fill,ScaledContactWeights318.fill]

lemma value184_second (w : Assignment) (c₀ t₀ c t : ℚ) :
      ContactChainWitness318.value184 (view (ScaledDetectorChain318.fill 0 w c₀ t₀) c t)=
        ContactChainWitness318.value184 (view w c t) := by
  simp only [ContactChainWitness318.value184,value159_second,value160_second,value161_second,value162_second,value163_second,value164_second,value165_second,value166_second,value167_second,value168_second,value169_second,value170_second,value171_second,value172_second,value173_second,value174_second,value175_second,value176_second,value177_second,value178_second,value179_second,value180_second,value181_second,value182_second,value183_second]
  simp [view,ContactChainLimits318.view,ScaledDetectorChain318.fill,ScaledContactWeights318.fill]

lemma value185_second (w : Assignment) (c₀ t₀ c t : ℚ) :
      ContactChainWitness318.value185 (view (ScaledDetectorChain318.fill 0 w c₀ t₀) c t)=
        ContactChainWitness318.value185 (view w c t) := by
  simp only [ContactChainWitness318.value185,value159_second,value160_second,value161_second,value162_second,value163_second,value164_second,value165_second,value166_second,value167_second,value168_second,value169_second,value170_second,value171_second,value172_second,value173_second,value174_second,value175_second,value176_second,value177_second,value178_second,value179_second,value180_second,value181_second,value182_second,value183_second,value184_second]
  simp [view,ContactChainLimits318.view,ScaledDetectorChain318.fill,ScaledContactWeights318.fill]

lemma value186_second (w : Assignment) (c₀ t₀ c t : ℚ) :
      ContactChainWitness318.value186 (view (ScaledDetectorChain318.fill 0 w c₀ t₀) c t)=
        ContactChainWitness318.value186 (view w c t) := by
  simp only [ContactChainWitness318.value186,value159_second,value160_second,value161_second,value162_second,value163_second,value164_second,value165_second,value166_second,value167_second,value168_second,value169_second,value170_second,value171_second,value172_second,value173_second,value174_second,value175_second,value176_second,value177_second,value178_second,value179_second,value180_second,value181_second,value182_second,value183_second,value184_second,value185_second]
  simp [view,ContactChainLimits318.view,ScaledDetectorChain318.fill,ScaledContactWeights318.fill]

lemma value187_second (w : Assignment) (c₀ t₀ c t : ℚ) :
      ContactChainWitness318.value187 (view (ScaledDetectorChain318.fill 0 w c₀ t₀) c t)=
        ContactChainWitness318.value187 (view w c t) := by
  simp only [ContactChainWitness318.value187,value159_second,value160_second,value161_second,value162_second,value163_second,value164_second,value165_second,value166_second,value167_second,value168_second,value169_second,value170_second,value171_second,value172_second,value173_second,value174_second,value175_second,value176_second,value177_second,value178_second,value179_second,value180_second,value181_second,value182_second,value183_second,value184_second,value185_second,value186_second]
  simp [view,ContactChainLimits318.view,ScaledDetectorChain318.fill,ScaledContactWeights318.fill]

lemma value188_second (w : Assignment) (c₀ t₀ c t : ℚ) :
      ContactChainWitness318.value188 (view (ScaledDetectorChain318.fill 0 w c₀ t₀) c t)=
        ContactChainWitness318.value188 (view w c t) := by
  simp only [ContactChainWitness318.value188,value159_second,value160_second,value161_second,value162_second,value163_second,value164_second,value165_second,value166_second,value167_second,value168_second,value169_second,value170_second,value171_second,value172_second,value173_second,value174_second,value175_second,value176_second,value177_second,value178_second,value179_second,value180_second,value181_second,value182_second,value183_second,value184_second,value185_second,value186_second,value187_second]
  simp [view,ContactChainLimits318.view,ScaledDetectorChain318.fill,ScaledContactWeights318.fill]

lemma realChain_second (w : Assignment) (c₀ t₀ c t : ℚ) :
      realChain (ScaledDetectorChain318.fill 0 w c₀ t₀) c t=realChain w c t :=
    value187_second w c₀ t₀ c t

lemma imagChain_second (w : Assignment) (c₀ t₀ c t : ℚ) :
      imagChain (ScaledDetectorChain318.fill 0 w c₀ t₀) c t=imagChain w c t :=
    value188_second w c₀ t₀ c t

lemma traceQuotient_second (w : Assignment) (c₀ t₀ c t : ℚ) :
      traceQuotient (ScaledDetectorChain318.fill 0 w c₀ t₀) c t=traceQuotient w c t := by
  simp only [traceQuotient,realChain_second,imagChain_second]

lemma poleInput_second (w : Assignment) (c₀ t₀ c t : ℚ) :
      poleInput (ScaledDetectorChain318.fill 0 w c₀ t₀) c t=poleInput w c t := by
  simp only [poleInput,traceQuotient_second,realChain_second,imagChain_second]

lemma squareFactor_second (w : Assignment) (c₀ t₀ c t : ℚ) :
      squareFactor (ScaledDetectorChain318.fill 0 w c₀ t₀) c t=squareFactor w c t := by
  simp only [squareFactor,traceQuotient_second,realChain_second,imagChain_second]

end ChainInputInvariance318
