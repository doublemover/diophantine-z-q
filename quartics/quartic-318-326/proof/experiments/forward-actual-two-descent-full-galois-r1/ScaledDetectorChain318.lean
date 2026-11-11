module
public import ScaledContactWeights318
public section
noncomputable section
namespace ScaledDetectorChain318
open CircuitReplay Raw318FinalReplay ScaledContactWeights318 ContactWeightWitness318
set_option maxHeartbeats 0
set_option maxRecDepth 100000

@[expose] def view (w : Assignment) (c t : ℚ) : Assignment :=
  ContactChainLimits318.view w (scaledWeight c t)
    ((scaledWeight c t)^7*(delta c t)^18) ((scaledWeight c t)^25*(delta c t)^72)
@[expose] def realChain (w : Assignment) (c t : ℚ) : ℚ := ContactChainWitness318.value187 (view w c t)
@[expose] def imagChain (w : Assignment) (c t : ℚ) : ℚ := ContactChainWitness318.value188 (view w c t)
@[expose] def traceQuotient (w : Assignment) (c t : ℚ) : ℚ :=
  ((realChain w c t)^2-2*(imagChain w c t)^2)/(2*realChain w c t)
@[expose] def poleInput (w : Assignment) (c t : ℚ) : ℚ :=
  (traceQuotient w c t)^2*contact (parameter c t)/(c^10*(delta c t)^6)
@[expose] def squareFactor (w : Assignment) (c t : ℚ) : ℚ :=
  traceQuotient w c t/(c^5*(delta c t)^3)

@[expose] def fill (offset : ℕ) (w : Assignment) (c t : ℚ) : Assignment := fun i =>
  if i=210+51*offset then ContactChainWitness318.value159 (view w c t) else
  if i=211+51*offset then ContactChainWitness318.value160 (view w c t) else
  if i=212+51*offset then ContactChainWitness318.value161 (view w c t) else
  if i=213+51*offset then ContactChainWitness318.value162 (view w c t) else
  if i=214+51*offset then ContactChainWitness318.value163 (view w c t) else
  if i=215+51*offset then ContactChainWitness318.value164 (view w c t) else
  if i=216+51*offset then ContactChainWitness318.value165 (view w c t) else
  if i=217+51*offset then ContactChainWitness318.value166 (view w c t) else
  if i=218+51*offset then ContactChainWitness318.value167 (view w c t) else
  if i=219+51*offset then ContactChainWitness318.value168 (view w c t) else
  if i=220+51*offset then ContactChainWitness318.value169 (view w c t) else
  if i=221+51*offset then ContactChainWitness318.value170 (view w c t) else
  if i=222+51*offset then ContactChainWitness318.value171 (view w c t) else
  if i=223+51*offset then ContactChainWitness318.value172 (view w c t) else
  if i=224+51*offset then ContactChainWitness318.value173 (view w c t) else
  if i=225+51*offset then ContactChainWitness318.value174 (view w c t) else
  if i=226+51*offset then ContactChainWitness318.value175 (view w c t) else
  if i=227+51*offset then ContactChainWitness318.value176 (view w c t) else
  if i=228+51*offset then ContactChainWitness318.value177 (view w c t) else
  if i=229+51*offset then ContactChainWitness318.value178 (view w c t) else
  if i=230+51*offset then ContactChainWitness318.value179 (view w c t) else
  if i=231+51*offset then ContactChainWitness318.value180 (view w c t) else
  if i=232+51*offset then ContactChainWitness318.value181 (view w c t) else
  if i=233+51*offset then ContactChainWitness318.value182 (view w c t) else
  if i=234+51*offset then ContactChainWitness318.value183 (view w c t) else
  if i=235+51*offset then ContactChainWitness318.value184 (view w c t) else
  if i=236+51*offset then ContactChainWitness318.value185 (view w c t) else
  if i=237+51*offset then ContactChainWitness318.value186 (view w c t) else
  if i=238+51*offset then ContactChainWitness318.value187 (view w c t) else
  if i=239+51*offset then ContactChainWitness318.value188 (view w c t) else
  if i=240+51*offset then traceQuotient w c t else
  if i=241+51*offset then poleInput w c t else ScaledContactWeights318.fill offset w c t i

lemma squareclass (w : Assignment) (c t : ℚ) :
    poleInput w c t=contact (parameter c t)*(squareFactor w c t)^2 := by
  simp only [poleInput,squareFactor,div_pow,mul_pow,←pow_mul]
  norm_num <;> ring

/-- Thirty literal quadratic gates, transported with their actual weights. -/
theorem chain_rows1 (S : ℚ) (w : Assignment) (c t : ℚ) :
    Constraints [r173 S,r174 S,r175 S,r176 S,r177 S,r178 S,r179 S,r180 S,r181 S,r182 S,r183 S,r184 S,r185 S,r186 S,r187 S,r188 S,r189 S,r190 S,r191 S,r192 S,r193 S,r194 S,r195 S,r196 S,r197 S,r198 S,r199 S,r200 S,r201 S,r202 S] (fill 0 w c t) := by
  simp only [Constraints,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp]
  refine ⟨?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ⟩
  · norm_num [r173,fill,ScaledContactWeights318.fill,ContactChainWitness318.value159,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r174,fill,ScaledContactWeights318.fill,ContactChainWitness318.value160,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r175,fill,ScaledContactWeights318.fill,ContactChainWitness318.value161,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r176,fill,ScaledContactWeights318.fill,ContactChainWitness318.value162,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r177,fill,ScaledContactWeights318.fill,ContactChainWitness318.value163,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r178,fill,ScaledContactWeights318.fill,ContactChainWitness318.value164,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r179,fill,ScaledContactWeights318.fill,ContactChainWitness318.value165,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r180,fill,ScaledContactWeights318.fill,ContactChainWitness318.value166,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r181,fill,ScaledContactWeights318.fill,ContactChainWitness318.value167,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r182,fill,ScaledContactWeights318.fill,ContactChainWitness318.value168,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r183,fill,ScaledContactWeights318.fill,ContactChainWitness318.value169,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r184,fill,ScaledContactWeights318.fill,ContactChainWitness318.value170,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r185,fill,ScaledContactWeights318.fill,ContactChainWitness318.value171,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r186,fill,ScaledContactWeights318.fill,ContactChainWitness318.value172,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r187,fill,ScaledContactWeights318.fill,ContactChainWitness318.value173,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r188,fill,ScaledContactWeights318.fill,ContactChainWitness318.value174,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r189,fill,ScaledContactWeights318.fill,ContactChainWitness318.value175,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r190,fill,ScaledContactWeights318.fill,ContactChainWitness318.value176,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r191,fill,ScaledContactWeights318.fill,ContactChainWitness318.value177,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r192,fill,ScaledContactWeights318.fill,ContactChainWitness318.value178,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r193,fill,ScaledContactWeights318.fill,ContactChainWitness318.value179,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r194,fill,ScaledContactWeights318.fill,ContactChainWitness318.value180,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r195,fill,ScaledContactWeights318.fill,ContactChainWitness318.value181,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r196,fill,ScaledContactWeights318.fill,ContactChainWitness318.value182,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r197,fill,ScaledContactWeights318.fill,ContactChainWitness318.value183,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r198,fill,ScaledContactWeights318.fill,ContactChainWitness318.value184,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r199,fill,ScaledContactWeights318.fill,ContactChainWitness318.value185,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r200,fill,ScaledContactWeights318.fill,ContactChainWitness318.value186,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r201,fill,ScaledContactWeights318.fill,ContactChainWitness318.value187,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r202,fill,ScaledContactWeights318.fill,ContactChainWitness318.value188,
      view,ContactChainLimits318.view] <;> ring
lemma trace_row1 (S : ℚ) (w : Assignment) (c t : ℚ)
    (hr : realChain w c t≠0) : r203 S (fill 0 w c t)=0 := by
  norm_num [r203,fill,ScaledContactWeights318.fill]
  change -(1/2*realChain w c t*realChain w c t)+realChain w c t*traceQuotient w c t+
    imagChain w c t*imagChain w c t=0
  unfold traceQuotient
  field_simp [hr] <;> ring

lemma pole_gate (w : Assignment) (c t : ℚ)
    (hc : c≠0) (hd : delta c t≠0) (hF : contact (parameter c t)≠0) :
    -(scaledWeight c t*(delta c t)^3*poleInput w c t)+
      parameter c t*scaledWeight c t*(delta c t)^3*poleInput w c t+
      -(traceQuotient w c t*traceQuotient w c t)=0 := by
  have hs := scaled_contact_identity c t hF
  have hp : scaledWeight c t*(delta c t)^4*poleInput w c t=(traceQuotient w c t)^2 := by
    unfold poleInput
    calc
      _=(contact (parameter c t)*scaledWeight c t)*
        ((traceQuotient w c t)^2*(delta c t)^4)/(c^10*(delta c t)^6) := by ring
      _=(c^10*(delta c t)^2)*
        ((traceQuotient w c t)^2*(delta c t)^4)/(c^10*(delta c t)^6) := by rw [hs]
      _=(traceQuotient w c t)^2 := by field_simp [hc,hd] <;> ring
  have ht : parameter c t=delta c t+1 := by dsimp [delta]; ring
  rw [ht]
  calc
    _=scaledWeight c t*(delta c t)^4*poleInput w c t-(traceQuotient w c t)^2 := by ring
    _=0 := by rw [hp,sub_self]

lemma pole_row1 (S : ℚ) (w : Assignment) (c t : ℚ)
    (hc : c≠0) (hd : delta c t≠0) (hF : contact (parameter c t)≠0) : r204 S (fill 0 w c t)=0 := by
  norm_num [r204,fill,ScaledContactWeights318.fill]
  exact pole_gate w c t hc hd hF

/-- Thirty literal quadratic gates, transported with their actual weights. -/
theorem chain_rows2 (S : ℚ) (w : Assignment) (c t : ℚ) :
    Constraints [r226 S,r227 S,r228 S,r229 S,r230 S,r231 S,r232 S,r233 S,r234 S,r235 S,r236 S,r237 S,r238 S,r239 S,r240 S,r241 S,r242 S,r243 S,r244 S,r245 S,r246 S,r247 S,r248 S,r249 S,r250 S,r251 S,r252 S,r253 S,r254 S,r255 S] (fill 1 w c t) := by
  simp only [Constraints,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp]
  refine ⟨?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ⟩
  · norm_num [r226,fill,ScaledContactWeights318.fill,ContactChainWitness318.value159,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r227,fill,ScaledContactWeights318.fill,ContactChainWitness318.value160,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r228,fill,ScaledContactWeights318.fill,ContactChainWitness318.value161,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r229,fill,ScaledContactWeights318.fill,ContactChainWitness318.value162,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r230,fill,ScaledContactWeights318.fill,ContactChainWitness318.value163,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r231,fill,ScaledContactWeights318.fill,ContactChainWitness318.value164,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r232,fill,ScaledContactWeights318.fill,ContactChainWitness318.value165,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r233,fill,ScaledContactWeights318.fill,ContactChainWitness318.value166,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r234,fill,ScaledContactWeights318.fill,ContactChainWitness318.value167,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r235,fill,ScaledContactWeights318.fill,ContactChainWitness318.value168,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r236,fill,ScaledContactWeights318.fill,ContactChainWitness318.value169,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r237,fill,ScaledContactWeights318.fill,ContactChainWitness318.value170,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r238,fill,ScaledContactWeights318.fill,ContactChainWitness318.value171,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r239,fill,ScaledContactWeights318.fill,ContactChainWitness318.value172,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r240,fill,ScaledContactWeights318.fill,ContactChainWitness318.value173,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r241,fill,ScaledContactWeights318.fill,ContactChainWitness318.value174,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r242,fill,ScaledContactWeights318.fill,ContactChainWitness318.value175,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r243,fill,ScaledContactWeights318.fill,ContactChainWitness318.value176,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r244,fill,ScaledContactWeights318.fill,ContactChainWitness318.value177,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r245,fill,ScaledContactWeights318.fill,ContactChainWitness318.value178,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r246,fill,ScaledContactWeights318.fill,ContactChainWitness318.value179,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r247,fill,ScaledContactWeights318.fill,ContactChainWitness318.value180,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r248,fill,ScaledContactWeights318.fill,ContactChainWitness318.value181,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r249,fill,ScaledContactWeights318.fill,ContactChainWitness318.value182,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r250,fill,ScaledContactWeights318.fill,ContactChainWitness318.value183,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r251,fill,ScaledContactWeights318.fill,ContactChainWitness318.value184,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r252,fill,ScaledContactWeights318.fill,ContactChainWitness318.value185,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r253,fill,ScaledContactWeights318.fill,ContactChainWitness318.value186,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r254,fill,ScaledContactWeights318.fill,ContactChainWitness318.value187,
      view,ContactChainLimits318.view] <;> ring
  · norm_num [r255,fill,ScaledContactWeights318.fill,ContactChainWitness318.value188,
      view,ContactChainLimits318.view] <;> ring
lemma trace_row2 (S : ℚ) (w : Assignment) (c t : ℚ)
    (hr : realChain w c t≠0) : r256 S (fill 1 w c t)=0 := by
  norm_num [r256,fill,ScaledContactWeights318.fill]
  change -(1/2*realChain w c t*realChain w c t)+realChain w c t*traceQuotient w c t+
    imagChain w c t*imagChain w c t=0
  unfold traceQuotient
  field_simp [hr] <;> ring

lemma pole_row2 (S : ℚ) (w : Assignment) (c t : ℚ)
    (hc : c≠0) (hd : delta c t≠0) (hF : contact (parameter c t)≠0) : r257 S (fill 1 w c t)=0 := by
  norm_num [r257,fill,ScaledContactWeights318.fill]
  exact pole_gate w c t hc hd hF

end ScaledDetectorChain318
