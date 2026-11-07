module
public import RawAnchorNorm318
public import RawSourcePole318
public import CompressedGlobal318
public section
namespace ScalarSource318
open CircuitReplay Raw318FinalReplay ConcreteG8Domain
open scoped QuadraticAlgebra
set_option maxHeartbeats 0
set_option maxRecDepth 100000
@[expose] def r (w:Assignment):ℚ :=
  101783690143177584*w 0+101783690143177584*w 118+
  267108917866935984*w 296+533801448346128768*w 297+4376874610839020
@[expose] def N (w:Assignment):ℚ := 1+w 311
@[expose] def Q (w:Assignment):ℚ := w 310
@[expose] def W (w:Assignment):ℚ := (N w)^2+r w*(Q w)^2

/-- Decode the literal current scalar quotient rows, including the emitted
inverse power 16 and the separate division by n_H/r. -/
theorem equations (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w) :
    r w*w 298=1 ∧ w 302=(w 298)^16 ∧ r w*w 309=w 37 ∧
    w 309*Q w=w 308*w 302 ∧ N w=1+(w 309)^2+2*w 33*w 298 ∧
    (1+114444*r w)*w 313=W w ∧ w 298*w 314=114444*(w 313)^2 := by
  have h265:r265 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=265)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r265] at h265
  have h266:r266 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=266)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r266] at h266
  have h267:r267 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=267)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r267] at h267
  have h268:r268 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=268)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r268] at h268
  have h269:r269 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=269)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r269] at h269
  have h276:r276 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=276)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r276] at h276
  have h277:r277 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=277)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r277] at h277
  have h278:r278 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=278)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r278] at h278
  have h279:r279 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=279)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r279] at h279
  have h280:r280 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=280)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r280] at h280
  have h281:r281 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=281)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r281] at h281
  have h299:w 299=(w 298)^2 := by linear_combination h266
  have h300:w 300=(w 298)^4 := by rw [h299] at h267; linear_combination h267
  have h301:w 301=(w 298)^8 := by rw [h300] at h268; linear_combination h268
  have h302:w 302=(w 298)^16 := by rw [h301] at h269; linear_combination h269
  have h312:w 312=(w 310)^2 := by linear_combination h279
  refine ⟨?_,h302,?_,?_,?_,?_,?_⟩
  · dsimp [r]; linear_combination h265
  · dsimp [r]; linear_combination h276
  · dsimp [Q]; linear_combination h277
  · dsimp [N]; linear_combination h278
  · dsimp [W,N,Q,r]
    rw [h312] at h280
    linear_combination h280
  · linear_combination h281

theorem r_inverse (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w) :
    r w≠0 ∧ w 298=(r w)⁻¹ := by
  have hh := (equations S w source).1
  exact ⟨left_ne_zero_of_mul_eq_one hh,eq_inv_of_mul_eq_one_left (by simpa [mul_comm] using hh)⟩

theorem Q_nonzero (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w) : Q w≠0 := by
  obtain ⟨hri,hpow,hscale,hQ,-⟩ := equations S w source
  have hri0:w 298≠0 := right_ne_zero_of_mul_eq_one hri
  have hnR := (RawAnchorNorm318.scalar_inverse_norm S w source).2.2
  have hprod:w 309*Q w≠0 := by rw [hQ,hpow]; exact mul_ne_zero hnR (pow_ne_zero _ hri0)
  exact (mul_ne_zero_iff.mp hprod).2

/-- This is the exact cleared pole relation; its zero normalizer branch
need not be discarded to derive local soundness at a positive contact. -/
theorem pole_relation (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w) :
    w 314*(1+114444*r w)^2=114444*r w*(W w)^2 := by
  obtain ⟨hri,hpow,hscale,hQ,hN,hW,hb⟩ := equations S w source
  have hb':w 314=114444*r w*(w 313)^2 := by
    calc
      w 314=(r w*w 298)*w 314 := by rw [hri,one_mul]
      _=114444*r w*(w 313)^2 := by rw [mul_assoc,hb]; ring
  rw [hb',←hW]
  ring

/-- The nonzero normalized quotient numerator forces n_H nonzero in the
literal rows, without assuming a sign of H or a group label. -/
theorem normH_nonzero (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w) : w 37≠0 := by
  obtain ⟨hri,hpow,hscale,hQ,-⟩ := equations S w source
  have hri0:w 298≠0 := right_ne_zero_of_mul_eq_one hri
  have hnR := (RawAnchorNorm318.scalar_inverse_norm S w source).2.2
  have hprod:w 309*Q w≠0 := by rw [hQ,hpow]; exact mul_ne_zero hnR (pow_ne_zero _ hri0)
  rw [←hscale]
  exact mul_ne_zero (left_ne_zero_of_mul_eq_one hri) (mul_ne_zero_iff.mp hprod).1

/-- The exact effective exponent is fifteen, not sixteen. -/
theorem Q_formula (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w) :
    Q w=w 308/(w 37*(r w)^15) := by
  obtain ⟨hri,hpow,hscale,hQ,-⟩ := equations S w source
  have hr0 := (r_inverse S w source).1
  have hn0 := normH_nonzero S w source
  apply (eq_div_iff (mul_ne_zero hn0 (pow_ne_zero _ hr0))).mpr
  calc
    Q w*(w 37*(r w)^15)=(w 309*Q w)*(r w)^16 := by rw [←hscale]; ring
    _=w 308*(r w*w 298)^16 := by rw [hQ,hpow]; ring
    _=w 308 := by rw [hri]; simp

/-- Standard quadratic norm identity with a nonzero rational denominator. -/
theorem norm_one_add_div (a b t:ℚ) (ht:t≠0) :
    AnchorNorm318.norm (1+pair a b/pair t 0)=1+2*a/t+(a^2-2*b^2)/t^2 := by
  have htK:pair t 0≠(0:K) := by intro hh; exact ht (congrArg QuadraticAlgebra.re hh)
  have he:(1+pair a b/pair t 0)*pair t 0=pair (t+a) b := by
    rw [add_mul,one_mul,div_mul_cancel₀ _ htK]
    ext <;> simp [pair]
  have hn:=congrArg AnchorNorm318.norm he
  rw [AnchorNorm318.norm_mul,AnchorNorm318.norm_pair,AnchorNorm318.norm_pair] at hn
  norm_num at hn
  generalize AnchorNorm318.norm (1+pair a b/pair t 0)=n at *
  field_simp [ht]
  linear_combination hn

theorem N_formula (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w) :
    N w=AnchorNorm318.norm (1+CompressedOrientation318.fH w/pair (r w) 0) := by
  obtain ⟨hri,hpow,hscale,hQ,hN,-⟩ := equations S w source
  have hr0 := (r_inverse S w source).1
  have h309:w 309=w 37/r w := (eq_div_iff hr0).mpr (by simpa [mul_comm] using hscale)
  have hn:(w 37)^2=(w 33)^2-2*(w 34)^2 := by
    have hh:=CompressedGlobal318.source_norm_square S w source
    simpa [CompressedOrientation318.fH,AnchorNorm318.norm_pair] using hh.symm
  rw [hN,h309,(r_inverse S w source).2]
  change _=AnchorNorm318.norm (1+pair (w 33) (w 34)/pair (r w) 0)
  rw [norm_one_add_div _ _ _ hr0]
  field_simp [hr0]
  linear_combination hn

@[expose] noncomputable def fR (w:Assignment):K := ((RawAnchorNorm318.scalarRoot w)⁻¹)^2

theorem norm_ratio (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w) :
    AnchorNorm318.norm (fR w/CompressedOrientation318.fH w)=(w 308/w 37)^2 := by
  rw [AnchorNorm318.norm_div,fR,AnchorNorm318.norm_pow,AnchorNorm318.norm_inv]
  rw [←(RawAnchorNorm318.scalar_inverse_norm S w source).1]
  rw [show AnchorNorm318.norm (CompressedOrientation318.fH w)=(w 37)^2 from
    CompressedGlobal318.source_norm_square S w source]
  exact (div_pow _ _ _).symm

@[expose] def beta (w:Assignment):ℚ := 3723*(2*w 0+1)^2

/-- Bind the decoded raw scalar parameter to the exact four-factor contact
polynomial in the user's current input beta. -/
theorem r_formula (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w) :
    r w=(beta w-1)*(beta w-2401)*(32*beta w+343)*(2*beta w-1) := by
  have h79:r79 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=79)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r79] at h79
  have h263:r263 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=263)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r263] at h263
  have h264:r264 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=264)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r264] at h264
  have h118:w 118=(w 0)^2 := by linear_combination h79
  have h296:w 296=(w 0+w 118)^2 := by linear_combination h263
  have h297:w 297=(w 0+w 118)^2+(496408687/100291113:ℚ)*(w 0+w 118)*w 296+
      (197130368/33430371:ℚ)*(w 296)^2 := by linear_combination h264
  dsimp only [r,beta]
  rw [h297,h296,h118]
  ring

end ScalarSource318
#print axioms ScalarSource318.equations
#print axioms ScalarSource318.r_inverse
#print axioms ScalarSource318.Q_nonzero
#print axioms ScalarSource318.pole_relation

#print axioms ScalarSource318.Q_formula
#print axioms ScalarSource318.N_formula
#print axioms ScalarSource318.norm_ratio

#print axioms ScalarSource318.r_formula
