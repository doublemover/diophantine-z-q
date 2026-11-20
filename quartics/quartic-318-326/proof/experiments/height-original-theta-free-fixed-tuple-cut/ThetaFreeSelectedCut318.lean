module
public import CMIsogeny318
public import ContactHeight318
public section
noncomputable section

namespace ThetaFreeSelectedCut318
open ContactRadical318 ContactHeight318

/-- Actual fifteen-prime product times the odd contact radical for this point. -/
def support (u v : ℤ) : ℝ := ((badProduct*radical u v : ℕ) : ℝ)

theorem support_lower (u v : ℤ) : 11185621387570686764517810≤support u v := by
  have hr : 1≤radical u v := radical_pos u v
  unfold support
  rw [bad_product_exact]
  exact_mod_cast (by omega : 11185621387570686764517810≤11185621387570686764517810*radical u v)

private theorem support_large (u v : ℤ) : 1000000≤support u v :=
  (by norm_num : (1000000:ℝ)≤11185621387570686764517810).trans (support_lower u v)

theorem log_margin {S:ℝ} (hb:11185621387570686764517810≤S) : 5≤Real.log S ∧ 1000000*(Real.log S)^2≤S := by
  have hs : 0<S := lt_of_lt_of_le (by norm_num : (0:ℝ)<11185621387570686764517810) hb
  have hx:=Real.log_le_log (by norm_num : (0:ℝ)<2^10) ((by norm_num : (2:ℝ)^10≤11185621387570686764517810).trans hb)
  rw [Real.log_pow] at hx
  norm_num only [Nat.cast_ofNat] at hx
  have hl : 5≤Real.log S := by linarith [Real.log_two_gt_d9]
  let t:=Real.sqrt S
  let y:=Real.sqrt t
  have ht : t^2=S := Real.sq_sqrt hs.le
  have ht0 : 0<t := Real.sqrt_pos.mpr hs
  have hy : y^2=t := Real.sq_sqrt ht0.le
  have hy0 : 0<y := Real.sqrt_pos.mpr ht0
  have hh : Real.log S=4*Real.log y := by
    have h1:=Real.log_sqrt hs.le
    have h2:=Real.log_sqrt ht0.le
    change Real.log t=Real.log S/2 at h1
    change Real.log y=Real.log t/2 at h2
    linarith
  have hxy : Real.log S≤4*y := by linarith [Real.log_le_sub_one_of_pos hy0]
  have hxx := pow_le_pow_left₀ (by linarith : 0≤Real.log S) hxy 2
  have hbt : 16000000≤t := by
    apply (sq_le_sq₀ (by norm_num : (0:ℝ)≤16000000) ht0.le).mp
    rw [ht];exact (by norm_num : (16000000:ℝ)^2≤11185621387570686764517810).trans hb
  exact ⟨hl,by nlinarith only [hxx,hy,ht,mul_le_mul_of_nonneg_right hbt ht0.le]⟩

/-- Arithmetic part of finite Galois Hom-lattice descent. The input hd is
the logarithmic Minkowski bound for the actual lattice and its ground field;
it is not claimed as a native theorem about abelian varieties. -/
theorem hom_field_576 {S g n D:ℝ} (hb:11185621387570686764517810≤S) (hg:1≤g) (hgen:g≤S^5)
    (hn:1≤n) (hr:n≤8*g)
    (hd:Real.log D≤Real.log 576+3*n*Real.log 2+
      2*n*(1+Real.log n)*Real.log (n+1)) :
    Real.log D≤S^6/1000 := by
  let x:=Real.log S
  obtain ⟨hx,hsmall⟩:=log_margin hb
  change 5≤x at hx
  change 1000000*x^2≤S at hsmall
  have hs : 10≤S := (by norm_num : (10:ℝ)≤11185621387570686764517810).trans hb
  have hs1 : (1:ℝ)≤S^5 := one_le_pow₀ (by linarith)
  have hp : n+1≤S^6 := by
    rw [pow_succ]
    nlinarith only [hr,hgen,hs1,mul_le_mul_of_nonneg_left hs (show 0≤S^5 by positivity)]
  have hlog:=Real.log_le_log (by linarith : 0<n+1) hp
  rw [Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  change Real.log (n+1)≤6*x at hlog
  have hlogn : Real.log n≤6*x := (Real.log_le_log (by linarith) (by linarith : n≤n+1)).trans hlog
  have hm : 2*n*(1+Real.log n)*Real.log (n+1)≤2*(8*g)*(7*x)*(6*x) := by
    gcongr <;> first | assumption | positivity | linarith [Real.log_nonneg hn]
  have h2 : 3*n*Real.log 2≤24*g := by
    have hm:=mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le (show 0≤3*n by linarith)
    linarith
  have h8 : Real.log (576:ℝ)≤8 := by linarith [CMIsogeny318.log_576]
  have h1 : 1≤x^2 := by nlinarith [sq_nonneg (x-1)]
  have hg1 : g≤g*x^2 := by simpa using mul_le_mul_of_nonneg_left h1 (show 0≤g by linarith)
  have htot : Real.log D≤1000*g*x^2 := by nlinarith only [hd,hm,h2,h8,hg,hg1]
  have hbnd:=mul_le_mul_of_nonneg_right hgen (sq_nonneg x)
  have hbig:=mul_le_mul_of_nonneg_left hsmall (show 0≤S^5 by positivity)
  nlinarith only [htot,hbnd,hbig]

theorem forward_constant : Real.log (540225/4 : ℝ)<12 := by
  have h := Real.log_lt_log (by positivity : 0<(540225/4:ℝ)^4)
    (by norm_num : (540225/4:ℝ)^4<2^69)
  rw [Real.log_pow,Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith [Real.log_two_lt_d9]

private theorem gross_margin {S : ℝ} (hS : 1000000≤S) : 1000000*S≤S^6 := by
  have h : S≤S^5 := by simpa using
    (pow_le_pow_right₀ (by linarith : 1≤S) (by decide : 1≤5))
  calc 1000000*S ≤ S^5*S := mul_le_mul_of_nonneg_right (hS.trans h) (by linarith)
       _ = _ := (pow_succ S 5).symm

/-- Actual CM point, with hA using the unshifted surface convention. The
earlier surface height and genuine selected-point comparison are inputs,
not replaced by an assumed upper bound on the input detector or its height. -/
theorem cm {u v : ℤ} {hA : ℝ}
    (height : pointHeight u v≤2*(hA+Real.log Real.pi)+Real.log (540225/4 : ℝ))
    (cmHeight : hA<854*support u v) :
    pointHeight u v<(support u v)^6/2 := by
  have hS:=support_large u v
  have hπ : Real.log Real.pi≤3 := (Real.log_le_sub_one_of_pos Real.pi_pos).trans
    (by linarith [Real.pi_lt_four])
  linarith [gross_margin hS,forward_constant]

/-- The literal directional height on the same A, Faltings variation for a
chosen isogeny from the dimension-two quotient, and the GR degree bound
centered at that quotient. The logarithmic degree of the initial modular
map is irrelevant. delta denotes [E:Q], *not* the height-576 base degree. -/
theorem noncm {u v : ℤ} {hY b delta deg : ℝ}
    (height : pointHeight u v≤2*hY+Real.log (540225/4 : ℝ))
    (variation : hY≤b+(1/2)*Real.log deg)
    (hd : 0<delta) (he : 0<deg)
    (degree : deg≤(CMIsogeny318.Xi delta (b-Real.log Real.pi))^2)
    (homField : Real.log delta≤(support u v)^6/1000)
    (quotient : b≤2*(support u v)^6/1000) :
    pointHeight u v<(support u v)^6/2 := by
  let S := support u v
  have hS : 1000000≤S := support_large u v
  change Real.log delta≤S^6/1000 at homField
  change b≤2*S^6/1000 at quotient
  change pointHeight u v<S^6/2
  have hg := gross_margin hS
  have hπ := Real.log_nonneg (by linarith [Real.pi_gt_three] : 1≤Real.pi)
  have hmax : max 1 (max (Real.log delta) (b-Real.log Real.pi))≤S^6 := by
    apply max_le (by linarith)
    apply max_le <;> linarith
  have hlog := Real.log_le_log (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_left _ _)) hmax
  rw [Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hlogS := Real.log_le_sub_one_of_pos (by linarith : 0<S)
  have hGR := CMIsogeny318.half_log_degree delta (b-Real.log Real.pi) deg hd he degree
  linarith [CMIsogeny318.log_fourteen,forward_constant]

/-- Numerical terminal retaining the actual base-576 descent bound and the m≤2
signed quotient rows b≤6g log S. No log-delta or b cutoffs are pre-assumed. -/
theorem from_signed_rows {u v : ℤ} {g n delta deg b hY : ℝ}
    (hg : 1≤g) (hgen : g≤(support u v)^5) (hn : 1≤n) (hr : n≤8*g)
    (desc : Real.log delta≤Real.log 576+3*n*Real.log 2+2*n*(1+Real.log n)*Real.log (n+1))
    (rows : b≤6*g*Real.log (support u v))
    (height : pointHeight u v≤2*hY+Real.log (540225/4 : ℝ))
    (variation : hY≤b+(1/2)*Real.log deg) (hd : 0<delta) (he : 0<deg)
    (degree : deg≤(CMIsogeny318.Xi delta (b-Real.log Real.pi))^2) :
    pointHeight u v<(support u v)^6/2 := by
  let S:=support u v
  have hS : 0≤S := by linarith [support_lower u v]
  obtain ⟨hx,hs⟩:=log_margin (support_lower u v)
  change 5≤Real.log S at hx
  change 1000000*(Real.log S)^2≤S at hs
  change b≤6*g*Real.log S at rows
  change g≤S^5 at hgen
  have hlog : 3*Real.log S≤(Real.log S)^2 := by nlinarith [sq_nonneg (Real.log S-4)]
  have bound : b≤2*S^6/1000 := by
    have h1 := mul_le_mul_of_nonneg_right hgen (show 0≤Real.log S by linarith)
    have h2 := mul_le_mul_of_nonneg_left hlog (show 0≤S^5 by positivity)
    have h3 := mul_le_mul_of_nonneg_left hs (show 0≤S^5 by positivity)
    nlinarith only [rows,h1,h2,h3,pow_nonneg hS 6]
  exact noncm height variation hd he degree
    (hom_field_576 (support_lower u v) hg hgen hn hr desc) bound

end ThetaFreeSelectedCut318
