module
public import CompressedPoint318
public section
namespace CompressedGlobal318
open ConcreteG8Domain (K pair)
open CircuitReplay Raw318FinalReplay CompressedOrientation318 RawLucasOrientation318 CompressedPoint318
open scoped QuadraticAlgebra
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section

@[expose] def anchorB (w : Assignment) : K := k^2+m*shift w+D*fV w

/-- The actual norm-square row is essential: it excludes the torsion poles
without assuming a real sign or a square reciprocal abscissa. -/
theorem source_norm_square (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    QuadraticAlgebra.norm (fH w)=(w 37)^2 := by
  have h38 : r38 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=38)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r38] at h38
  norm_num [fH,pair,QuadraticAlgebra.norm_def]
  linear_combination -h38

theorem norm_square_obstruction (f : K) (n : ℚ)
    (hn : QuadraticAlgebra.norm f=n^2) : D*f^2≠1 := by
  intro he
  have hh := congrArg QuadraticAlgebra.norm he
  rw [map_mul,map_pow,map_one,hn] at hh
  have hD : QuadraticAlgebra.norm D=(49:ℚ) := by
    norm_num [D,pair,QuadraticAlgebra.norm_def]
  rw [hD] at hh
  have hbad : 7*n^2=1 := by nlinarith [sq_nonneg n]
  exact ConcreteQuadraticDomains.seven_times_square_ne_one n hbad

theorem source_A_ne (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    anchorA w≠0 := by
  have hh := source_ordinate_identity S w source
  intro hA
  rw [hA,zero_pow (by decide : 2≠0),mul_zero] at hh
  have hz : 1-D*(fH w)^2=0 :=
    (mul_eq_zero.mp hh.symm).resolve_left (pow_ne_zero 2 k_ne)
  exact norm_square_obstruction (fH w) (w 37) (source_norm_square S w source)
    (by linear_combination -hz)

theorem compression_B_identity {F : Type*} [Field F] (f s k m D : F)
    (hP : m^2=k^4-D)
    (hF : 1=k^2*(f+f*s^2)+2*m*(f*s)+D*(f*s)^2) :
    f*(k^2+m*s+D*f*s^2)^2=k^2*(1-D*f^2*s^4) := by
  linear_combination f*s^2*hP-(k^2+D*f*s^2)*hF

theorem source_B_identity (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    fH w*(anchorB w)^2=k^2*(1-D*(fV w)^2) := by
  obtain ⟨ht,hg⟩ := source_products S w source
  have he := (source_relations S w source).2
  rw [ht,hg] at he
  have hh := compression_B_identity (fH w) (shift w) k m D constant_equation he
  dsimp only [anchorB]
  rw [hg]
  convert hh using 1 <;> ring

theorem source_V_norm_square (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    QuadraticAlgebra.norm (fV w)=(w 37*QuadraticAlgebra.norm (shift w))^2 := by
  rw [(source_products S w source).2,map_mul,map_pow,source_norm_square S w source]
  ring

theorem source_B_ne (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    anchorB w≠0 := by
  have hh := source_B_identity S w source
  intro hB
  rw [hB,zero_pow (by decide : 2≠0),mul_zero] at hh
  have hz : 1-D*(fV w)^2=0 :=
    (mul_eq_zero.mp hh.symm).resolve_left (pow_ne_zero 2 k_ne)
  exact norm_square_obstruction (fV w) _ (source_V_norm_square S w source)
    (by linear_combination -hz)

/-- Globally, every actual source assignment yields a finite nonzero-ordinate H;
local positivity was not needed to justify any division. -/
theorem source_global_H (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    fH w≠0 ∧ yH w≠0 ∧ E.Nonsingular (xH w) (yH w) ∧ zH w= -xH w/yH w := by
  have hA := source_A_ne S w source
  have hc := source_formal_coordinate S w source hA
  exact ⟨source_fH_ne S w source,hc.1,source_nonsingular S w source hA,hc.2⟩

@[expose] def xV (w : Assignment) : K := 1/(fH w*(shift w)^2)
@[expose] def yV (w : Assignment) : K := -anchorB w/(k*fH w*(shift w)^3)
@[expose] def zV (w : Assignment) : K := k*shift w/anchorB w

theorem source_global_V (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (hs : shift w≠0) :
    yV w≠0 ∧ E.Nonsingular (xV w) (yV w) ∧ zV w= -xV w/yV w := by
  have hf := source_fH_ne S w source
  have hB := source_B_ne S w source
  have hy : yV w≠0 := div_ne_zero (neg_ne_zero.mpr hB)
    (mul_ne_zero (mul_ne_zero k_ne hf) (pow_ne_zero 3 hs))
  refine ⟨hy,?_,?_⟩
  · rw [WeierstrassCurve.Affine.nonsingular_iff']
    constructor
    · rw [WeierstrassCurve.Affine.equation_iff]
      simp only [E,zero_mul,mul_zero,add_zero]
      have hh := source_B_identity S w source
      rw [(source_products S w source).2] at hh
      dsimp [xV,yV]
      field_simp [hf,k_ne,hs]
      linear_combination hh
    · right
      simpa [E] using mul_ne_zero (show (2:K)≠0 by norm_num) hy
  · dsimp [zV,xV,yV]
    field_simp [hf,k_ne,hs,hB]

/-- The common alternate formal numerator vanishes exactly in the allowed
V=O chart branch; its denominator is globally nonzero. -/
theorem source_zV_zero (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    zV w=0 ↔ shift w=0 := by
  simp [zV,div_eq_zero_iff,source_B_ne S w source,k_ne]

end
end CompressedGlobal318
