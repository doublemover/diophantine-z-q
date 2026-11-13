module
public import ScaledDetectorChain318
public import NormChainCompleteness
public section
noncomputable section
namespace ActualDetectorFold318
open CircuitReplay ConcreteG8Domain ContactChainWitness318
open scoped QuadraticAlgebra
set_option maxHeartbeats 1000000

/-- The actual sixteen leaves in original order, including four unsquared
conjugated v-minus-one leaves. No independent leaf values are substituted. -/
@[expose] def leaves (w : Assignment) : List (K × K) :=
  [(pair (w 156) 0,pair (w 126) (0)),
   (pair (w 151) 0,pair (w 125) (0)),
   (pair (w 151) 0,pair (w 58) (2*w 59)),
   (pair (w 151) 0,pair (w 60) (2*w 61)),
   (pair (w 151) 0,pair (2*w 62) (2*w 63)),
   (pair (w 151) 0,pair (w 64) (2*w 65)),
   (pair (w 151) 0,pair (w 19-1) (-w 20)),
   (pair (w 151) 0,pair (w 23-1) (-w 24)),
   (pair (w 151) 0,pair (w 27-1) (-w 28)),
   (pair (w 151) 0,pair (w 31-1) (-w 32)),
   (pair (w 156) 0,pair (w 127) (2*w 128)),
   (pair (w 158) 0,pair (w 129) (2*w 130)),
   (pair (w 158) 0,pair (w 131) (2*w 132)),
   (pair (w 158) 0,pair (w 133) (2*w 134)),
   (pair (w 156) 0,pair (110885832*w 0-7446*w 102+110885832*w 118+221771664*w 135+13860729) (-7446*w 103-29784*w 136)),
   (pair (w 158) 0,pair (-2*w 123+w 137+1) (-4*w 124+4*w 138))]

@[expose] def chain (w : Assignment) : K := pair (value187 w) (value188 w)

lemma step0 (w : Assignment) :
    (pair (1) (0))^2+
      pair (w 156) 0*pair (w 126) (0)=pair (value159 w) (0) := by
  ext <;> simp only [value159,pow_two,QuadraticAlgebra.re_add,
    QuadraticAlgebra.im_add,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,pair]
  all_goals ring

lemma step1 (w : Assignment) :
    (pair (value159 w) (0))^2+
      pair (w 151) 0*pair (w 125) (0)=pair (value160 w) (0) := by
  ext <;> simp only [value160,pow_two,QuadraticAlgebra.re_add,
    QuadraticAlgebra.im_add,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,pair]
  all_goals ring

lemma step2 (w : Assignment) :
    (pair (value160 w) (0))^2+
      pair (w 151) 0*pair (w 58) (2*w 59)=pair (value161 w) (value162 w) := by
  ext <;> simp only [value161,value162,pow_two,QuadraticAlgebra.re_add,
    QuadraticAlgebra.im_add,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,pair]
  all_goals ring

lemma step3 (w : Assignment) :
    (pair (value161 w) (value162 w))^2+
      pair (w 151) 0*pair (w 60) (2*w 61)=pair (value163 w) (value164 w) := by
  ext <;> simp only [value163,value164,pow_two,QuadraticAlgebra.re_add,
    QuadraticAlgebra.im_add,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,pair]
  all_goals ring

lemma step4 (w : Assignment) :
    (pair (value163 w) (value164 w))^2+
      pair (w 151) 0*pair (2*w 62) (2*w 63)=pair (value165 w) (value166 w) := by
  ext <;> simp only [value165,value166,pow_two,QuadraticAlgebra.re_add,
    QuadraticAlgebra.im_add,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,pair]
  all_goals ring

lemma step5 (w : Assignment) :
    (pair (value165 w) (value166 w))^2+
      pair (w 151) 0*pair (w 64) (2*w 65)=pair (value167 w) (value168 w) := by
  ext <;> simp only [value167,value168,pow_two,QuadraticAlgebra.re_add,
    QuadraticAlgebra.im_add,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,pair]
  all_goals ring

lemma step6 (w : Assignment) :
    (pair (value167 w) (value168 w))^2+
      pair (w 151) 0*pair (w 19-1) (-w 20)=pair (value169 w) (value170 w) := by
  ext <;> simp only [value169,value170,pow_two,QuadraticAlgebra.re_add,
    QuadraticAlgebra.im_add,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,pair]
  all_goals ring

lemma step7 (w : Assignment) :
    (pair (value169 w) (value170 w))^2+
      pair (w 151) 0*pair (w 23-1) (-w 24)=pair (value171 w) (value172 w) := by
  ext <;> simp only [value171,value172,pow_two,QuadraticAlgebra.re_add,
    QuadraticAlgebra.im_add,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,pair]
  all_goals ring

lemma step8 (w : Assignment) :
    (pair (value171 w) (value172 w))^2+
      pair (w 151) 0*pair (w 27-1) (-w 28)=pair (value173 w) (value174 w) := by
  ext <;> simp only [value173,value174,pow_two,QuadraticAlgebra.re_add,
    QuadraticAlgebra.im_add,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,pair]
  all_goals ring

lemma step9 (w : Assignment) :
    (pair (value173 w) (value174 w))^2+
      pair (w 151) 0*pair (w 31-1) (-w 32)=pair (value175 w) (value176 w) := by
  ext <;> simp only [value175,value176,pow_two,QuadraticAlgebra.re_add,
    QuadraticAlgebra.im_add,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,pair]
  all_goals ring

lemma step10 (w : Assignment) :
    (pair (value175 w) (value176 w))^2+
      pair (w 156) 0*pair (w 127) (2*w 128)=pair (value177 w) (value178 w) := by
  ext <;> simp only [value177,value178,pow_two,QuadraticAlgebra.re_add,
    QuadraticAlgebra.im_add,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,pair]
  all_goals ring

lemma step11 (w : Assignment) :
    (pair (value177 w) (value178 w))^2+
      pair (w 158) 0*pair (w 129) (2*w 130)=pair (value179 w) (value180 w) := by
  ext <;> simp only [value179,value180,pow_two,QuadraticAlgebra.re_add,
    QuadraticAlgebra.im_add,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,pair]
  all_goals ring

lemma step12 (w : Assignment) :
    (pair (value179 w) (value180 w))^2+
      pair (w 158) 0*pair (w 131) (2*w 132)=pair (value181 w) (value182 w) := by
  ext <;> simp only [value181,value182,pow_two,QuadraticAlgebra.re_add,
    QuadraticAlgebra.im_add,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,pair]
  all_goals ring

lemma step13 (w : Assignment) :
    (pair (value181 w) (value182 w))^2+
      pair (w 158) 0*pair (w 133) (2*w 134)=pair (value183 w) (value184 w) := by
  ext <;> simp only [value183,value184,pow_two,QuadraticAlgebra.re_add,
    QuadraticAlgebra.im_add,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,pair]
  all_goals ring

lemma step14 (w : Assignment) :
    (pair (value183 w) (value184 w))^2+
      pair (w 156) 0*pair (110885832*w 0-7446*w 102+110885832*w 118+221771664*w 135+13860729) (-7446*w 103-29784*w 136)=pair (value185 w) (value186 w) := by
  ext <;> simp only [value185,value186,pow_two,QuadraticAlgebra.re_add,
    QuadraticAlgebra.im_add,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,pair]
  all_goals ring

lemma step15 (w : Assignment) :
    (pair (value185 w) (value186 w))^2+
      pair (w 158) 0*pair (-2*w 123+w 137+1) (-4*w 124+4*w 138)=pair (value187 w) (value188 w) := by
  ext <;> simp only [value187,value188,pow_two,QuadraticAlgebra.re_add,
    QuadraticAlgebra.im_add,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,pair]
  all_goals ring

/-- The source's thirty stored gates are exactly this ordered fold. -/
theorem fold_actual (w : Assignment) :
    (leaves w).foldl (fun x p => x^2+p.1*p.2) 1=chain w := by
  change (leaves w).foldl (fun x p => x^2+p.1*p.2) (pair 1 0)=_
  simp only [leaves,List.foldl_cons,List.foldl_nil,chain,step0,step1,step2,step3,step4,step5,step6,step7,step8,step9,step10,step11,step12,step13,step14,step15]

/-- Positive weighted-leaf depths now apply to the actual output pair. -/
theorem near_one (v : AddValuation K (WithTop ℤ)) (w : Assignment)
    (h : ∀ a∈leaves w, 0<v (a.1*a.2)) : 0<v (chain w-1) := by
  rw [←fold_actual]
  exact NormChainCompleteness.fold_near_one v _ 1 (by simp) h

/-- Opposite-place parity is consumed for the same literal chain. -/
theorem good (v : AddValuation K (WithTop ℤ)) (w : Assignment)
    (h : ∀ a∈leaves w, ValuationEvenNormChain.OddAt v a.1 ∧
      ValuationEvenNormChain.EvenAt v a.2) : NormChainCompleteness.Good v (chain w) := by
  rw [←fold_actual]
  exact NormChainCompleteness.actual_chain_good v _ h

lemma scaled_actual (w : Assignment) (c t : ℚ) :
    chain (ScaledDetectorChain318.view w c t)=
      pair (ScaledDetectorChain318.realChain w c t) (ScaledDetectorChain318.imagChain w c t) := rfl

end ActualDetectorFold318
