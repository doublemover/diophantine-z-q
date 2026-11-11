module
public import PELOriginalAutomorphicFourierRecurrence318
public import PELOriginalLevelThetaIndependence318
public section
noncomputable section
namespace PELOriginalAutomorphicSubspace318
open QuaternionicRealPeriod318 PELOriginalThetaConvergence318 PELOriginalLevelTheta318
open PELOriginalAutomorphicFourierRecurrence318
variable (τ:ℂ) (N:ℕ)
lemma zero_automorphic:Automorphic τ N (0:ComplexVectors→ℂ):=by
  refine ⟨differentiable_const _,?_,?_⟩ <;> intros <;> simp
lemma add_automorphic {f g:ComplexVectors→ℂ}(hf:Automorphic τ N f)(hg:Automorphic τ N g):
    Automorphic τ N (f+g):=by
  refine ⟨hf.entire.add hg.entire,?_,?_⟩
  · intro m z;simp only [Pi.add_apply,hf.integer,hg.integer]
  · intro b z;simp only [Pi.add_apply,hf.period,hg.period,mul_add]
lemma smul_automorphic(c:ℂ){f:ComplexVectors→ℂ}(hf:Automorphic τ N f):
    Automorphic τ N (c • f):=by
  refine ⟨hf.entire.const_smul c,?_,?_⟩
  · intro m z;simp only [Pi.smul_apply,hf.integer]
  · intro b z;simp only [Pi.smul_apply,smul_eq_mul,hf.period];ring
lemma sub_automorphic {f g:ComplexVectors→ℂ}(hf:Automorphic τ N f)(hg:Automorphic τ N g):
    Automorphic τ N (f-g):=by
  simpa only [neg_one_smul,sub_eq_add_neg] using
    add_automorphic τ N hf (smul_automorphic τ N (-1) hg)
@[expose] def space:Submodule ℂ (ComplexVectors→ℂ) where
  carrier:=Automorphic τ N
  zero_mem':=zero_automorphic τ N
  add_mem':=add_automorphic τ N
  smul_mem':=smul_automorphic τ N
lemma finite_sum {ι:Type*}(s:Finset ι)(f:ι→ComplexVectors→ℂ)
    (hf:∀i∈s,Automorphic τ N (f i)):
    Automorphic τ N (fun z=>∑i∈s,f i z):=by
  classical
  simpa only [Finset.sum_apply] using (space τ N).sum_mem hf

variable [NeZero N]
/-- Every integer frequency lies in the full original N-lattice coset
of its chosen residue representative. No parity/index factor discarded. -/
lemma frequency_decomposition(k:Index):
    ∃b:Index,k=PELOriginalLevelThetaIndependence318.representative N (residue N k)+shift N b:=by
  let r:=PELOriginalLevelThetaIndependence318.representative N (residue N k)
  have hr:=PELOriginalLevelThetaIndependence318.residue_representative N (residue N k)
  have h0:((r.1:ℤ):ZMod N)=(k.1:ZMod N):=congrArg Prod.fst hr
  have h1:((r.2:ℤ):ZMod N)=(k.2:ZMod N):=congrArg Prod.snd hr
  obtain ⟨b0,hb0⟩:∃b0:ℤ,k.1-r.1=(N:ℤ)*b0:=
    (ZMod.intCast_eq_intCast_iff_dvd_sub r.1 k.1 N).mp h0
  obtain ⟨b1,hb1⟩:∃b1:ℤ,k.2-r.2=(N:ℤ)*b1:=
    (ZMod.intCast_eq_intCast_iff_dvd_sub r.2 k.2 N).mp h1
  refine ⟨(b0,b1),?_⟩
  apply Prod.ext
  · change k.1=r.1+(N:ℤ)*b0
    linarith
  · change k.2=r.2+(N:ℤ)*b1
    linarith
lemma coefficients_zero_of_representatives {f:ComplexVectors→ℂ}(hf:Automorphic τ N f)
    (hr:∀r:Label N,EntireDoubleFourierTranslation318.coefficient f
      (PELOriginalLevelThetaIndependence318.representative N r)=0):
    ∀k:Index,EntireDoubleFourierTranslation318.coefficient f k=0:=by
  intro k
  obtain ⟨b,hb⟩:=frequency_decomposition N k
  have h:=full_recurrence τ N hf b
    (PELOriginalLevelThetaIndependence318.representative N (residue N k))
  rw [←hb,hr,mul_zero] at h
  exact (mul_eq_zero.mp h).resolve_left (Complex.exp_ne_zero _)
end PELOriginalAutomorphicSubspace318
