module
public import ArithmeticBranchRepresentatives318
public section
noncomputable section
namespace IrreducibleUniformPrimitiveEquation318
open Polynomial UpperHalfPlane OpenJComplexEvaluation318 TranscendentalJGenericFiber318
open AnalyticTranscendentalBranchDomain318 ArithmeticPrimitiveOrbit318
open UniformTranscendentalPrimitiveEquation318 ArithmeticBranchRepresentatives318
variable (N:ℕ) [NeZero N]

abbrev rootsSpec (Q:Polynomial (K N)) := ∀(τ:UpperHalfPlane) (h:Admissible τ)
    (ht:Transcendental ℤ (ActualQJ318.jInvariant τ)) (z:ℂ),
    Q.eval₂ (embedding N τ h ht) z=0 ↔ ∃P:ArithmeticMarks N τ h,valueX P.val=z

private theorem standard_root (Q:Polynomial (K N)) (spec:rootsSpec N Q) (p:T) :
    Q.eval₂ (E N p) (branch N p.val)=0 := by
  let e := OpenJAnalyticPoints318.pointAddEquiv N p.val p.property.1
  let P := MarkedPeriod318.standardPoint N p.val
  apply (spec p.val p.property.1 p.property.2 _).mpr
  exact ⟨⟨e.symm P,(addOrderOf_injective e.symm.toAddMonoidHom e.symm.injective P).trans
    (MarkedPeriod318.standardPoint_order N p.val)⟩,
    ArithmeticStandardPeriodX318.inverse_x N p.val p.property.1 P⟩

/-- Coprimality forbids a nonunit complementary factor as soon as every
root of that factor at ONE injective complex embedding is a root of f.
No unseen assertion about splitting fields or equality of degrees. -/
private theorem other_unit {k:Type*} [Field k] (e:k→+*ℂ) (f g:Polynomial k)
    (hc:IsCoprime f g) (hcovers:∀z:ℂ,g.eval₂ e z=0→f.eval₂ e z=0) : IsUnit g := by
  by_contra hn
  obtain ⟨z,hz⟩ := IsAlgClosed.exists_eval₂_eq_zero e g
    (fun he=>hn (Polynomial.isUnit_iff_degree_eq_zero.mpr he))
  obtain ⟨a,b,hab⟩ := hc
  have h := congrArg (Polynomial.eval₂RingHom e z) hab
  have hf := hcovers z hz
  simp only [map_add,map_mul,map_one] at h
  change a.eval₂ e z*f.eval₂ e z+b.eval₂ e z*g.eval₂ e z=1 at h
  simpa [hf,hz] using h

/-- Every uniform, separable primitive-coordinate equation on the actual
arithmetic family is irreducible, including level 2. Factors are first
separated globally along the standard branch, then transported to all
roots at a single fixed arithmetic reference period by genuine SL₂(Z)
transport. No transitive Galois action, degree equality, or presumed
identification with a named modular function field is an input. -/
theorem irreducible (hN:1<N) (Q:Polynomial (K N)) (hs:Q.Separable)
    (spec:rootsSpec N Q) : Irreducible Q := by
  obtain ⟨τ,_,ha,ht⟩ := exists_period 0
  let p:T := ⟨τ,ha,ht⟩
  constructor
  · intro hu
    have hh := hu.map (Polynomial.eval₂RingHom (E N p) (branch N τ))
    apply hh.ne_zero
    exact standard_root N Q spec p
  · intro f g he
    have hc : IsCoprime f g := (he ▸ hs).isCoprime
    have hzero (s:T) : f.eval₂ (E N s) (branch N s.val)*g.eval₂ (E N s) (branch N s.val)=0 := by
      simpa only [he,Polynomial.eval₂_mul] using standard_root N Q spec s
    have transfer (a:Polynomial (K N))
        (hvan:∀s:T,a.eval₂ (E N s) (branch N s.val)=0) :
        ∀z:ℂ,Q.eval₂ (E N p) z=0→a.eval₂ (E N p) z=0 := by
      intro z hz
      obtain ⟨P,rfl⟩ := (spec τ ha ht z).mp hz
      exact specialize_all N a (fun σ h t=>hvan ⟨σ,h,t⟩) τ ha ht P
    rcases rep_split (rep_specialize N hN f) (rep_specialize N hN g) hzero with hf|hg
    · exact Or.inr (other_unit (E N p) f g hc (fun z hz=>transfer f hf z (by
        simp only [he,Polynomial.eval₂_mul,hz,mul_zero])))
    · exact Or.inl (other_unit (E N p) g f hc.symm (fun z hz=>transfer g hg z (by
        simp only [he,Polynomial.eval₂_mul,hz,zero_mul])))

/-- Unconditional existence of the actual irreducible primitive x-equation
on the generic arithmetic j-line, with its uniform complex root spec. -/
theorem exists_equation (hN:1<N) : ∃Q:Polynomial (K N),
    Q.Monic ∧ Q.Separable ∧ Irreducible Q ∧ rootsSpec N Q := by
  obtain ⟨Q,hm,hs,spec⟩ := uniform N hN
  exact ⟨Q,hm,hs,irreducible N hN Q hs spec,spec⟩

end IrreducibleUniformPrimitiveEquation318
