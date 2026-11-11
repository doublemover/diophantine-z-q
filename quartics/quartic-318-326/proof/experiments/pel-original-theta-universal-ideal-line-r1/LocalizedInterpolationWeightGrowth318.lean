module
public import LocalizedRootWeightBounds318
public import LocalizedRootInterpolation318
public section
noncomputable section
namespace LocalizedInterpolationWeightGrowth318
open Polynomial PolynomialWeightBounds318
open LocalizedPrimitiveSelectedPolynomial318 LocalizedPrimitiveSelectedGraphs318
variable {ι : Type*} [Fintype ι]
variable (d : MvPolynomial ι ℂ) (Q : Polynomial (Localization.Away d))

lemma root_bound (hm : Q.Monic) :
    Bounded (fun q : OpenRoots d Q => PrincipalOpenWeight318.weight d q.val.val.1)
      (fun q => ‖q.val.val.2‖) := by
  apply LocalizedRootWeightBounds318.root d (fun q : OpenRoots d Q => q.val.val.1)
    (fun q => q.property) Q hm (fun q => q.val.val.2)
  intro q
  exact (LocalizedPrimitiveRootChart318.equation_on_open d Q _ q.property _).symm.trans q.val.property

/-- Every coefficient of the canonical ALL-root interpolation has a
single weighted bound. The fixed Bezout polynomial controls every inverse
derivative, including arbitrarily close roots. -/
theorem coefficients (hm : Q.Monic) (hs : Q.Separable) (F : OpenRoots d Q → ℂ)
    (hF : Bounded (fun q : OpenRoots d Q => PrincipalOpenWeight318.weight d q.val.val.1)
      (fun q => ‖F q‖)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ v : ι → ℂ,
      ∀ hv : MvPolynomial.eval v d ≠ 0, ∀ n : ℕ,
      ‖(LocalizedRootInterpolation318.polynomial d Q hm F v).coeff n‖ ≤
        C*PrincipalOpenWeight318.weight d v^N := by
  classical
  obtain ⟨A,B,hAB⟩ := (Polynomial.separable_def' Q).mp hs
  have hr := root_bound d Q hm
  have hB := LocalizedRootWeightBounds318.polynomial d
    (fun q : OpenRoots d Q => q.val.val.1) (fun q => q.property) B
    (fun q => q.val.val.2) hr
  obtain ⟨Cr,hCr,Nr,hr⟩ := hr
  obtain ⟨Cf,hCf,Nf,hF⟩ := hF
  obtain ⟨Cb,hCb,Nb,hB⟩ := hB
  let W := PrincipalOpenWeight318.weight d
  have hW (v : ι → ℂ) : 1 ≤ W v := PrincipalOpenWeight318.one_le d v
  have hW0 (v : ι → ℂ) : 0 ≤ W v := zero_le_one.trans (hW v)
  have hrad : Bounded W (fun v => 1+(1+Cr*W v^Nr)) :=
    add hW (const 1) (add hW (const 1) ⟨Cr,hCr,Nr,fun _ => le_rfl⟩)
  have hvalues : Bounded W (fun v => (Cf*W v^Nf)*(Cb*W v^Nb)) :=
    mul hW0 ⟨Cf,hCf,Nf,fun _ => le_rfl⟩ ⟨Cb,hCb,Nb,fun _ => le_rfl⟩
      (fun v => mul_nonneg hCb (pow_nonneg (hW0 v) _))
  have hrad0 (v : ι → ℂ) : 0 ≤ 1+(1+Cr*W v^Nr) := by
    have hv := hW0 v
    positivity
  have hupper : Bounded W (fun v => (Q.natDegree : ℝ) *
      ((Cf*W v^Nf)*(Cb*W v^Nb)*(1+(1+Cr*W v^Nr))^Q.natDegree)) :=
    mul hW0 (const Q.natDegree)
      (mul hW0 hvalues (pow hW0 hrad hrad0 Q.natDegree)
        (fun v => pow_nonneg (hrad0 v) _))
      (fun v => by have hv := hW0 v; positivity)
  obtain ⟨C,hC,N,hupper⟩ := hupper
  refine ⟨C,hC,N,?_⟩
  intro v hv n
  have hWv := hW0 v
  let ev := ComplexPolynomialOpenPoints318.evaluation d v hv
  let T := allRoots d Q hm v hv
  let a := fun r => F (point d Q v hv r)
  have hnodal : Lagrange.nodal T Subtype.val = Q.map ev :=
    LocalizedSelectedComplementProduct318.all_root_product d Q hm hs v hv
  have hab : A.map ev*Q.map ev+B.map ev*(Q.map ev).derivative=1 := by
    simpa only [Polynomial.map_add,Polynomial.map_mul,Polynomial.map_one,
      Polynomial.derivative_map] using congrArg (Polynomial.map ev) hAB
  have hcard : T.card = Q.natDegree := LocalizedRootInterpolation318.allRoots_card d Q hm hs v hv
  have hestimate := LagrangeBezoutWeights318.coefficient_bound T Subtype.val a
    (Q.map ev) (A.map ev) (B.map ev) hnodal hab
    1 (1+Cr*W v^Nr) (Cf*W v^Nf) (Cb*W v^Nb)
    zero_le_one (by positivity) (by positivity) (by positivity)
    (fun r _ => by simpa only [one_mul] using add_le_add_left (hr (point d Q v hv r)) 1)
    (fun r _ => hF (point d Q v hv r))
    (fun r _ => by simpa only [Polynomial.eval_map] using hB (point d Q v hv r)) n
  rw [LocalizedRootInterpolation318.on_open d Q hm F v hv]
  change ‖(Lagrange.interpolate T Subtype.val a).coeff n‖ ≤ _
  apply le_trans _ (hupper v)
  simpa only [one_pow,one_mul,hcard]
    using hestimate

/-- Uniform pole exponents for ALL coefficients, not just a finite list
selected after interpolation. -/
theorem pole_coefficients (hm : Q.Monic) (hs : Q.Separable) (F : OpenRoots d Q → ℂ)
    (hF : Bounded (fun q : OpenRoots d Q => PrincipalOpenWeight318.weight d q.val.val.1)
      (fun q => ‖F q‖)) :
    ∃ M N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ι → ℂ,
      ∀ hv : MvPolynomial.eval v d ≠ 0, ∀ n : ℕ,
      ‖MvPolynomial.eval v d ^ M *
        (LocalizedRootInterpolation318.polynomial d Q hm F v).coeff n‖ ≤ C*(1+‖v‖)^N := by
  obtain ⟨C,hC,N,h⟩ := coefficients d Q hm hs F hF
  let X := {v : ι → ℂ // MvPolynomial.eval v d ≠ 0} × ℕ
  have hb (x : X) := x.1.property
  have hf : Bounded (fun x : X => PrincipalOpenWeight318.weight d x.1.val)
      (fun x => ‖(LocalizedRootInterpolation318.polynomial d Q hm F x.1.val).coeff x.2‖) :=
    ⟨C,hC,N,fun x => h x.1.val x.1.property x.2⟩
  obtain ⟨M,K,D,hD,hh⟩ := PrincipalOpenWeight318.pole_growth d (fun x : X => x.1.val) hb _ hf
  refine ⟨M,K,D,hD,?_⟩
  intro v hv n
  simpa only [norm_mul,norm_pow] using hh (⟨v,hv⟩,n)
end LocalizedInterpolationWeightGrowth318
