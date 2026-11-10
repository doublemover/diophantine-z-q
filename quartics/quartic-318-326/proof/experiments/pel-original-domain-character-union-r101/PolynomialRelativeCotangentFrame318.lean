module
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.Tactic
public section
noncomputable section
namespace PolynomialRelativeCotangentFrame318
open Polynomial KaehlerDifferential
open scoped TensorProduct
variable {R S:Type*} [CommRing R] [CommRing S]
  [Algebra R S] [Algebra R[X] S] [IsScalarTower R R[X] S]
variable (e:KaehlerDifferential R S≃ₗ[S]S)
@[expose] def coefficient:S:=e (D R S (algebraMap R[X] S X))
@[expose] def quotientMap:S→ₗ[S]KaehlerDifferential R[X] S:=
  (KaehlerDifferential.map R R[X] S S).comp e.symm.toLinearMap
lemma quotient_surjective:Function.Surjective (quotientMap e):=
  (KaehlerDifferential.map_surjective R R[X] S).comp e.symm.surjective
lemma polynomial_map (ω:KaehlerDifferential R R[X]):
    e (KaehlerDifferential.map R R R[X] S ω)=
      algebraMap R[X] S (KaehlerDifferential.polynomialEquiv R ω)*coefficient e:=by
  have h:ω=(KaehlerDifferential.polynomialEquiv R ω) • D R R[X] X:=by
    rw [←KaehlerDifferential.polynomialEquiv_symm]
    exact ((KaehlerDifferential.polynomialEquiv R).symm_apply_apply ω).symm
  conv_lhs => rw [h]
  rw [map_smul,←IsScalarTower.algebraMap_smul S,map_smul,
    KaehlerDifferential.map_D,smul_eq_mul]
  rfl
lemma tensor_image_mem (x:S⊗[R[X]]KaehlerDifferential R R[X]):
    e (KaehlerDifferential.mapBaseChange R R[X] S x)∈
      (Ideal.span {coefficient e}:Ideal S):=by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy=>simpa only [map_add] using (Ideal.span {coefficient e}).add_mem hx hy
  | tmul s ω=>
    rw [KaehlerDifferential.mapBaseChange_tmul,map_smul,polynomial_map,smul_eq_mul]
    exact (Ideal.span {coefficient e}).mul_mem_left _
      ((Ideal.span {coefficient e}).mul_mem_left _ (Ideal.subset_span (Set.mem_singleton _)))
/-- The true relative cotangent map has this exact kernel, derived from
the actual transitivity sequence, not just the square relation. -/
theorem kernel:LinearMap.ker (quotientMap e)=(Ideal.span {coefficient e}:Ideal S):=by
  ext x
  constructor
  · intro hx
    have hx':e.symm x∈LinearMap.ker (KaehlerDifferential.map R R[X] S S):=hx
    rw [←KaehlerDifferential.range_mapBaseChange R R[X] S] at hx'
    obtain ⟨y,hy⟩:=hx'
    have h:=tensor_image_mem e y
    simpa only [hy,LinearEquiv.apply_symm_apply] using h
  · intro hx
    have h0:quotientMap e (coefficient e)=0:=by
      change KaehlerDifferential.map R R[X] S S
        (e.symm (e (D R S (algebraMap R[X] S X))))=0
      rw [LinearEquiv.symm_apply_apply,KaehlerDifferential.map_D]
      simpa only [Algebra.algebraMap_self] using
        (D R[X] S).map_algebraMap X
    have hi:(Ideal.span {coefficient e}:Ideal S)≤LinearMap.ker (quotientMap e):=
      Ideal.span_le.mpr (by intro y hy;rcases Set.mem_singleton_iff.mp hy with rfl;exact h0)
    exact hi hx

/-- Exact annihilator criterion for the ACTUAL relative Kähler module.
It is cyclic with relation coefficient·dz=0, so no larger annihilator
or unproved tame-different conversion is silently introduced. -/
theorem annihilator_iff (a:S):
    (∀ω:KaehlerDifferential R[X] S,a • ω=0)↔a∈(Ideal.span {coefficient e}:Ideal S):=by
  constructor
  · intro h
    have ha:quotientMap e a=0:=by
      calc
        quotientMap e a=quotientMap e (a • (1:S)):=by rw [smul_eq_mul,mul_one]
        _=a • quotientMap e 1:=map_smul (quotientMap e) a 1
        _=0:=h (quotientMap e 1)
    change a∈LinearMap.ker (quotientMap e) at ha
    rwa [kernel] at ha
  · intro ha ω
    have hq:quotientMap e a=0:=by
      change a∈LinearMap.ker (quotientMap e)
      rwa [kernel]
    obtain ⟨x,rfl⟩:=quotient_surjective e ω
    calc
      a • quotientMap e x=quotientMap e (a*x):=(map_smul (quotientMap e) a x).symm
      _=quotientMap e (x*a):=by rw [mul_comm a x]
      _=x • quotientMap e a:=map_smul (quotientMap e) x a
      _=0:=by rw [hq,smul_zero]
end PolynomialRelativeCotangentFrame318
