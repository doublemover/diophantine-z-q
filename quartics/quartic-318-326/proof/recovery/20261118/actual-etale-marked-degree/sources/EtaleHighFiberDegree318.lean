module
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Tactic
public section
noncomputable section
namespace EtaleHighFiberDegree318
open scoped TensorProduct Polynomial
open Polynomial

/-- A prescribed nonempty principal open of the affine j-line contains a
complex point of arbitrarily large norm, including after excluding every
root of the discriminant and all other finitely many bad values. -/
theorem arbitrarily_high (f : ℂ[X]) (hf : f≠0) (b : ℝ) :
    ∃ c:ℂ, b<‖c‖ ∧ f.eval c≠0 := by
  classical
  obtain ⟨M,hM⟩ := (f.roots.toFinset.finite_toSet.isCompact).exists_bound_of_continuousOn
    (continuous_id.continuousOn : ContinuousOn (fun x:ℂ => x) _)
  let r := max 0 (max b M)+1
  have hb : b<r := by dsimp [r]; linarith [le_max_left b M,le_max_right 0 (max b M)]
  have hm : M<r := by dsimp [r]; linarith [le_max_right b M,le_max_right 0 (max b M)]
  have hp : 0≤r := by dsimp [r]; linarith [le_max_left 0 (max b M)]
  have hn : ‖(r:ℂ)‖=r := by simp [Real.norm_eq_abs,abs_of_nonneg hp]
  refine ⟨(r:ℂ),by rwa [hn],?_⟩
  intro hz
  have hh : (r:ℂ) ∈ f.roots.toFinset := by simpa using (Polynomial.mem_roots hf).mpr hz
  exact hm.not_ge (by simpa only [hn] using hM _ hh)

abbrev Base (f : ℂ[X]) := Localization.Away f
def evalAlgebra (f : ℂ[X]) (c : ℂ) (hc : f.eval c≠0) : Algebra (Base f) ℂ :=
  (IsLocalization.Away.lift (S:=Base f) (g:=Polynomial.evalRingHom c) f
    (isUnit_iff_ne_zero.mpr hc)).toAlgebra

/-- Actual affine fibre algebra for Spec(A) over a point on D(f). -/
abbrev FiberAlgebra (f : ℂ[X]) (A : Type*) [CommRing A] [Algebra (Base f) A]
    (c : ℂ) (hc : f.eval c≠0) :=
  letI := evalAlgebra f c hc
  ℂ ⊗[Base f] A

/-- Over a separably closed field, the spectrum of a finite étale algebra has
exactly its linear dimension in points, including products and the zero
algebra if it occurs; reducedness/constant rank are not inferred from the
size of an arbitrary nonétale closed fibre. -/
theorem card_spec (k B : Type*) [Field k] [IsSepClosed k] [CommRing B]
    [Algebra k B] [Algebra.Etale k B] [Module.Finite k B] :
    Nat.card (PrimeSpectrum B)=Module.finrank k B := by
  classical
  letI : IsArtinianRing B := IsArtinianRing.of_finite k B
  letI : Fintype (PrimeSpectrum B) := Fintype.ofFinite _
  let e := Algebra.FormallyEtale.equivPiOfIsSepClosed k B
  rw [e.toLinearEquiv.finrank_eq,Module.finrank_fintype_fun_eq_card,Nat.card_eq_fintype_card]

/-- Uniform rank equals actual geometric fibre size after specialization at
any c in the étale chart. The finite free étale chart is an upstream input;
no assumption about the number of fibre points or the modular degree. -/
theorem card_actual (f : ℂ[X]) (A : Type*) [CommRing A] [Algebra (Base f) A]
    [Module.Free (Base f) A] [Module.Finite (Base f) A] [Algebra.Etale (Base f) A]
    (c : ℂ) (hc : f.eval c≠0) :
    Nat.card (PrimeSpectrum (FiberAlgebra f A c hc))=Module.finrank (Base f) A := by
  letI := evalAlgebra f c hc
  letI : Nontrivial (Base f) := RingHom.domain_nontrivial (algebraMap (Base f) ℂ)
  change Nat.card (PrimeSpectrum (ℂ ⊗[Base f] A))=_
  rw [card_spec ℂ _,Module.finrank_baseChange]
end EtaleHighFiberDegree318
