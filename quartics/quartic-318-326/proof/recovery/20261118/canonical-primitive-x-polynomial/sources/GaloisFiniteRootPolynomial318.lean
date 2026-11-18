module
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.Tactic
public section
noncomputable section
namespace GaloisFiniteRootPolynomial318
open Polynomial
variable {k L:Type*} [Field k] [Field L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
variable (s:Finset L) (stable:∀ (g:L≃ₐ[k]L) a,a∈s→g a∈s)

/-- Rational descent of the monic squarefree polynomial of a stable,
finite set of DISTINCT geometric coordinates. -/
theorem exists_base :
    ∃q:Polynomial k, q.map (algebraMap k L)=∏a∈s,(X-C a) := by
  classical
  let p : Polynomial L := ∏a∈s,(X-C a)
  have hmap (g:L≃ₐ[k]L) : p.map g.toRingEquiv.toRingHom=p := by
    have hg : s.image (fun a=>g a)=s := by
      ext a
      constructor
      · rintro ha
        obtain ⟨b,hb,rfl⟩:=Finset.mem_image.mp ha
        exact stable g b hb
      · intro ha
        exact Finset.mem_image.mpr ⟨g.symm a,stable g.symm a ha,g.apply_symm_apply a⟩
    calc
      _ = ∏a∈s,(X-C (g a)) := by simp [p,Polynomial.map_prod]
      _ = ∏a∈s.image (fun a=>g a),(X-C a) :=
        (Finset.prod_image (fun _ _ _ _ h=>g.injective h)).symm
      _ = p := by rw [hg]
  apply (Polynomial.mem_lifts p).mp
  apply (Polynomial.lifts_iff_coeff_lifts p).mpr
  intro n
  apply (IsGalois.mem_range_algebraMap_iff_fixed _).mpr
  intro g
  simpa only [Polynomial.coeff_map] using congrArg (fun z:Polynomial L=>z.coeff n) (hmap g)

def poly : Polynomial k := (exists_base s stable).choose
theorem map_poly :
    (poly s stable).map (algebraMap k L)=∏a∈s,(X-C a) := (exists_base s stable).choose_spec
theorem monic : (poly s stable).Monic := by
  apply (algebraMap k L).injective.monic_map_iff.mpr
  rw [map_poly]
  exact monic_prod_X_sub_C id s
theorem roots : ((poly s stable).map (algebraMap k L)).roots=s.val := by
  rw [map_poly,roots_prod_X_sub_C]
theorem degree : (poly s stable).natDegree=s.card := by
  rw [←Polynomial.natDegree_map_eq_of_injective (algebraMap k L).injective,map_poly]
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun a _=>monic_X_sub_C a)]
  simp
theorem separable : (poly s stable).Separable := by
  have hd : ((poly s stable).map (algebraMap k L)).natDegree=s.card := by
    rw [Polynomial.natDegree_map_eq_of_injective (algebraMap k L).injective,degree]
  have hs : ((poly s stable).map (algebraMap k L)).Splits := by
    apply Polynomial.splits_iff_card_roots.mpr
    rw [roots,hd] <;> rfl
  apply (Polynomial.separable_map (algebraMap k L)).mp
  apply (Polynomial.nodup_roots_iff_of_splits ((monic s stable).map _).ne_zero hs).mp
  rw [roots]
  exact s.nodup
theorem zero_iff (a:L) :
    Polynomial.aeval a (poly s stable)=0 ↔ a∈s := by
  rw [Polynomial.aeval_def,←Polynomial.mem_roots_map_of_injective
    (algebraMap k L).injective (monic s stable).ne_zero,roots] <;> rfl
end GaloisFiniteRootPolynomial318
