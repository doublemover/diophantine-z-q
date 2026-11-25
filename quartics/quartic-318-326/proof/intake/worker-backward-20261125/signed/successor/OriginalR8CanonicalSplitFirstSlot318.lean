module
public import OriginalR8RepresentedFirstSlotEqualizer318
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.TensorProduct.Maps
public section
noncomputable section

namespace OriginalR8CanonicalSplitFirstSlot318

open scoped TensorProduct
open TensorProduct Algebra.FormallyEtale
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w
variable {F : Type u} {K : Type v} {A B : Type w}
  [Field F] [Field K] [Algebra F K]
  [CommRing A] [CommRing B] [Algebra F A] [Algebra F B]

/-- K-algebra base change of the actual first-slot arrow. -/
@[expose] def lifted (f : A →ₐ[F] B) : (K ⊗[F] A) →ₐ[K] (K ⊗[F] B) :=
  Algebra.TensorProduct.map (AlgHom.id K K) f

theorem lifted_eq_lt (f : A →ₐ[F] B) (z : K ⊗[F] A) :
    lifted (K:=K) f z = f.toLinearMap.lTensor K z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul c a =>
      rw [lifted,Algebra.TensorProduct.map_tmul,LinearMap.lTensor_tmul,AlgHom.id_apply]
  | add x y hx hy =>
      rw [map_add,map_add,hx,hy]

variable [Algebra.EssFiniteType K (K ⊗[F] A)] [Algebra.FormallyEtale K (K ⊗[F] A)]
  [Algebra.EssFiniteType K (K ⊗[F] B)] [Algebra.FormallyEtale K (K ⊗[F] B)] [IsSepClosed K]
variable {G : Type (max v w)} [Fintype G] [DecidableEq G]

/-- Only the geometric orbit criterion on the actual comap remains:
the split algebras, first-slot reads, and frame-action reads come from
canonical finite-étale coordinate naturality, not supplied splittings. -/
theorem canonical_fixed [Module.FaithfullyFlat F K]
    (ι : A →ₐ[F] B) (σ : G → B ≃ₐ[F] B)
    (surj : Function.Surjective (PrimeSpectrum.comap (lifted (K:=K) ι)))
    (constant : ∀ g (p : PrimeSpectrum (K ⊗[F] B)),
      (p.comap (lifted (K:=K) (σ g).toAlgHom)).comap (lifted (K:=K) ι) =
        p.comap (lifted (K:=K) ι))
    (fibre : ∀ p q : PrimeSpectrum (K ⊗[F] B),
      p.comap (lifted (K:=K) ι) = q.comap (lifted (K:=K) ι) →
        ∃ g, p.comap (lifted (K:=K) (σ g).toAlgHom) = q)
    (b : B) :
    (∀ g : G, σ g b = b) ↔ ∃ a : A, ι a = b := by
  letI : SMul G (PrimeSpectrum (K ⊗[F] B)) :=
    ⟨fun g p => p.comap (lifted (K:=K) (σ g).toAlgHom)⟩
  let eA := equivPiOfIsSepClosed K (K ⊗[F] A)
  let eB := equivPiOfIsSepClosed K (K ⊗[F] B)
  refine OriginalR8RepresentedFirstSlotEqualizer318.fixed_iff_in_image ι σ eA eB
    (PrimeSpectrum.comap (lifted (K:=K) ι)) surj constant fibre ?_ ?_ b
  · intro a p
    change eB (ι.toLinearMap.lTensor K a) p = eA a (p.comap (lifted (K:=K) ι))
    rw [← lifted_eq_lt ι]
    exact (equivPiOfIsSepClosed_comap (lifted (K:=K) ι) a p).symm
  · intro g z p
    change eB (((σ g).toLinearMap.lTensor K) z) p =
      eB z (p.comap (lifted (K:=K) (σ g).toAlgHom))
    rw [← lifted_eq_lt (σ g).toAlgHom]
    exact (equivPiOfIsSepClosed_comap (lifted (K:=K) (σ g).toAlgHom) z p).symm

end OriginalR8CanonicalSplitFirstSlot318
#print axioms OriginalR8CanonicalSplitFirstSlot318.lifted_eq_lt
#print axioms OriginalR8CanonicalSplitFirstSlot318.canonical_fixed
