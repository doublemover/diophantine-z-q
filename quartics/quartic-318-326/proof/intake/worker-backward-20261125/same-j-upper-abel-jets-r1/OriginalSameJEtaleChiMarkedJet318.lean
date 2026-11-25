module
public import OriginalSameJRetainedAffineJet318

@[expose] public section
noncomputable section

open Algebra Polynomial

namespace OriginalSameJEtaleChiMarkedJet318
open OriginalSameJRetainedAffineJet318

variable {k A : Type*} [Field k] [CommRing A]
  [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A]
variable (a v : k)

abbrev residueAlgebra : Algebra k[X] k := (namedResidue a).toRingHom.toAlgebra
abbrev jetAlgebra : Algebra k[X] (Jet k) := (namedBase a v).toRingHom.toAlgebra

theorem jet_tower :
    letI : Algebra k[X] (Jet k) := jetAlgebra a v
    IsScalarTower k k[X] (Jet k) := by
  let : Algebra k[X] (Jet k) := jetAlgebra a v
  exact IsScalarTower.of_algebraMap_eq fun c => ((namedBase a v).commutes c).symm

variable (e : A →ₐ[k] k)
variable (he : e.toRingHom.comp (algebraMap k[X] A) = (namedResidue a).toRingHom)

def overResidue :
    letI : Algebra k[X] k := residueAlgebra a
    A →ₐ[k[X]] k := by
  let : Algebra k[X] k := residueAlgebra a
  exact { e.toRingHom with commutes' := fun p => RingHom.congr_fun he p }

variable [Algebra.FormallyEtale k[X] A]

/-- The only lift used below is the full retained point, with X mapped
to a + vε. The two P¹ affine functions stay in the original A. -/
def originalJet : A →ₐ[k] Jet k := by
  let : Algebra k[X] k := residueAlgebra a
  let : Algebra k[X] (Jet k) := jetAlgebra a v
  let l : A →ₐ[k[X]] Jet k := lift (base_specializes a v) (overResidue a e he)
  refine { l.toRingHom with commutes' := fun c => ?_ }
  have hA : algebraMap k A c = algebraMap k[X] A (algebraMap k k[X] c) :=
    RingHom.congr_fun (IsScalarTower.algebraMap_eq k k[X] A) c
  change l (algebraMap k A c) = algebraMap k (Jet k) c
  rw [hA]
  exact (l.commutes (algebraMap k k[X] c)).trans ((namedBase a v).commutes c)

abbrev chi : A := algebraMap k[X] A (Polynomial.X : k[X])

theorem original_specializes (x : A) :
    proj ((originalJet a v e he) x) = e x := by
  let : Algebra k[X] k := residueAlgebra a
  let : Algebra k[X] (Jet k) := jetAlgebra a v
  have h := AlgHom.congr_fun (specializes (base_specializes a v) (overResidue a e he)) x
  exact h

theorem original_chi :
    originalJet a v e he (chi (k:=k) (A:=A)) = ((a,v) : Jet k) := by
  let : Algebra k[X] k := residueAlgebra a
  let : Algebra k[X] (Jet k) := jetAlgebra a v
  exact ((lift (base_specializes a v) (overResidue a e he)).commutes (Polynomial.X : k[X])).trans
    (namedBase_X a v)

/-- Equality with any genuine evaluation first jet. Knowing just its
base coordinate and that its entire residue is e suffices; no
re-identification by a scalar value alone. -/
theorem unique_from_actual_chart (j : A →ₐ[k] Jet k)
    (hfull : ∀ x, proj (j x) = e x)
    (hχ : j (chi (k:=k) (A:=A)) = ((a,v) : Jet k)) :
    j = originalJet a v e he := by
  let : Algebra k[X] k := residueAlgebra a
  let : Algebra k[X] (Jet k) := jetAlgebra a v
  have hbase : j.comp (IsScalarTower.toAlgHom k (k[X]) A) = namedBase a v :=
    Polynomial.algHom_ext (hχ.trans (namedBase_X a v).symm)
  let g : A →ₐ[k[X]] Jet k :=
    { j.toRingHom with commutes' := fun p => AlgHom.congr_fun hbase p }
  have hs : (projection (base_specializes a v)).comp g = overResidue a e he :=
    AlgHom.ext hfull
  have hg : g = lift (base_specializes a v) (overResidue a e he) :=
    unique_lift (base_specializes a v) (overResidue a e he) g hs
  exact AlgHom.ext fun x => AlgHom.congr_fun hg x

theorem true_reciprocal (π : A) (hπ : chi (k:=k) (A:=A) * π = 1) (ha : a ≠ 0) :
    (originalJet a v e he π).fst = a⁻¹ ∧
      (originalJet a v e he π).snd = -(a⁻¹ * v * a⁻¹) :=
  reciprocal_read (originalJet a v e he) (chi (k:=k) (A:=A)) π hπ a v ha
    (original_chi a v e he)

end OriginalSameJEtaleChiMarkedJet318

#print axioms OriginalSameJEtaleChiMarkedJet318.original_specializes
#print axioms OriginalSameJEtaleChiMarkedJet318.original_chi
#print axioms OriginalSameJEtaleChiMarkedJet318.unique_from_actual_chart
#print axioms OriginalSameJEtaleChiMarkedJet318.true_reciprocal
