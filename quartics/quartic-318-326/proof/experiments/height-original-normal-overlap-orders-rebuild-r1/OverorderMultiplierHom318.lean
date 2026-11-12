module
public import FiniteOrderConductorTraceDual318
public section
noncomputable section
namespace OverorderMultiplierHom318
variable {A N B : Type*} [CommRing A] [CommRing N] [CommRing B]
  [Algebra A N] [Algebra A B] (j : N →ₐ[A] B)

/-- Multipliers landing in the literal raw-order image for EVERY
normal-order element, without a field-rank identification. -/
def Multipliers := {z : B // ∀ n : N,∃ a : A,algebraMap A B a=z*j n}

variable (hi : Function.Injective (algebraMap A B))

@[expose] def preimage (z : Multipliers j) (n : N) : A := Classical.choose (z.property n)
lemma preimage_spec (z : Multipliers j) (n : N) :
    algebraMap A B (preimage j z n)=z.val*j n := Classical.choose_spec (z.property n)

/-- Every conductor multiplier gives a full raw-order-linear map. -/
@[expose] def toHom (z : Multipliers j) : N →ₗ[A] A where
  toFun := preimage j z
  map_add' x y := by
    apply hi
    rw [map_add,preimage_spec,preimage_spec,preimage_spec,map_add,mul_add]
  map_smul' a n := by
    apply hi
    change algebraMap A B (preimage j z (a • n))=
      algebraMap A B (a*preimage j z n)
    rw [preimage_spec,map_mul,preimage_spec,map_smul,Algebra.smul_def]
    ring

variable (hj : Function.Injective j) (d : A)
  (hu : IsUnit (algebraMap A B d))
  (hd : ∀ n : N,∃ a : A,algebraMap A B a=algebraMap A B d*j n)

include hj hu hd in
/-- The produced common conductor denominator forces EVERY actual
raw-order-linear functional to be multiplication by its value at1. -/
theorem hom_value (f : N →ₗ[A] A) (n : N) :
    algebraMap A B (f n)=algebraMap A B (f 1)*j n := by
  obtain ⟨a,ha⟩ := hd n
  have hn : d • n=a • (1:N) := by
    apply hj
    simpa only [map_smul,map_one,Algebra.smul_def,mul_one] using ha.symm
  have hf := congrArg f hn
  rw [map_smul,map_smul] at hf
  change d*f n=a*f 1 at hf
  have hb := congrArg (algebraMap A B) hf
  simp only [map_mul,ha] at hb
  apply hu.mul_left_cancel
  calc
    _ = (algebraMap A B d*j n)*algebraMap A B (f 1) := hb
    _ = _ := by ring

@[expose] def fromHom (f : N →ₗ[A] A) : Multipliers j :=
  ⟨algebraMap A B (f 1),fun n => ⟨f n,hom_value j hj d hu hd f n⟩⟩

/-- Entire Hom-set identification, not just an injection or one
chosen functional. Both inverse laws retain literal ambient values. -/
@[expose] def equivalence : Multipliers j ≃ (N →ₗ[A] A) where
  toFun := toHom j hi
  invFun := fromHom j hj d hu hd
  left_inv z := by
    apply Subtype.ext
    change algebraMap A B (preimage j z 1)=z.val
    simpa only [map_one,mul_one] using preimage_spec j z (1:N)
  right_inv f := by
    apply LinearMap.ext
    intro n
    apply hi
    exact (preimage_spec j (fromHom j hj d hu hd f) n).trans
      (hom_value j hj d hu hd f n).symm
end OverorderMultiplierHom318
