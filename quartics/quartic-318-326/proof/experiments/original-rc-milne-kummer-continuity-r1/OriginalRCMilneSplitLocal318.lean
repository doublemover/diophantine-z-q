module
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Abel

public section

namespace OriginalRCMilneSplitLocal318

variable (G : Type*) [AddCommGroup G]

/-- The ordinary doubling map on the actual local elliptic point
group once the actual split comparison identifies its factors. -/
@[expose] def twice : G →+ G where
  toFun x := x+x
  map_zero' := zero_add _
  map_add' x y := by abel

/-- The oriented product formula for the actual map after splitting
the quadratic field and making the actual twist point identification. -/
@[expose] def sumDifference : G × G →+ G × G where
  toFun z := (z.1+z.2,z.1-z.2)
  map_zero' := Prod.ext (zero_add _) (sub_zero _)
  map_add' z w := Prod.ext (by change (z.1+w.1)+(z.2+w.2) = _; abel)
    (by change (z.1+w.1)-(z.2+w.2) = _; abel)

theorem mem_range_iff (z : G × G) :
    z ∈ (sumDifference G).range ↔ z.1+z.2 ∈ (twice G).range := by
  constructor
  · rintro ⟨v,rfl⟩
    refine ⟨v.1,?_⟩
    change v.1+v.1 = (v.1+v.2)+(v.1-v.2)
    abel
  · rintro ⟨v,hv⟩
    change v+v = z.1+z.2 at hv
    refine ⟨(v,z.1-v),Prod.ext ?_ ?_⟩
    · change v+(z.1-v) = z.1
      abel
    · change v-(z.1-v) = z.2
      calc
        _ = (v+v)-z.1 := by abel
        _ = z.2 := by rw [hv]; abel

private theorem mem_ker_iff (z : G × G) :
    z ∈ (sumDifference G).ker ↔ z.2 = z.1 ∧ z.1 ∈ (twice G).ker := by
  change (z.1+z.2,z.1-z.2) = (0,0) ↔ z.2 = z.1 ∧ z.1+z.1 = 0
  constructor
  · intro h
    have he : z.1-z.2 = 0 := congrArg Prod.snd h
    have hz := (sub_eq_zero.mp he).symm
    exact ⟨hz, by simpa only [hz] using (congrArg Prod.fst h : z.1+z.2=0)⟩
  · rintro ⟨hz,h⟩
    rw [hz]
    exact Prod.ext h (sub_self _)

/-- This is the diagonal **actual 2-torsion**, not an independent
local dimension assumption. -/
def kernelEquiv : (sumDifference G).ker ≃+ (twice G).ker where
  toFun x := ⟨x.val.1,((mem_ker_iff G x.val).mp x.property).2⟩
  invFun x := ⟨(x.val,x.val),(mem_ker_iff G (x.val,x.val)).mpr ⟨rfl,x.property⟩⟩
  left_inv x := Subtype.ext (Prod.ext rfl (((mem_ker_iff G x.val).mp x.property).1.symm))
  right_inv x := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

@[expose] def coordinateSum : G × G →+ G where
  toFun z := z.1+z.2
  map_zero' := zero_add _
  map_add' z w := by change (z.1+w.1)+(z.2+w.2) = _; abel

@[expose] def toDoubleQuotient : G × G →+ G ⧸ (twice G).range :=
  (QuotientAddGroup.mk' (twice G).range).comp (coordinateSum G)

theorem toDoubleQuotient_ker :
    (toDoubleQuotient G).ker = (sumDifference G).range := by
  ext z
  change ((z.1+z.2 : G) : G ⧸ (twice G).range) = 0 ↔
    z ∈ (sumDifference G).range
  exact (QuotientAddGroup.eq_zero_iff (z.1+z.2)).trans (mem_range_iff G z).symm

theorem toDoubleQuotient_surjective : Function.Surjective (toDoubleQuotient G) := by
  intro z
  obtain ⟨w,hw⟩ := QuotientAddGroup.mk'_surjective (twice G).range z
  refine ⟨(w,0),?_⟩
  change QuotientAddGroup.mk' (twice G).range (w+0) = z
  rwa [add_zero]

/-- This is the actual quotient by the sum/difference range, via
the class of the sum. The kernel comparison is a proved equality. -/
noncomputable def cokernelEquiv :
    (G × G) ⧸ (sumDifference G).range ≃+ G ⧸ (twice G).range :=
  QuotientAddGroup.liftEquiv _ (toDoubleQuotient_surjective G) (toDoubleQuotient_ker G).symm

theorem ker_card :
    Nat.card (sumDifference G).ker = Nat.card (twice G).ker :=
  Nat.card_congr (kernelEquiv G).toEquiv

theorem coker_card :
    Nat.card ((G × G) ⧸ (sumDifference G).range) = Nat.card (G ⧸ (twice G).range) :=
  Nat.card_congr (cokernelEquiv G).toEquiv

end OriginalRCMilneSplitLocal318

#print axioms OriginalRCMilneSplitLocal318.kernelEquiv
#print axioms OriginalRCMilneSplitLocal318.cokernelEquiv
