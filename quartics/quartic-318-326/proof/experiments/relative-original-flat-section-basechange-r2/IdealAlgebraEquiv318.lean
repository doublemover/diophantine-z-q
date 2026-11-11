module
public import VaryingSourceTensorCollapse318
public section
noncomputable section
namespace IdealAlgebraEquiv318
universe u
variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) (I : Ideal A)
/-- Restrict an actual source algebra equivalence to the entire ideal,
retaining its actual inclusion and the coefficient scalar action. -/
@[expose] def map : I →ₗ[R] I.map e.toRingHom where
  toFun x := ⟨e x,Ideal.mem_map_of_mem e.toRingHom x.property⟩
  map_add' x y := Subtype.ext (map_add e x y)
  map_smul' r x := Subtype.ext (e.toLinearEquiv.map_smul r x)
lemma bijective : Function.Bijective (map R A B e I) := by
  constructor
  · intro x y h
    exact Subtype.ext (e.injective (congrArg Subtype.val h))
  · intro y
    obtain ⟨x,hx,hxy⟩ := (Ideal.mem_map_of_equiv e.toRingEquiv y.val).mp y.property
    exact ⟨⟨x,hx⟩,Subtype.ext hxy⟩
@[expose] def equivalence : I ≃ₗ[R] I.map e.toRingHom :=
  LinearEquiv.ofBijective (map R A B e I) (bijective R A B e I)
lemma value (x : I) : (equivalence R A B e I x).val=e x.val := rfl
end IdealAlgebraEquiv318
