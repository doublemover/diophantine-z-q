module
public import ActualTwoDescentActualShaPowerBounds318
public section
noncomputable section
namespace ActualTwoDescentHigherMultiplesTransport318
set_option maxHeartbeats 16000000
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "Gal" => Field.absoluteGaloisGroup F
local instance : DecidableEq Qbar := Classical.decEq _
open ActualTwoDescentEllipticModel318 ActualTwoDescentFieldAlgebraicClosureHalving318
open ActualTwoDescentFieldGaloisPointAction318 ActualTwoDescentFieldGaloisFixedRational318
open ActualTwoDescentFieldHalvingCocycle318 ActualTwoDescentContinuousEllipticCocycles318
open ActualTwoDescentFullEllipticRepresentation318 ActualTwoDescentFullEllipticHOneKernel318
open groupCohomology

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

abbrev multiples (A : Type*) [AddCommGroup A] (m : ℕ) := (nsmulAddMonoidHom (α:=A) m).range
abbrev torsionKernel (A : Type*) [AddCommGroup A] (m : ℕ) := (nsmulAddMonoidHom (α:=A) m).ker

lemma actual_multiples_map_equiv (e : A ≃+ B) (m : ℕ) : (multiples A m).map e.toAddMonoidHom=multiples B m := by
  ext b
  constructor
  · rintro ⟨a,⟨x,hx⟩,rfl⟩
    refine ⟨e x,?_⟩
    change m • e x=e a
    rw [←e.map_nsmul]
    exact congrArg e hx
  · rintro ⟨b,rfl⟩
    refine ⟨m • e.symm b,⟨e.symm b,rfl⟩,?_⟩
    change e (m • e.symm b)=m • b
    rw [e.map_nsmul,e.apply_symm_apply]

lemma actual_multiples_index_equiv (e : A ≃+ B) (m : ℕ) : (multiples A m).index=(multiples B m).index := by
  rw [←actual_multiples_map_equiv e m]
  exact (AddSubgroup.index_map_equiv (multiples A m) e).symm

lemma actual_multiples_prod (m : ℕ) : multiples (A × B) m=(multiples A m).prod (multiples B m) := by
  ext p
  constructor
  · rintro ⟨q,rfl⟩
    exact ⟨⟨q.1,rfl⟩,⟨q.2,rfl⟩⟩
  · rintro ⟨⟨a,ha⟩,⟨b,hb⟩⟩
    exact ⟨(a,b),Prod.ext ha hb⟩

end ActualTwoDescentHigherMultiplesTransport318
