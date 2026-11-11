module
public import ContactDifferenceSheafEpimorphism318
public section
noncomputable section
namespace RelativeClassBaseTwistIso318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
variable {X B : Scheme.{u}} (p : X ⟶ B) (L K : Line X)
/-- Actual naive relative equality is exactly a whole-line isomorphism
up to one actual base line, before any sheafification. -/
lemma iff_relative : RelativeLineClassQuotient318.classMap p (classOf L)=
    RelativeLineClassQuotient318.classMap p (classOf K) ↔
    ∃ M : Line B,Nonempty ((LineSheafTensor318.line L (LineSheafPullback318.line p M)).object ≅ K.object) := by
  constructor
  · intro h
    obtain ⟨z,hz,he⟩ := (QuotientGroup.mk'_eq_mk' (RelativeLineClassQuotient318.baseLines p)).mp h
    obtain ⟨d,rfl⟩ := hz
    have hd : ∃ M : Line B,classOf M=d := LineSheafClass318.induction (fun M => ⟨M,rfl⟩) d
    obtain ⟨M,rfl⟩ := hd
    refine ⟨M,(classOf_eq_iff _ _).mp ?_⟩
    rw [LineSheafClassGroup318.classOf_tensor]
    exact he
  · rintro ⟨M,hM⟩
    have he := congrArg (RelativeLineClassQuotient318.classMap p) ((classOf_eq_iff _ _).mpr hM)
    rw [LineSheafClassGroup318.classOf_tensor,map_mul,
      ←LineClassPullbackHom318.on_representatives,RelativeLineClassQuotient318.base_class_trivial,mul_one] at he
    exact he
end RelativeClassBaseTwistIso318
