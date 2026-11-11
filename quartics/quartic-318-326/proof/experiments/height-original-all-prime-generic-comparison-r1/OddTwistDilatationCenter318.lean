module
public import OddTwistDilatationSourceMap318
public section
noncomputable section
namespace OddTwistDilatationCenter318
open Polynomial OddTwistDilatationCoordinates318 OddTwistDilatationEtale318
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
variable (V : Type*) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  (pi : V) (hp : Irreducible pi) (u : Vˣ) (a : V)

/-- The original section lands in the good open of the DILATATION chart:
separation from the other contacts implies their values remain units.
The distinguished original twist itself is allowed valuation one. -/
theorem other_contact_unit (b z : V) (hab : IsUnit (a-b)) :
    IsUnit (a+pi*(↑u⁻¹ : V)*z^2-b) := by
  have hsmall : ¬IsUnit (pi*(↑u⁻¹ : V)*z^2) := by
    intro h
    exact hp.not_isUnit (isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left h))
  by_contra h
  have hn : ¬IsUnit (-(pi*(↑u⁻¹ : V)*z^2)) := by
    simpa only [isUnit_neg] using hsmall
  have hs := IsLocalRing.nonunits_add h hn
  have he : (a+pi*(↑u⁻¹ : V)*z^2-b)+(-(pi*(↑u⁻¹ : V)*z^2))=a-b := by ring
  exact hs (he.symm ▸ hab)

variable (d : Fin 3 → Vˣ) (b : Fin 3 → V)
  (hsep : ∀ j, IsUnit (a-b j)) (T y : V) (r : Fin 3 → V)
  (hy : y^2=(u : V)*pi*(T-a)) (hr : ∀ j,(r j)^2=(d j : V)*(T-b j))

/-- A genuine integral point on a genuinely smooth odd-characteristic
chart is produced from the original signed root data. All other roots
are retained, the original distinguished root is pi*Z, and the original
contact parameter evaluates to T. No unit-twist premise is imposed on
that distinguished branch. -/
theorem exists_smooth_center (h2 : IsUnit (2 : V)) :
    ∃ (z : V)
      (hroots : ∀ j,(r j)^2=Polynomial.eval z
        (coefficient pi u a (fun j => (d j : V)) b j))
      (hunits : ∀ j,IsUnit (r j)),
      y=pi*z ∧
      Algebra.Smooth V (Chart V pi u a (fun j => (d j : V)) b) ∧
      point V pi u a (fun j => (d j : V)) b z r hroots hunits
        (coordinate V pi u a (fun j => (d j : V)) b)=z ∧
      point V pi u a (fun j => (d j : V)) b z r hroots hunits
        (contactValue V pi u a (fun j => (d j : V)) b)=T ∧
      ∀ j,point V pi u a (fun j => (d j : V)) b z r hroots hunits
        (ThreeRootCoordinates318.generator _ j)=r j := by
  obtain ⟨z,hz,hT,hroots⟩ := exists_chart_coordinates pi u a
    (fun j => (d j : V)) b T y r hy hr hp
  have htexp : T=a+pi*(↑u⁻¹ : V)*z^2 := by
    simpa only [contact,eval_add,eval_C,eval_mul,eval_pow,eval_X] using hT.symm
  have hunits (j : Fin 3) : IsUnit (r j) := by
    apply (isUnit_pow_iff (by decide : (2 : ℕ) ≠ 0)).mp
    rw [hr j,htexp]
    exact (d j).isUnit.mul (other_contact_unit V pi hp u a (b j) z (hsep j))
  refine ⟨z,hroots,hunits,hz,smooth V pi u a _ b h2,
    point_coordinate V pi u a _ b z r hroots hunits,?_,?_⟩
  · rw [point_contact,hT]
  · exact point_signed_root V pi u a _ b z r hroots hunits
end OddTwistDilatationCenter318
