module
public import GenericPrimitiveXCoordinate318
public section
noncomputable section
namespace PrimitiveXEquationDegree318
open GenericPrimitiveXCoordinate318 TranscendentalJGenericFiber318 GenericMarkingOrbitField318
variable (N:ℕ) [NeZero N] (L:Type*) [Field L] [Algebra (K N) L]
variable [FiniteDimensional (K N) L] [IsGalois (K N) L]
variable (P:A N L) (hP:addOrderOf P=N) (H:Subgroup (ZMod N)ˣ)
variable (qN:Polynomial (K N)) (irr:Irreducible qN)
variable (ann : ∀Q:A N L, addOrderOf Q=N → Polynomial.aeval (x N L Q) qN=0)

/-- The only divisional input consumed here is a single irreducible
polynomial annihilating the actual primitive x-coordinates. No splitting,
specified degree, or assertion that it has no extraneous roots is needed. -/
theorem common_minpoly (u:H) : minpoly (K N) (x N L P)=minpoly (K N) (XP N L P H u) := by
  let d := (u.val:ZMod N).val
  have hd : Nat.Coprime d N := (ZMod.isUnit_iff_coprime d N).mp (by simpa [d] using u.val.isUnit)
  have hc : Nat.Coprime (addOrderOf P) d := by rw [hP]; exact hd.symm
  have hQ : addOrderOf (d • P)=N := hc.addOrderOf_nsmul.trans hP
  exact (minpoly.eq_of_irreducible irr (ann P hP)).symm.trans
    (minpoly.eq_of_irreducible irr (ann (d • P) hQ))

/-- The dimension bound is for the invariant field formed from the
actual x-coordinate diamond transformations, not a putative cover degree. -/
theorem degree :
    (Module.finrank (K N) (invariantField N L P H
      (common_minpoly N L P hP H qN irr ann)):ℝ)≤
      (N:ℝ)*H.index*EulerIndex318.eulerProduct N :=
  (Nat.cast_le.mpr (bound N L P H _ hP)).trans (ActualGammaHIndexUpper318.gammaH_index N H)
end PrimitiveXEquationDegree318
