module
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Properties
public section
noncomputable section
namespace ReducedSchemePointFactorization318
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X Y:Scheme} (f:X⟶Y) [IsReduced X] [QuasiCompact f]

/-- A genuine morphism from a reduced source has radical kernel on
EVERY affine target chart, because the actual source section rings
are reduced. Quasi-compactness is used explicitly for the kernel formula. -/
lemma kernel_radical:f.ker.radical=f.ker:=by
  ext U : 2
  simp only [Scheme.IdealSheafData.radical_ideal,Scheme.Hom.ker_apply]
  apply Ideal.IsRadical.radical
  rw [RingHom.ker_eq_comap_bot]
  exact Ideal.isRadical_bot.comap _

lemma vanishing_le_kernel(Z:Closeds Y)(h:Set.range f⊆Z):
    Scheme.IdealSheafData.vanishingIdeal Z≤f.ker:=by
  have hs:f.ker.support≤Z:=by
    change (f.ker.support:Set Y)⊆(Z:Set Y)
    rw [f.support_ker]
    exact closure_minimal h Z.isClosed
  have hi:=Scheme.IdealSheafData.vanishingIdeal_antimono hs
  rw [Scheme.IdealSheafData.vanishingIdeal_support,kernel_radical] at hi
  exact hi

/-- Factor the ACTUAL scheme morphism through the reduced closed
subscheme from its range condition. This is not a factorization of
underlying sets alone; it uses the actual radical kernel ideal sheaf. -/
@[expose] def factor(Z:Closeds Y)(h:Set.range f⊆Z):
    X⟶(Scheme.IdealSheafData.vanishingIdeal Z).subscheme:=
  f.toImage≫Scheme.IdealSheafData.inclusion (vanishing_le_kernel f Z h)
@[reassoc] lemma factor_inclusion(Z:Closeds Y)(h:Set.range f⊆Z):
    factor f Z h≫(Scheme.IdealSheafData.vanishingIdeal Z).subschemeι=f:=by
  rw [factor,Category.assoc,Scheme.IdealSheafData.inclusion_subschemeι,
    Scheme.Hom.toImage_imageι]
end ReducedSchemePointFactorization318
