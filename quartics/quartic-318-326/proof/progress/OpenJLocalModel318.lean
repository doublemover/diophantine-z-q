module
public import LocalizedNormalModel318
public import EvenValuationNormalization318
public section
noncomputable section
namespace OpenJLocalModel318
set_option maxHeartbeats 700000
open AlgebraicGeometry PowerSeries
open scoped TensorProduct
variable (N:ℕ) (B:Type) [CommRing B] [IsDomain B]
  [Algebra (OpenJModel318.Base N) B] [Algebra (Polynomial ℤ) B]
  [IsScalarTower (Polynomial ℤ) (OpenJModel318.Base N) B]
  [Algebra.Etale (OpenJModel318.Base N) B] [Module.Finite (OpenJModel318.Base N) B]

abbrev Model:=integralClosure (Polynomial ℤ) B
abbrev Point:=AffineHeightOneStalk318.Point (Model B)
abbrev Stalk (x:Point B):=AffineHeightOneStalk318.Stalk (Model B) x

/-- The genuine integral-closure model of the finite etale open-j cover has
DVR stalks at every actual codimension-one point. No normality, Noetherianity,
local DVR, or generic-function-field premise is supplied. -/
theorem actual_stalk_dvr (hN:N≠0) (x:Point B) : IsDiscreteValuationRing (Stalk B x) := by
  have h:=OpenJNormalModel318.actual_finite_normal_model N B hN
  letI:=h.2.1
  letI:=h.2.2
  exact AffineHeightOneStalk318.stalk_dvr (Model B) x

/-- The resulting actual completed local stalk is a complete DVR and the
canonical completion map is faithfully flat and preserves every valuation. -/
theorem completed_local_data (hN:N≠0) (x:Point B) :
    letI:=actual_stalk_dvr N B hN x
    IsDiscreteValuationRing (ActualDVRCompletion318.Completion (Stalk B x)) ∧
      Module.FaithfullyFlat (Stalk B x) (ActualDVRCompletion318.Completion (Stalk B x)) ∧
      ∀a:Stalk B x,
        IsDiscreteValuationRing.addVal (ActualDVRCompletion318.Completion (Stalk B x))
          (algebraMap (Stalk B x) (ActualDVRCompletion318.Completion (Stalk B x)) a)=
            IsDiscreteValuationRing.addVal (Stalk B x) a := by
  letI:=actual_stalk_dvr N B hN x
  exact ⟨inferInstance, CompletionDescent318.completion_faithfullyFlat _,
    ActualDVRCompletion318.completion_value _⟩

/-- The coefficient algebra is the actual integral j-line, followed by its
canonical integral-closure map, actual stalk germ, and actual completion. -/
theorem actual_formal_map (hN:N≠0) (x:Point B) (u:(Stalk B x)ˣ)
    (pi:Stalk B x) (m:ℕ) (hp:Irreducible pi) (hm:0<m) :
    letI:=actual_stalk_dvr N B hN x
    ∃e:(Polynomial ℤ)⟦X⟧→+*ActualDVRCompletion318.Completion (Stalk B x),
      e X=algebraMap (Stalk B x) (ActualDVRCompletion318.Completion (Stalk B x))
        ((u:Stalk B x)*pi^(2*m)) ∧
      ∀a:Polynomial ℤ,e (C a)=
        algebraMap (Stalk B x) (ActualDVRCompletion318.Completion (Stalk B x))
          (StructureSheaf.toStalk (CommRingCat.of (Model B)) x.val
            (algebraMap (Polynomial ℤ) (Model B) a)) := by
  have h:=OpenJNormalModel318.actual_finite_normal_model N B hN
  letI:=h.2.1
  letI:=h.2.2
  exact HeightOneContact318.source_formal_map x u pi m hp hm

/-- An actual positive even contact value at an actual codimension-one point
constructs its canonical formal base map without a chosen uniformizer. -/
theorem even_contact_formal_map (hN:N≠0) (x:Point B) (f:Stalk B x) (m:ℕ)
    (hm:0<m)
    (hv:letI:=actual_stalk_dvr N B hN x
      IsDiscreteValuationRing.addVal (Stalk B x) f=((2*m:ℕ):ℕ∞)) :
    letI:=actual_stalk_dvr N B hN x
    ∃e:(Polynomial ℤ)⟦X⟧→+*ActualDVRCompletion318.Completion (Stalk B x),
      e X=algebraMap (Stalk B x) (ActualDVRCompletion318.Completion (Stalk B x)) f ∧
      ∀a:Polynomial ℤ,e (C a)=
        algebraMap (Stalk B x) (ActualDVRCompletion318.Completion (Stalk B x))
          (StructureSheaf.toStalk (CommRingCat.of (Model B)) x.val
            (algebraMap (Polynomial ℤ) (Model B) a)) := by
  letI:=actual_stalk_dvr N B hN x
  exact EvenValuationNormalization318.formal_map (R:=Stalk B x)
    ((StructureSheaf.toStalk (CommRingCat.of (Model B)) x.val).hom.comp
      (algebraMap (Polynomial ℤ) (Model B))) f m hm hv

/-- The finite etale normalization of the actual quadratic contact order at a
codimension-one point of the constructed integral open-j model. -/
theorem even_contact_normalization (hN:N≠0) (x:Point B) (f:Stalk B x) (m:ℕ)
    (h2:IsUnit (2:Stalk B x))
    (hv:letI:=actual_stalk_dvr N B hN x
      IsDiscreteValuationRing.addVal (Stalk B x) f=((2*m:ℕ):ℕ∞)) :
    let R:=Stalk B x
    letI:=actual_stalk_dvr N B hN x
    ∃(u:Rˣ) (φ:QuadraticPresentation318.RootRing f →ₐ[R]
        (EvenContactEtale318.RootRing u ⊗[R] FractionRing R)),
      letI:Algebra (QuadraticPresentation318.RootRing f)
          (EvenContactEtale318.RootRing u ⊗[R] FractionRing R):=φ.toRingHom.toAlgebra
      IsIntegralClosure (EvenContactEtale318.RootRing u)
          (QuadraticPresentation318.RootRing f)
          (EvenContactEtale318.RootRing u ⊗[R] FractionRing R) ∧
        Algebra.Etale R (EvenContactEtale318.RootRing u) ∧
        Module.Finite R (EvenContactEtale318.RootRing u) ∧
        Function.Injective φ ∧
        Nonempty (FractionRing R ⊗[R] QuadraticPresentation318.RootRing f ≃ₐ[R]
          EvenContactEtale318.RootRing u ⊗[R] FractionRing R) := by
  letI:=actual_stalk_dvr N B hN x
  exact EvenValuationNormalization318.normalization f m h2 hv

end OpenJLocalModel318
