module
public import ContactFrameNormalization318
public import SourceOpenFractionField318
public section
noncomputable section
namespace ContactUnbranchedDifferentialFrame318
open Polynomial KaehlerDifferential ContactKummerOrder318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
variable (c:Fin 4→ℚˣ)

@[expose] def baseFrame : KaehlerDifferential ℚ OpenBase ≃ₗ[OpenBase] OpenBase := by
  letI:=Algebra.FormallyEtale.of_isLocalization (Rₘ:=OpenBase) (Submonoid.powers denominator)
  exact EtaleDifferentialFrame318.ofFormallyEtale (KaehlerDifferential.polynomialEquiv ℚ)

/-- A literal dt frame on the entire unbranched order, not only its function field. -/
@[expose] def frame : KaehlerDifferential ℚ (OpenOrder c) ≃ₗ[OpenOrder c] OpenOrder c := by
  letI:Algebra.Etale OpenBase (OpenOrder c):=(open_finite_free_etale c).2.2
  exact EtaleDifferentialFrame318.ofFormallyEtale baseFrame

@[expose] def coordinate : OpenOrder c :=
  algebraMap OpenBase (OpenOrder c) (algebraMap ℚ[X] OpenBase X)

theorem frame_D : frame c (D ℚ (OpenOrder c) (coordinate c))=1 := by
  letI:=Algebra.FormallyEtale.of_isLocalization (Rₘ:=OpenBase) (Submonoid.powers denominator)
  letI:Algebra.Etale OpenBase (OpenOrder c):=(open_finite_free_etale c).2.2
  change EtaleDifferentialFrame318.ofFormallyEtale baseFrame (D ℚ _ (algebraMap _ _ _))=1
  rw [ContactFrameNormalization318.ofFormallyEtale_D]
  change algebraMap OpenBase (OpenOrder c)
    (EtaleDifferentialFrame318.ofFormallyEtale (KaehlerDifferential.polynomialEquiv ℚ)
      (D ℚ OpenBase (algebraMap ℚ[X] OpenBase X)))=1
  rw [ContactFrameNormalization318.ofFormallyEtale_D,
    KaehlerDifferential.polynomialEquiv_D,Polynomial.derivative_X,map_one,map_one]

@[expose] def toOpen : SourceOrder c→ₐ[ℚ]OpenOrder c :=
  { SourceOpenFractionField318.orderToOpen c with
    commutes' := fun r=>RingHom.map_rat_algebraMap _ r }

theorem toOpen_coordinate : toOpen c (algebraMap ℚ[X] (SourceOrder c) X)=coordinate c :=
  SourceOpenFractionField318.orderToOpen_on_polynomial c X

theorem D_t_ne_zero : D ℚ (SourceOrder c) (algebraMap ℚ[X] (SourceOrder c) X)≠0 := by
  letI:=ContactKummerOpenDomain318.open_domain c
  intro h
  have hh:=congrArg (fun ω=>frame c (AlgHomDifferential318.map (toOpen c) ω)) h
  rw [AlgHomDifferential318.map_D,toOpen_coordinate,frame_D,map_zero,map_zero] at hh
  exact one_ne_zero hh
end ContactUnbranchedDifferentialFrame318
