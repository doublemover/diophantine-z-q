module
public import ComplexSphereAffineNormalization318
public section
noncomputable section
namespace ComplexSphereFourPointNormalization318
open Set Filter Topology
open scoped OnePoint Manifold ContDiff
open ComplexSphereCharts318 ComplexSphereAffineNormalization318
local instance : ChartedSpace ℂ (OnePoint ℂ):=sphereCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω (OnePoint ℂ):=sphere_manifold
variable (p:Fin 4→OnePoint ℂ) (hp:Function.Injective p)
include hp

lemma pole_finite (j:Fin 3) : poleCoordinate (p 0) (p j.succ)≠∞ := by
  rw [←poleCoordinate_at (p 0)]
  intro h
  have hh:=hp ((poleCoordinate (p 0)).injective h)
  exact Fin.succ_ne_zero j hh

/-- Literal finite coordinates of the other three ORIGINAL points after
the constructed pole change, not freely assigned branch parameters. -/
@[expose] def finiteCoordinate (j:Fin 3) : ℂ:=
  (OnePoint.ne_infty_iff_exists.mp (pole_finite p hp j)).choose
lemma finiteCoordinate_spec (j:Fin 3) :
    (finiteCoordinate p hp j:OnePoint ℂ)=poleCoordinate (p 0) (p j.succ):=
  (OnePoint.ne_infty_iff_exists.mp (pole_finite p hp j)).choose_spec
lemma finiteCoordinate_injective : Function.Injective (finiteCoordinate p hp) := by
  intro j k he
  have h:=congrArg (fun z:ℂ=>(z:OnePoint ℂ)) he
  rw [finiteCoordinate_spec,finiteCoordinate_spec] at h
  exact Fin.succ_injective (hp ((poleCoordinate (p 0)).injective h))
lemma denominator_ne : finiteCoordinate p hp 1-finiteCoordinate p hp 0≠0 := by
  intro h
  have he:=finiteCoordinate_injective p hp (sub_eq_zero.mp h)
  norm_num at he

@[expose] def normalization : OnePoint ℂ≃ₜOnePoint ℂ:=
  (poleCoordinate (p 0)).trans
    (affineSphere (finiteCoordinate p hp 1-finiteCoordinate p hp 0)⁻¹
      (-finiteCoordinate p hp 0/(finiteCoordinate p hp 1-finiteCoordinate p hp 0))
      (inv_ne_zero (denominator_ne p hp)))
@[expose] def parameter : ℂ:=
  (finiteCoordinate p hp 2-finiteCoordinate p hp 0)/
    (finiteCoordinate p hp 1-finiteCoordinate p hp 0)

lemma normalization_zero : normalization p hp (p 0)=∞ := by
  change affineSphere _ _ _ (poleCoordinate (p 0) (p 0))=∞
  rw [poleCoordinate_at,affineSphere_infty]
lemma normalization_succ (j:Fin 3) : normalization p hp (p j.succ)=
    ((finiteCoordinate p hp j-finiteCoordinate p hp 0)/
      (finiteCoordinate p hp 1-finiteCoordinate p hp 0):ℂ) := by
  change affineSphere _ _ _ (poleCoordinate (p 0) (p j.succ))=_
  rw [←finiteCoordinate_spec,affineSphere_coe]
  congr 1
  ring
lemma normalization_one : normalization p hp (p 1)=(0:ℂ) := by
  simpa only [sub_self,zero_div] using normalization_succ p hp 0
lemma normalization_two : normalization p hp (p 2)=(1:ℂ) := by
  simpa only [div_self (denominator_ne p hp)] using normalization_succ p hp 1
lemma normalization_three : normalization p hp (p 3)=(parameter p hp:ℂ) :=
  normalization_succ p hp 2

lemma parameter_ne_zero : parameter p hp≠0 := by
  intro h
  have he:normalization p hp (p 3)=normalization p hp (p 1):=by
    rw [normalization_three,normalization_one,h]
  have hh:=hp ((normalization p hp).injective he)
  norm_num at hh
lemma parameter_ne_one : parameter p hp≠1 := by
  intro h
  have he:normalization p hp (p 3)=normalization p hp (p 2):=by
    rw [normalization_three,normalization_two,h]
  have hh:=hp ((normalization p hp).injective he)
  norm_num at hh

/-- Actual biholomorphic three-point normalization, with the fourth
parameter constructed from the SAME original ordered quadruple. -/
theorem normalization_biholomorphic :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (normalization p hp) ∧
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (normalization p hp).symm := by
  have hh:ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (normalization p hp):=
    (affineSphere_holomorphic _ _ _).comp (poleCoordinate_holomorphic (p 0))
  exact ⟨hh,ComplexCurveHomeomorphInverse318.inverse (normalization p hp) hh⟩
end ComplexSphereFourPointNormalization318
