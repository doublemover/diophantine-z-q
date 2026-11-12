module
public import GlobalDoubleCoordinateCertificate318
public section
noncomputable section
namespace ConcreteOriginalFourEightCoordinates318
open ConcreteG8Domain LocalGenerator318 GlobalGeneratorPoints318 WeierstrassCurve.Affine
local instance : DecidableEq K := Classical.decEq _
@[expose] def x4 : K := x2P
@[expose] def y4 : K := y2P
@[expose] def x8 : K := pair (185409077062376639473514197468962796034664839312971/2378165910128368936043708525094584964402305495424) (-95997379956148838276189174434661503974846859256063/1783624432596276702032781393820938723301729121568)
@[expose] def y8 : K := pair (6435917032254081611655604212170430961199799449537336599906280406883521876745/6737520703225312903969734641895590939265174289300465526947708345907664384) (-18228099854597878127760687820215293675849256817981059410840294664752942276341/26950082812901251615878938567582363757060697157201862107790833383630657536)
@[expose] def slope8 : K := pair (-1584642518430050812445197/314786032497232484288324) (6886359240223415913584699/1259144129988929937153296)
/-- Reuse and credit the EXISTING exact coordinates of2P=4R. -/
lemma multiple4 : ∃ h : E.Nonsingular x4 y4, (4:ℤ) • R=Point.some x4 y4 h := by
  obtain ⟨hn,he⟩:=LocalGenerator318.actual_double_coordinates
  refine ⟨hn,?_⟩
  have hm : (4:ℤ) • R=(2:ℤ) • R+(2:ℤ) • R := by rw [←add_zsmul];norm_num
  rw [hm,two_zsmul_R]
  exact he
/-- Literal original group equality, with exact rational-quadratic coordinates. -/
lemma multiple8 : ∃ h : E.Nonsingular x8 y8, (8:ℤ) • R=Point.some x8 y8 h := by
  obtain ⟨hn,hp⟩:=multiple4
  have hy : y4≠0 := by
    intro hz
    have hh:=congrArg QuadraticAlgebra.re hz
    norm_num [y4,y2P,pair] at hh
  obtain ⟨hn',he⟩:=GlobalDoubleCoordinateCertificate318.double x4 y4 slope8 x8 y8 hn hy
    (by ext <;> norm_num [slope8,x4,y4,x2P,y2P,D,i,pair,pow_succ])
    (by ext <;> norm_num [slope8,x4,x2P,x8,pair,pow_succ])
    (by ext <;> norm_num [slope8,x4,y4,x2P,y2P,x8,y8,pair,pow_succ])
  refine ⟨hn',?_⟩
  have hm : (8:ℤ) • R=(4:ℤ) • R+(4:ℤ) • R := by rw [←add_zsmul];norm_num
  rw [hm,hp]
  exact he
end ConcreteOriginalFourEightCoordinates318
