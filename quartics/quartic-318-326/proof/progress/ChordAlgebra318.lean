module
public import TorusBijection318
public section
noncomputable section
namespace ChordAlgebra318
set_option maxHeartbeats 0

@[expose] def slope (a b x y : ℂ) : ℂ := (y-b)/(x-a)
@[expose] def chordX (a b x y : ℂ) : ℂ := (slope a b x y)^2/4-x-a
@[expose] def chordY (a b x y : ℂ) : ℂ := -b-slope a b x y*(chordX a b x y-a)
@[expose] def slopeD (a b g x y : ℂ) : ℂ := ((6*x^2-g/2)*(x-a)-(y-b)*y)/(x-a)^2

lemma first_flow (a b g h x y : ℂ) (hd : x-a≠0)
    (hf : y^2=4*x^3-g*x-h) (ha : b^2=4*a^3-g*a-h) :
    slope a b x y*slopeD a b g x y/2-y=chordY a b x y := by
  have he : (slope a b x y*slopeD a b g x y/2-y)-chordY a b x y =
      ((b-y)*(y^2-4*x^3+g*x+h)+(y-b)*(b^2-4*a^3+g*a+h))/(4*(x-a)^3) := by
    simp only [chordY, chordX, slopeD, slope]
    field_simp
    ring
  rw [hf,ha] at he
  ring_nf at he
  linear_combination he

lemma second_flow (a b g h x y : ℂ) (hd : x-a≠0)
    (hf : y^2=4*x^3-g*x-h) (ha : b^2=4*a^3-g*a-h) :
    -slopeD a b g x y*(chordX a b x y-a)-
      slope a b x y*(slope a b x y*slopeD a b g x y/2-y)=
      6*(chordX a b x y)^2-g/2 := by
  have he : (-slopeD a b g x y*(chordX a b x y-a)-
      slope a b x y*(slope a b x y*slopeD a b g x y/2-y))-
      (6*(chordX a b x y)^2-g/2) =
      (-3*(-8*a^2*x+a*g+4*a*x^2+2*b*y+h-y^2)*(y^2-4*x^3+g*x+h)+
       -3*(-4*a^3+8*a^2*x-4*a*x^2+b^2-2*b*y-g*x-h+4*x^3)*
        (b^2-4*a^3+g*a+h))/(8*(x-a)^4) := by
    simp only [chordX, slopeD, slope]
    field_simp
    ring
  rw [hf,ha] at he
  ring_nf at he
  linear_combination he

lemma chord_curve (a b g h x y : ℂ) (hd : x-a≠0)
    (hf : y^2=4*x^3-g*x-h) (ha : b^2=4*a^3-g*a-h) :
    (chordY a b x y)^2=4*(chordX a b x y)^3-g*chordX a b x y-h := by
  have he : (chordY a b x y)^2-(4*(chordX a b x y)^3-g*chordX a b x y-h) =
      ((-4*a^3+12*a^2*x-a*g-2*b*y-h-4*x^3+y^2)*(y^2-4*x^3+g*x+h)+
       (4*a^3-12*a*x^2-b^2+2*b*y+g*x+h+4*x^3)*(b^2-4*a^3+g*a+h))/
        (4*(x-a)^3) := by
    simp only [chordY, chordX, slope]
    field_simp
    ring
  rw [hf,ha] at he
  ring_nf at he
  linear_combination he
end ChordAlgebra318
