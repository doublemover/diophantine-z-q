module

public import SparseQuartic

public section

namespace Current318FinalPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/- Exact residual syntax from ../candidates/v10-reduced-anchor-318/sheared/compiled-ir.json.
Source SHA256: 716c8daa06142c9e10d22b0fd507fd97f06873fcb1fa88a77ed347fc873f9e97.
This data declaration and the theorems below do not prove the arithmetic source characterization. -/


-- UA.reciprocal.f.0.definition
@[expose] def row0 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 1 1⟩,
    ⟨2, 0, .quadratic 2 2⟩,
    ⟨-1, 0, .linear 58⟩
]

-- UA.reciprocal.f.1.definition
@[expose] def row1 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 1 2⟩,
    ⟨-1, 0, .linear 59⟩
]

-- UA.reciprocal.equation.0
@[expose] def row2 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .one⟩,
    ⟨-1, 0, .quadratic 3 3⟩,
    ⟨-2, 0, .quadratic 4 4⟩,
    ⟨-11, 0, .quadratic 58 58⟩,
    ⟨48, 0, .quadratic 58 59⟩,
    ⟨-88, 0, .quadratic 59 59⟩
]

-- UA.reciprocal.equation.1
@[expose] def row3 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 3 4⟩,
    ⟨-3, 0, .quadratic 58 58⟩,
    ⟨22, 0, .quadratic 58 59⟩,
    ⟨-24, 0, .quadratic 59 59⟩
]

-- US.reciprocal.f.0.definition
@[expose] def row4 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 5 5⟩,
    ⟨2, 0, .quadratic 6 6⟩,
    ⟨-1, 0, .linear 60⟩
]

-- US.reciprocal.f.1.definition
@[expose] def row5 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 5 6⟩,
    ⟨-1, 0, .linear 61⟩
]

-- US.reciprocal.equation.0
@[expose] def row6 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .one⟩,
    ⟨-1, 0, .quadratic 7 7⟩,
    ⟨-2, 0, .quadratic 8 8⟩,
    ⟨-11, 0, .quadratic 60 60⟩,
    ⟨48, 0, .quadratic 60 61⟩,
    ⟨-88, 0, .quadratic 61 61⟩
]

-- US.reciprocal.equation.1
@[expose] def row7 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 7 8⟩,
    ⟨-3, 0, .quadratic 60 60⟩,
    ⟨22, 0, .quadratic 60 61⟩,
    ⟨-24, 0, .quadratic 61 61⟩
]

-- UT.reciprocal.f.0.definition
@[expose] def row8 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 9 9⟩,
    ⟨2, 0, .quadratic 10 10⟩,
    ⟨-2, 0, .linear 62⟩
]

-- UT.reciprocal.f.1.definition
@[expose] def row9 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 9 10⟩,
    ⟨-1, 0, .linear 63⟩
]

-- UT.reciprocal.equation.0
@[expose] def row10 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .one⟩,
    ⟨-1, 0, .quadratic 11 11⟩,
    ⟨-2, 0, .quadratic 12 12⟩,
    ⟨-44, 0, .quadratic 62 62⟩,
    ⟨96, 0, .quadratic 62 63⟩,
    ⟨-88, 0, .quadratic 63 63⟩
]

-- UT.reciprocal.equation.1
@[expose] def row11 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 11 12⟩,
    ⟨-12, 0, .quadratic 62 62⟩,
    ⟨44, 0, .quadratic 62 63⟩,
    ⟨-24, 0, .quadratic 63 63⟩
]

-- UZ.reciprocal.f.0.definition
@[expose] def row12 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 13 13⟩,
    ⟨2, 0, .quadratic 14 14⟩,
    ⟨-1, 0, .linear 64⟩
]

-- UZ.reciprocal.f.1.definition
@[expose] def row13 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 13 14⟩,
    ⟨-1, 0, .linear 65⟩
]

-- UZ.reciprocal.equation.0
@[expose] def row14 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .one⟩,
    ⟨-1, 0, .quadratic 15 15⟩,
    ⟨-2, 0, .quadratic 16 16⟩,
    ⟨-11, 0, .quadratic 64 64⟩,
    ⟨48, 0, .quadratic 64 65⟩,
    ⟨-88, 0, .quadratic 65 65⟩
]

-- UZ.reciprocal.equation.1
@[expose] def row15 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 15 16⟩,
    ⟨-3, 0, .quadratic 64 64⟩,
    ⟨22, 0, .quadratic 64 65⟩,
    ⟨-24, 0, .quadratic 65 65⟩
]

-- VA.reciprocal.f.0.definition
@[expose] def row16 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 17 17⟩,
    ⟨2, 0, .quadratic 18 18⟩,
    ⟨-1, 0, .linear 66⟩
]

-- VA.reciprocal.f.1.definition
@[expose] def row17 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 17 18⟩,
    ⟨-1, 0, .linear 67⟩
]

-- VA.reciprocal.equation.0
@[expose] def row18 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .one⟩,
    ⟨-1, 0, .quadratic 19 19⟩,
    ⟨-2, 0, .quadratic 20 20⟩,
    ⟨-11, 0, .quadratic 66 66⟩,
    ⟨48, 0, .quadratic 66 67⟩,
    ⟨-88, 0, .quadratic 67 67⟩
]

-- VA.reciprocal.equation.1
@[expose] def row19 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 19 20⟩,
    ⟨-3, 0, .quadratic 66 66⟩,
    ⟨22, 0, .quadratic 66 67⟩,
    ⟨-24, 0, .quadratic 67 67⟩
]

-- VS.reciprocal.f.0.definition
@[expose] def row20 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 21 21⟩,
    ⟨2, 0, .quadratic 22 22⟩,
    ⟨-1, 0, .linear 68⟩
]

-- VS.reciprocal.f.1.definition
@[expose] def row21 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 21 22⟩,
    ⟨-1, 0, .linear 69⟩
]

-- VS.reciprocal.equation.0
@[expose] def row22 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .one⟩,
    ⟨-1, 0, .quadratic 23 23⟩,
    ⟨-2, 0, .quadratic 24 24⟩,
    ⟨-11, 0, .quadratic 68 68⟩,
    ⟨48, 0, .quadratic 68 69⟩,
    ⟨-88, 0, .quadratic 69 69⟩
]

-- VS.reciprocal.equation.1
@[expose] def row23 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 23 24⟩,
    ⟨-3, 0, .quadratic 68 68⟩,
    ⟨22, 0, .quadratic 68 69⟩,
    ⟨-24, 0, .quadratic 69 69⟩
]

-- VT.reciprocal.f.0.definition
@[expose] def row24 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 25 25⟩,
    ⟨2, 0, .quadratic 26 26⟩,
    ⟨-1, 0, .linear 70⟩
]

-- VT.reciprocal.f.1.definition
@[expose] def row25 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 25 26⟩,
    ⟨-1, 0, .linear 71⟩
]

-- VT.reciprocal.equation.0
@[expose] def row26 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .one⟩,
    ⟨-1, 0, .quadratic 27 27⟩,
    ⟨-2, 0, .quadratic 28 28⟩,
    ⟨-11, 0, .quadratic 70 70⟩,
    ⟨48, 0, .quadratic 70 71⟩,
    ⟨-88, 0, .quadratic 71 71⟩
]

-- VT.reciprocal.equation.1
@[expose] def row27 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 27 28⟩,
    ⟨-3, 0, .quadratic 70 70⟩,
    ⟨22, 0, .quadratic 70 71⟩,
    ⟨-24, 0, .quadratic 71 71⟩
]

-- VZ.reciprocal.f.0.definition
@[expose] def row28 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 29 29⟩,
    ⟨2, 0, .quadratic 30 30⟩,
    ⟨-1, 0, .linear 72⟩
]

-- VZ.reciprocal.f.1.definition
@[expose] def row29 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 29 30⟩,
    ⟨-1, 0, .linear 73⟩
]

-- VZ.reciprocal.equation.0
@[expose] def row30 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .one⟩,
    ⟨-1, 0, .quadratic 31 31⟩,
    ⟨-2, 0, .quadratic 32 32⟩,
    ⟨-11, 0, .quadratic 72 72⟩,
    ⟨48, 0, .quadratic 72 73⟩,
    ⟨-88, 0, .quadratic 73 73⟩
]

-- VZ.reciprocal.equation.1
@[expose] def row31 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 31 32⟩,
    ⟨-3, 0, .quadratic 72 72⟩,
    ⟨22, 0, .quadratic 72 73⟩,
    ⟨-24, 0, .quadratic 73 73⟩
]

-- fixedAnchor.t.0.definition
@[expose] def row32 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 33 35⟩,
    ⟨2, 0, .quadratic 34 36⟩,
    ⟨-1, 0, .linear 74⟩
]

-- fixedAnchor.t.1.definition
@[expose] def row33 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 33 36⟩,
    ⟨1, 0, .quadratic 34 35⟩,
    ⟨-1, 0, .linear 75⟩
]

-- V0.reciprocal.f.0.definition
@[expose] def row34 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 35 74⟩,
    ⟨2, 0, .quadratic 36 75⟩,
    ⟨-1, 0, .linear 76⟩
]

-- V0.reciprocal.f.1.definition
@[expose] def row35 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 35 75⟩,
    ⟨1, 0, .quadratic 36 74⟩,
    ⟨-1, 0, .linear 77⟩
]

-- fixedAnchor.quarticRelation.0
@[expose] def row36 : List (SparseQuartic.Term 318) := [
    ⟨8, 0, .one⟩,
    ⟨-57, 0, .linear 33⟩,
    ⟨56, 0, .linear 34⟩,
    ⟨-78, 0, .linear 74⟩,
    ⟨-88, 0, .quadratic 74 74⟩,
    ⟨192, 0, .quadratic 74 75⟩,
    ⟨144, 0, .linear 75⟩,
    ⟨-176, 0, .quadratic 75 75⟩,
    ⟨-57, 0, .linear 76⟩,
    ⟨56, 0, .linear 77⟩
]

-- fixedAnchor.quarticRelation.1
@[expose] def row37 : List (SparseQuartic.Term 318) := [
    ⟨28, 0, .linear 33⟩,
    ⟨-57, 0, .linear 34⟩,
    ⟨72, 0, .linear 74⟩,
    ⟨48, 0, .quadratic 74 74⟩,
    ⟨-176, 0, .quadratic 74 75⟩,
    ⟨-78, 0, .linear 75⟩,
    ⟨96, 0, .quadratic 75 75⟩,
    ⟨28, 0, .linear 76⟩,
    ⟨-57, 0, .linear 77⟩
]

-- H.normSquareRootEquation
@[expose] def row38 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 33 33⟩,
    ⟨-2, 0, .quadratic 34 34⟩,
    ⟨-1, 0, .quadratic 37 37⟩
]

-- rootA.realDifferenceInverse.definition
@[expose] def row39 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .one⟩,
    ⟨1, 0, .quadratic 58 78⟩,
    ⟨-1, 0, .quadratic 66 78⟩
]

-- rootA.squareRoot.definition.0
@[expose] def row40 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 1 19⟩,
    ⟨2, 0, .quadratic 2 20⟩,
    ⟨1, 0, .quadratic 3 17⟩,
    ⟨2, 0, .quadratic 4 18⟩,
    ⟨1, 0, .quadratic 58 79⟩,
    ⟨4, 0, .quadratic 59 80⟩,
    ⟨-1, 0, .quadratic 66 79⟩,
    ⟨-4, 0, .quadratic 67 80⟩
]

-- rootA.squareRoot.definition.1
@[expose] def row41 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 1 20⟩,
    ⟨1, 0, .quadratic 2 19⟩,
    ⟨1, 0, .quadratic 3 18⟩,
    ⟨1, 0, .quadratic 4 17⟩,
    ⟨1, 0, .quadratic 58 80⟩,
    ⟨2, 0, .quadratic 59 79⟩,
    ⟨-1, 0, .quadratic 66 80⟩,
    ⟨-2, 0, .quadratic 67 79⟩
]

-- rootS.realDifferenceInverse.definition
@[expose] def row42 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .one⟩,
    ⟨1, 0, .quadratic 60 81⟩,
    ⟨-1, 0, .quadratic 68 81⟩
]

-- rootS.squareRoot.definition.0
@[expose] def row43 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 5 23⟩,
    ⟨2, 0, .quadratic 6 24⟩,
    ⟨1, 0, .quadratic 7 21⟩,
    ⟨2, 0, .quadratic 8 22⟩,
    ⟨1, 0, .quadratic 60 82⟩,
    ⟨4, 0, .quadratic 61 83⟩,
    ⟨-1, 0, .quadratic 68 82⟩,
    ⟨-4, 0, .quadratic 69 83⟩
]

-- rootS.squareRoot.definition.1
@[expose] def row44 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 5 24⟩,
    ⟨1, 0, .quadratic 6 23⟩,
    ⟨1, 0, .quadratic 7 22⟩,
    ⟨1, 0, .quadratic 8 21⟩,
    ⟨1, 0, .quadratic 60 83⟩,
    ⟨2, 0, .quadratic 61 82⟩,
    ⟨-1, 0, .quadratic 68 83⟩,
    ⟨-2, 0, .quadratic 69 82⟩
]

-- rootT.realDifferenceInverse.definition
@[expose] def row45 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .one⟩,
    ⟨2, 0, .quadratic 62 84⟩,
    ⟨-1, 0, .quadratic 70 84⟩
]

-- rootT.squareRoot.definition.0
@[expose] def row46 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 9 27⟩,
    ⟨2, 0, .quadratic 10 28⟩,
    ⟨1, 0, .quadratic 11 25⟩,
    ⟨2, 0, .quadratic 12 26⟩,
    ⟨2, 0, .quadratic 62 85⟩,
    ⟨4, 0, .quadratic 63 86⟩,
    ⟨-1, 0, .quadratic 70 85⟩,
    ⟨-4, 0, .quadratic 71 86⟩
]

-- rootT.squareRoot.definition.1
@[expose] def row47 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 9 28⟩,
    ⟨1, 0, .quadratic 10 27⟩,
    ⟨1, 0, .quadratic 11 26⟩,
    ⟨1, 0, .quadratic 12 25⟩,
    ⟨2, 0, .quadratic 62 86⟩,
    ⟨2, 0, .quadratic 63 85⟩,
    ⟨-1, 0, .quadratic 70 86⟩,
    ⟨-2, 0, .quadratic 71 85⟩
]

-- rootZ.realDifferenceInverse.definition
@[expose] def row48 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .one⟩,
    ⟨1, 0, .quadratic 64 87⟩,
    ⟨-1, 0, .quadratic 72 87⟩
]

-- rootZ.squareRoot.definition.0
@[expose] def row49 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 13 31⟩,
    ⟨2, 0, .quadratic 14 32⟩,
    ⟨1, 0, .quadratic 15 29⟩,
    ⟨2, 0, .quadratic 16 30⟩,
    ⟨1, 0, .quadratic 64 88⟩,
    ⟨4, 0, .quadratic 65 89⟩,
    ⟨-1, 0, .quadratic 72 88⟩,
    ⟨-4, 0, .quadratic 73 89⟩
]

-- rootZ.squareRoot.definition.1
@[expose] def row50 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 13 32⟩,
    ⟨1, 0, .quadratic 14 31⟩,
    ⟨1, 0, .quadratic 15 30⟩,
    ⟨1, 0, .quadratic 16 29⟩,
    ⟨1, 0, .quadratic 64 89⟩,
    ⟨2, 0, .quadratic 65 88⟩,
    ⟨-1, 0, .quadratic 72 89⟩,
    ⟨-2, 0, .quadratic 73 88⟩
]

-- logV0.fSquare.0.definition
@[expose] def row51 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 76 76⟩,
    ⟨2, 0, .quadratic 77 77⟩,
    ⟨-1, 0, .linear 90⟩
]

-- logV0.fSquare.1.definition
@[expose] def row52 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 76 77⟩,
    ⟨-1, 0, .linear 91⟩
]

-- logV0.polynomial.definition.0
@[expose] def row53 : List (SparseQuartic.Term 318) := [
    ⟨195, 0, .one⟩,
    ⟨-2013, 0, .linear 90⟩,
    ⟨3088, 0, .quadratic 90 90⟩,
    ⟨-16896, 0, .quadratic 90 91⟩,
    ⟨1155, 0, .quadratic 90 92⟩,
    ⟨-1260, 0, .quadratic 90 93⟩,
    ⟨4392, 0, .linear 91⟩,
    ⟨24704, 0, .quadratic 91 91⟩,
    ⟨-2520, 0, .quadratic 91 92⟩,
    ⟨4620, 0, .quadratic 91 93⟩,
    ⟨-195, 0, .linear 92⟩
]

-- logV0.polynomial.definition.1
@[expose] def row54 : List (SparseQuartic.Term 318) := [
    ⟨1098, 0, .linear 90⟩,
    ⟨-2112, 0, .quadratic 90 90⟩,
    ⟨12352, 0, .quadratic 90 91⟩,
    ⟨-630, 0, .quadratic 90 92⟩,
    ⟨1155, 0, .quadratic 90 93⟩,
    ⟨-4026, 0, .linear 91⟩,
    ⟨-16896, 0, .quadratic 91 91⟩,
    ⟨2310, 0, .quadratic 91 92⟩,
    ⟨-2520, 0, .quadratic 91 93⟩,
    ⟨-195, 0, .linear 93⟩
]

-- logV0.definition.0
@[expose] def row55 : List (SparseQuartic.Term 318) := [
    ⟨8, 0, .quadratic 35 92⟩,
    ⟨-28, 0, .quadratic 35 93⟩,
    ⟨39, 0, .quadratic 35 94⟩,
    ⟨-72, 0, .quadratic 35 95⟩,
    ⟨-28, 0, .quadratic 36 92⟩,
    ⟨16, 0, .quadratic 36 93⟩,
    ⟨-72, 0, .quadratic 36 94⟩,
    ⟨78, 0, .quadratic 36 95⟩,
    ⟨88, 0, .quadratic 76 94⟩,
    ⟨-96, 0, .quadratic 76 95⟩,
    ⟨-96, 0, .quadratic 77 94⟩,
    ⟨176, 0, .quadratic 77 95⟩,
    ⟨57, 0, .linear 94⟩,
    ⟨-56, 0, .linear 95⟩
]

-- logV0.definition.1
@[expose] def row56 : List (SparseQuartic.Term 318) := [
    ⟨14, 0, .quadratic 35 92⟩,
    ⟨-8, 0, .quadratic 35 93⟩,
    ⟨36, 0, .quadratic 35 94⟩,
    ⟨-39, 0, .quadratic 35 95⟩,
    ⟨-8, 0, .quadratic 36 92⟩,
    ⟨28, 0, .quadratic 36 93⟩,
    ⟨-39, 0, .quadratic 36 94⟩,
    ⟨72, 0, .quadratic 36 95⟩,
    ⟨48, 0, .quadratic 76 94⟩,
    ⟨-88, 0, .quadratic 76 95⟩,
    ⟨-88, 0, .quadratic 77 94⟩,
    ⟨96, 0, .quadratic 77 95⟩,
    ⟨28, 0, .linear 94⟩,
    ⟨-57, 0, .linear 95⟩
]

-- logV2.polynomial.definition.0
@[expose] def row57 : List (SparseQuartic.Term 318) := [
    ⟨157, 0, .one⟩,
    ⟨40, 0, .linear 23⟩,
    ⟨-2, 0, .quadratic 23 23⟩,
    ⟨-75, 0, .quadratic 23 96⟩,
    ⟨-4, 0, .quadratic 24 24⟩,
    ⟨-150, 0, .quadratic 24 97⟩,
    ⟨-120, 0, .linear 96⟩
]

-- logV2.polynomial.definition.1
@[expose] def row58 : List (SparseQuartic.Term 318) := [
    ⟨4, 0, .quadratic 23 24⟩,
    ⟨75, 0, .quadratic 23 97⟩,
    ⟨-40, 0, .linear 24⟩,
    ⟨75, 0, .quadratic 24 96⟩,
    ⟨120, 0, .linear 97⟩
]

-- logV3.polynomial.definition.0
@[expose] def row59 : List (SparseQuartic.Term 318) := [
    ⟨157, 0, .one⟩,
    ⟨40, 0, .linear 27⟩,
    ⟨-2, 0, .quadratic 27 27⟩,
    ⟨-75, 0, .quadratic 27 98⟩,
    ⟨-4, 0, .quadratic 28 28⟩,
    ⟨-150, 0, .quadratic 28 99⟩,
    ⟨-120, 0, .linear 98⟩
]

-- logV3.polynomial.definition.1
@[expose] def row60 : List (SparseQuartic.Term 318) := [
    ⟨4, 0, .quadratic 27 28⟩,
    ⟨75, 0, .quadratic 27 99⟩,
    ⟨-40, 0, .linear 28⟩,
    ⟨75, 0, .quadratic 28 98⟩,
    ⟨120, 0, .linear 99⟩
]

-- logV4.polynomial.definition.0
@[expose] def row61 : List (SparseQuartic.Term 318) := [
    ⟨157, 0, .one⟩,
    ⟨40, 0, .linear 31⟩,
    ⟨-2, 0, .quadratic 31 31⟩,
    ⟨-75, 0, .quadratic 31 100⟩,
    ⟨-4, 0, .quadratic 32 32⟩,
    ⟨-150, 0, .quadratic 32 101⟩,
    ⟨-120, 0, .linear 100⟩
]

-- logV4.polynomial.definition.1
@[expose] def row62 : List (SparseQuartic.Term 318) := [
    ⟨4, 0, .quadratic 31 32⟩,
    ⟨75, 0, .quadratic 31 101⟩,
    ⟨-40, 0, .linear 32⟩,
    ⟨75, 0, .quadratic 32 100⟩,
    ⟨120, 0, .linear 101⟩
]

-- L1.definition.0
@[expose] def row63 : List (SparseQuartic.Term 318) := [
    ⟨39, 0, .linear 1⟩,
    ⟨57, 0, .quadratic 1 35⟩,
    ⟨-56, 0, .quadratic 1 36⟩,
    ⟨88, 0, .quadratic 1 74⟩,
    ⟨-96, 0, .quadratic 1 75⟩,
    ⟨-72, 0, .linear 2⟩,
    ⟨-56, 0, .quadratic 2 35⟩,
    ⟨114, 0, .quadratic 2 36⟩,
    ⟨-96, 0, .quadratic 2 74⟩,
    ⟨176, 0, .quadratic 2 75⟩,
    ⟨8, 0, .quadratic 3 102⟩,
    ⟨-28, 0, .quadratic 3 103⟩,
    ⟨-28, 0, .quadratic 4 102⟩,
    ⟨16, 0, .quadratic 4 103⟩
]

-- L1.definition.1
@[expose] def row64 : List (SparseQuartic.Term 318) := [
    ⟨36, 0, .linear 1⟩,
    ⟨28, 0, .quadratic 1 35⟩,
    ⟨-57, 0, .quadratic 1 36⟩,
    ⟨48, 0, .quadratic 1 74⟩,
    ⟨-88, 0, .quadratic 1 75⟩,
    ⟨-39, 0, .linear 2⟩,
    ⟨-57, 0, .quadratic 2 35⟩,
    ⟨56, 0, .quadratic 2 36⟩,
    ⟨-88, 0, .quadratic 2 74⟩,
    ⟨96, 0, .quadratic 2 75⟩,
    ⟨14, 0, .quadratic 3 102⟩,
    ⟨-8, 0, .quadratic 3 103⟩,
    ⟨-8, 0, .quadratic 4 102⟩,
    ⟨28, 0, .quadratic 4 103⟩
]

-- LP1.definition.0
@[expose] def row65 : List (SparseQuartic.Term 318) := [
    ⟨6, 0, .linear 17⟩,
    ⟨-1, 0, .quadratic 17 19⟩,
    ⟨-2, 0, .quadratic 18 20⟩,
    ⟨5, 0, .quadratic 94 104⟩,
    ⟨10, 0, .quadratic 95 105⟩
]

-- LP1.definition.1
@[expose] def row66 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 17 20⟩,
    ⟨-6, 0, .linear 18⟩,
    ⟨1, 0, .quadratic 18 19⟩,
    ⟨-5, 0, .quadratic 94 105⟩,
    ⟨-5, 0, .quadratic 95 104⟩
]

-- L2.definition.0
@[expose] def row67 : List (SparseQuartic.Term 318) := [
    ⟨39, 0, .linear 5⟩,
    ⟨57, 0, .quadratic 5 35⟩,
    ⟨-56, 0, .quadratic 5 36⟩,
    ⟨88, 0, .quadratic 5 74⟩,
    ⟨-96, 0, .quadratic 5 75⟩,
    ⟨-72, 0, .linear 6⟩,
    ⟨-56, 0, .quadratic 6 35⟩,
    ⟨114, 0, .quadratic 6 36⟩,
    ⟨-96, 0, .quadratic 6 74⟩,
    ⟨176, 0, .quadratic 6 75⟩,
    ⟨8, 0, .quadratic 7 106⟩,
    ⟨-28, 0, .quadratic 7 107⟩,
    ⟨-28, 0, .quadratic 8 106⟩,
    ⟨16, 0, .quadratic 8 107⟩
]

-- L2.definition.1
@[expose] def row68 : List (SparseQuartic.Term 318) := [
    ⟨36, 0, .linear 5⟩,
    ⟨28, 0, .quadratic 5 35⟩,
    ⟨-57, 0, .quadratic 5 36⟩,
    ⟨48, 0, .quadratic 5 74⟩,
    ⟨-88, 0, .quadratic 5 75⟩,
    ⟨-39, 0, .linear 6⟩,
    ⟨-57, 0, .quadratic 6 35⟩,
    ⟨56, 0, .quadratic 6 36⟩,
    ⟨-88, 0, .quadratic 6 74⟩,
    ⟨96, 0, .quadratic 6 75⟩,
    ⟨14, 0, .quadratic 7 106⟩,
    ⟨-8, 0, .quadratic 7 107⟩,
    ⟨-8, 0, .quadratic 8 106⟩,
    ⟨28, 0, .quadratic 8 107⟩
]

-- LP2.definition.0
@[expose] def row69 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 21 96⟩,
    ⟨2, 0, .quadratic 22 97⟩,
    ⟨1, 0, .quadratic 94 108⟩,
    ⟨2, 0, .quadratic 95 109⟩
]

-- LP2.definition.1
@[expose] def row70 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 21 97⟩,
    ⟨1, 0, .quadratic 22 96⟩,
    ⟨1, 0, .quadratic 94 109⟩,
    ⟨1, 0, .quadratic 95 108⟩
]

-- L3.definition.0
@[expose] def row71 : List (SparseQuartic.Term 318) := [
    ⟨39, 0, .linear 9⟩,
    ⟨57, 0, .quadratic 9 35⟩,
    ⟨-56, 0, .quadratic 9 36⟩,
    ⟨88, 0, .quadratic 9 74⟩,
    ⟨-96, 0, .quadratic 9 75⟩,
    ⟨-72, 0, .linear 10⟩,
    ⟨-56, 0, .quadratic 10 35⟩,
    ⟨114, 0, .quadratic 10 36⟩,
    ⟨-96, 0, .quadratic 10 74⟩,
    ⟨176, 0, .quadratic 10 75⟩,
    ⟨8, 0, .quadratic 11 110⟩,
    ⟨-28, 0, .quadratic 11 111⟩,
    ⟨-28, 0, .quadratic 12 110⟩,
    ⟨16, 0, .quadratic 12 111⟩
]

-- L3.definition.1
@[expose] def row72 : List (SparseQuartic.Term 318) := [
    ⟨36, 0, .linear 9⟩,
    ⟨28, 0, .quadratic 9 35⟩,
    ⟨-57, 0, .quadratic 9 36⟩,
    ⟨48, 0, .quadratic 9 74⟩,
    ⟨-88, 0, .quadratic 9 75⟩,
    ⟨-39, 0, .linear 10⟩,
    ⟨-57, 0, .quadratic 10 35⟩,
    ⟨56, 0, .quadratic 10 36⟩,
    ⟨-88, 0, .quadratic 10 74⟩,
    ⟨96, 0, .quadratic 10 75⟩,
    ⟨14, 0, .quadratic 11 110⟩,
    ⟨-8, 0, .quadratic 11 111⟩,
    ⟨-8, 0, .quadratic 12 110⟩,
    ⟨28, 0, .quadratic 12 111⟩
]

-- LP3.definition.0
@[expose] def row73 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 25 98⟩,
    ⟨2, 0, .quadratic 26 99⟩,
    ⟨1, 0, .quadratic 94 112⟩,
    ⟨2, 0, .quadratic 95 113⟩
]

-- LP3.definition.1
@[expose] def row74 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 25 99⟩,
    ⟨1, 0, .quadratic 26 98⟩,
    ⟨1, 0, .quadratic 94 113⟩,
    ⟨1, 0, .quadratic 95 112⟩
]

-- L4.definition.0
@[expose] def row75 : List (SparseQuartic.Term 318) := [
    ⟨39, 0, .linear 13⟩,
    ⟨57, 0, .quadratic 13 35⟩,
    ⟨-56, 0, .quadratic 13 36⟩,
    ⟨88, 0, .quadratic 13 74⟩,
    ⟨-96, 0, .quadratic 13 75⟩,
    ⟨-72, 0, .linear 14⟩,
    ⟨-56, 0, .quadratic 14 35⟩,
    ⟨114, 0, .quadratic 14 36⟩,
    ⟨-96, 0, .quadratic 14 74⟩,
    ⟨176, 0, .quadratic 14 75⟩,
    ⟨8, 0, .quadratic 15 114⟩,
    ⟨-28, 0, .quadratic 15 115⟩,
    ⟨-28, 0, .quadratic 16 114⟩,
    ⟨16, 0, .quadratic 16 115⟩
]

-- L4.definition.1
@[expose] def row76 : List (SparseQuartic.Term 318) := [
    ⟨36, 0, .linear 13⟩,
    ⟨28, 0, .quadratic 13 35⟩,
    ⟨-57, 0, .quadratic 13 36⟩,
    ⟨48, 0, .quadratic 13 74⟩,
    ⟨-88, 0, .quadratic 13 75⟩,
    ⟨-39, 0, .linear 14⟩,
    ⟨-57, 0, .quadratic 14 35⟩,
    ⟨56, 0, .quadratic 14 36⟩,
    ⟨-88, 0, .quadratic 14 74⟩,
    ⟨96, 0, .quadratic 14 75⟩,
    ⟨14, 0, .quadratic 15 114⟩,
    ⟨-8, 0, .quadratic 15 115⟩,
    ⟨-8, 0, .quadratic 16 114⟩,
    ⟨28, 0, .quadratic 16 115⟩
]

-- LP4.definition.0
@[expose] def row77 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 29 100⟩,
    ⟨2, 0, .quadratic 30 101⟩,
    ⟨1, 0, .quadratic 94 116⟩,
    ⟨2, 0, .quadratic 95 117⟩
]

-- LP4.definition.1
@[expose] def row78 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 29 101⟩,
    ⟨1, 0, .quadratic 30 100⟩,
    ⟨1, 0, .quadratic 94 117⟩,
    ⟨1, 0, .quadratic 95 116⟩
]

-- inputOddSquare.definition
@[expose] def row79 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 0 0⟩,
    ⟨-1, 0, .linear 118⟩
]

-- Lucas.C.0.definition
@[expose] def row80 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 106 114⟩,
    ⟨2, 0, .quadratic 107 115⟩,
    ⟨-1, 0, .linear 119⟩
]

-- Lucas.C.1.definition
@[expose] def row81 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 106 115⟩,
    ⟨1, 0, .quadratic 107 114⟩,
    ⟨-1, 0, .linear 120⟩
]

-- Lucas.AT.0.definition
@[expose] def row82 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 106 110⟩,
    ⟨2, 0, .quadratic 107 111⟩,
    ⟨-1, 0, .linear 121⟩
]

-- Lucas.AT.1.definition
@[expose] def row83 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 106 111⟩,
    ⟨1, 0, .quadratic 107 110⟩,
    ⟨-1, 0, .linear 122⟩
]

-- Lucas.F0.definition
@[expose] def row84 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 110 110⟩,
    ⟨2, 0, .quadratic 111 111⟩,
    ⟨4, 0, .quadratic 114 114⟩,
    ⟨-4, 0, .quadratic 114 119⟩,
    ⟨2, 0, .quadratic 114 121⟩,
    ⟨8, 0, .quadratic 115 115⟩,
    ⟨-8, 0, .quadratic 115 120⟩,
    ⟨4, 0, .quadratic 115 122⟩,
    ⟨1, 0, .quadratic 119 119⟩,
    ⟨-1, 0, .quadratic 119 121⟩,
    ⟨2, 0, .quadratic 120 120⟩,
    ⟨-2, 0, .quadratic 120 122⟩,
    ⟨-1, 0, .linear 123⟩
]

-- Lucas.F1.definition
@[expose] def row85 : List (SparseQuartic.Term 318) := [
    ⟨2, 0, .quadratic 110 111⟩,
    ⟨8, 0, .quadratic 114 115⟩,
    ⟨-4, 0, .quadratic 114 120⟩,
    ⟨2, 0, .quadratic 114 122⟩,
    ⟨-4, 0, .quadratic 115 119⟩,
    ⟨2, 0, .quadratic 115 121⟩,
    ⟨2, 0, .quadratic 119 120⟩,
    ⟨-1, 0, .quadratic 119 122⟩,
    ⟨-1, 0, .quadratic 120 121⟩,
    ⟨-2, 0, .linear 124⟩
]

-- normV0.testSquare.definition
@[expose] def row86 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 90 90⟩,
    ⟨-8, 0, .quadratic 91 91⟩,
    ⟨-1, 0, .linear 125⟩
]

-- testSquare.0.0.definition
@[expose] def row87 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 37 37⟩,
    ⟨-1, 0, .linear 126⟩
]

-- testSquare.10.0.definition
@[expose] def row88 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 102 102⟩,
    ⟨-2, 0, .quadratic 102 104⟩,
    ⟨2, 0, .quadratic 103 103⟩,
    ⟨4, 0, .quadratic 103 105⟩,
    ⟨1, 0, .quadratic 104 104⟩,
    ⟨2, 0, .quadratic 105 105⟩,
    ⟨-1, 0, .linear 127⟩
]

-- testSquare.10.1.definition
@[expose] def row89 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 102 103⟩,
    ⟨1, 0, .quadratic 102 105⟩,
    ⟨-1, 0, .quadratic 103 104⟩,
    ⟨-1, 0, .quadratic 104 105⟩,
    ⟨-1, 0, .linear 128⟩
]

-- testSquare.11.0.definition
@[expose] def row90 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 106 106⟩,
    ⟨-2, 0, .quadratic 106 108⟩,
    ⟨2, 0, .quadratic 107 107⟩,
    ⟨4, 0, .quadratic 107 109⟩,
    ⟨1, 0, .quadratic 108 108⟩,
    ⟨2, 0, .quadratic 109 109⟩,
    ⟨-1, 0, .linear 129⟩
]

-- testSquare.11.1.definition
@[expose] def row91 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 106 107⟩,
    ⟨1, 0, .quadratic 106 109⟩,
    ⟨-1, 0, .quadratic 107 108⟩,
    ⟨-1, 0, .quadratic 108 109⟩,
    ⟨-1, 0, .linear 130⟩
]

-- testSquare.12.0.definition
@[expose] def row92 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 110 110⟩,
    ⟨-2, 0, .quadratic 110 112⟩,
    ⟨2, 0, .quadratic 111 111⟩,
    ⟨4, 0, .quadratic 111 113⟩,
    ⟨1, 0, .quadratic 112 112⟩,
    ⟨2, 0, .quadratic 113 113⟩,
    ⟨-1, 0, .linear 131⟩
]

-- testSquare.12.1.definition
@[expose] def row93 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 110 111⟩,
    ⟨1, 0, .quadratic 110 113⟩,
    ⟨-1, 0, .quadratic 111 112⟩,
    ⟨-1, 0, .quadratic 112 113⟩,
    ⟨-1, 0, .linear 132⟩
]

-- testSquare.13.0.definition
@[expose] def row94 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 114 114⟩,
    ⟨-2, 0, .quadratic 114 116⟩,
    ⟨2, 0, .quadratic 115 115⟩,
    ⟨4, 0, .quadratic 115 117⟩,
    ⟨1, 0, .quadratic 116 116⟩,
    ⟨2, 0, .quadratic 117 117⟩,
    ⟨-1, 0, .linear 133⟩
]

-- testSquare.13.1.definition
@[expose] def row95 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 114 115⟩,
    ⟨1, 0, .quadratic 114 117⟩,
    ⟨-1, 0, .quadratic 115 116⟩,
    ⟨-1, 0, .quadratic 116 117⟩,
    ⟨-1, 0, .linear 134⟩
]

-- testSquare.14.0.definition
@[expose] def row96 : List (SparseQuartic.Term 318) := [
    ⟨221771664, 0, .quadratic 0 0⟩,
    ⟨-29784, 0, .quadratic 0 102⟩,
    ⟨443543328, 0, .quadratic 0 118⟩,
    ⟨1, 0, .quadratic 102 102⟩,
    ⟨-29784, 0, .quadratic 102 118⟩,
    ⟨2, 0, .quadratic 103 103⟩,
    ⟨221771664, 0, .quadratic 118 118⟩,
    ⟨-221771664, 0, .linear 135⟩
]

-- testSquare.14.1.definition
@[expose] def row97 : List (SparseQuartic.Term 318) := [
    ⟨14892, 0, .quadratic 0 103⟩,
    ⟨-1, 0, .quadratic 102 103⟩,
    ⟨14892, 0, .quadratic 103 118⟩,
    ⟨-14892, 0, .linear 136⟩
]

-- testSquare.15.0.definition
@[expose] def row98 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 123 123⟩,
    ⟨8, 0, .quadratic 124 124⟩,
    ⟨-1, 0, .linear 137⟩
]

-- testSquare.15.1.definition
@[expose] def row99 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 123 124⟩,
    ⟨-1, 0, .linear 138⟩
]

-- heightRootProduct.S.0.definition
@[expose] def row100 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 79 82⟩,
    ⟨2, 0, .quadratic 80 83⟩,
    ⟨-1, 0, .linear 139⟩
]

-- heightRootProduct.S.1.definition
@[expose] def row101 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 79 83⟩,
    ⟨1, 0, .quadratic 80 82⟩,
    ⟨-1, 0, .linear 140⟩
]

-- heightRootProduct.T.0.definition
@[expose] def row102 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 85 139⟩,
    ⟨2, 0, .quadratic 86 140⟩,
    ⟨-1, 0, .linear 141⟩
]

-- heightRootProduct.T.1.definition
@[expose] def row103 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 85 140⟩,
    ⟨1, 0, .quadratic 86 139⟩,
    ⟨-1, 0, .linear 142⟩
]

-- heightRootProduct.Z.0.definition
@[expose] def row104 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 88 141⟩,
    ⟨2, 0, .quadratic 89 142⟩,
    ⟨-1, 0, .linear 143⟩
]

-- heightRootProduct.Z.1.definition
@[expose] def row105 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 88 142⟩,
    ⟨1, 0, .quadratic 89 141⟩,
    ⟨-1, 0, .linear 144⟩
]

-- heightRootProduct.norm.definition
@[expose] def row106 : List (SparseQuartic.Term 318) := [
    ⟨4096, 0, .quadratic 143 143⟩,
    ⟨-8192, 0, .quadratic 144 144⟩,
    ⟨-1, 0, .linear 145⟩
]

-- commonLambdaInverse.definition
@[expose] def row107 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .one⟩,
    ⟨-1, 0, .quadratic 38 146⟩
]

-- detector0.Fsquare.definition
@[expose] def row108 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 38 38⟩,
    ⟨-1, 0, .linear 147⟩
]

-- detector0.Fmiddle.definition
@[expose] def row109 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 38 147⟩,
    ⟨-1, 0, .linear 148⟩
]

-- detector0.F.definition
@[expose] def row110 : List (SparseQuartic.Term 318) := [
    ⟨1205412, 0, .quadratic 38 147⟩,
    ⟨3081901, 0, .quadratic 147 147⟩,
    ⟨1952786, 0, .quadratic 147 148⟩,
    ⟨-3081901, 0, .linear 149⟩
]

-- detector0.delta3.definition
@[expose] def row111 : List (SparseQuartic.Term 318) := [
    ⟨2, 0, .quadratic 38 38⟩,
    ⟨-1, 0, .quadratic 38 147⟩,
    ⟨1, 0, .linear 150⟩
]

-- detector0.q1.definition
@[expose] def row112 : List (SparseQuartic.Term 318) := [
    ⟨1952786, 0, .one⟩,
    ⟨-3905572, 0, .linear 38⟩,
    ⟨32, 0, .quadratic 38 151⟩,
    ⟨1952786, 0, .linear 147⟩,
    ⟨-76265, 0, .quadratic 147 151⟩,
    ⟨-3081901, 0, .quadratic 149 151⟩
]

-- detector0.eWeight.definition
@[expose] def row113 : List (SparseQuartic.Term 318) := [
    ⟨3, 0, .quadratic 38 151⟩,
    ⟨-1, 0, .quadratic 147 151⟩,
    ⟨1, 0, .quadratic 150 151⟩,
    ⟨1, 0, .linear 152⟩
]

-- detector0.eDelta.definition
@[expose] def row114 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 38 151⟩,
    ⟨1, 0, .quadratic 38 152⟩,
    ⟨-1, 0, .linear 153⟩
]

-- detector0.e2.definition
@[expose] def row115 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 151 151⟩,
    ⟨2, 0, .quadratic 151 152⟩,
    ⟨1, 0, .quadratic 152 152⟩,
    ⟨-1, 0, .linear 154⟩
]

-- detector0.e4OverDelta.definition
@[expose] def row116 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 38 155⟩,
    ⟨-1, 0, .quadratic 154 154⟩,
    ⟨-1, 0, .linear 155⟩
]

-- detector0.q4.definition
@[expose] def row117 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 151 156⟩,
    ⟨1, 0, .quadratic 152 156⟩,
    ⟨-1, 0, .quadratic 153 156⟩,
    ⟨-1, 0, .quadratic 155 155⟩
]

-- detector0.q7.definition
@[expose] def row118 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 151 157⟩,
    ⟨-1, 0, .quadratic 156 156⟩
]

-- detector0.q13.definition
@[expose] def row119 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 151 158⟩,
    ⟨-1, 0, .quadratic 157 157⟩
]

-- detector0.normChain.0.0.definition
@[expose] def row120 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .one⟩,
    ⟨1, 0, .quadratic 126 156⟩,
    ⟨-1, 0, .linear 159⟩
]

-- detector0.normChain.1.0.definition
@[expose] def row121 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 125 151⟩,
    ⟨1, 0, .quadratic 159 159⟩,
    ⟨-1, 0, .linear 160⟩
]

-- detector0.normChain.2.0.definition
@[expose] def row122 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 58 151⟩,
    ⟨1, 0, .quadratic 160 160⟩,
    ⟨-1, 0, .linear 161⟩
]

-- detector0.normChain.2.1.definition
@[expose] def row123 : List (SparseQuartic.Term 318) := [
    ⟨2, 0, .quadratic 59 151⟩,
    ⟨-1, 0, .linear 162⟩
]

-- detector0.normChain.3.0.definition
@[expose] def row124 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 60 151⟩,
    ⟨1, 0, .quadratic 161 161⟩,
    ⟨2, 0, .quadratic 162 162⟩,
    ⟨-1, 0, .linear 163⟩
]

-- detector0.normChain.3.1.definition
@[expose] def row125 : List (SparseQuartic.Term 318) := [
    ⟨2, 0, .quadratic 61 151⟩,
    ⟨2, 0, .quadratic 161 162⟩,
    ⟨-1, 0, .linear 164⟩
]

-- detector0.normChain.4.0.definition
@[expose] def row126 : List (SparseQuartic.Term 318) := [
    ⟨2, 0, .quadratic 62 151⟩,
    ⟨1, 0, .quadratic 163 163⟩,
    ⟨2, 0, .quadratic 164 164⟩,
    ⟨-1, 0, .linear 165⟩
]

-- detector0.normChain.4.1.definition
@[expose] def row127 : List (SparseQuartic.Term 318) := [
    ⟨2, 0, .quadratic 63 151⟩,
    ⟨2, 0, .quadratic 163 164⟩,
    ⟨-1, 0, .linear 166⟩
]

-- detector0.normChain.5.0.definition
@[expose] def row128 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 64 151⟩,
    ⟨1, 0, .quadratic 165 165⟩,
    ⟨2, 0, .quadratic 166 166⟩,
    ⟨-1, 0, .linear 167⟩
]

-- detector0.normChain.5.1.definition
@[expose] def row129 : List (SparseQuartic.Term 318) := [
    ⟨2, 0, .quadratic 65 151⟩,
    ⟨2, 0, .quadratic 165 166⟩,
    ⟨-1, 0, .linear 168⟩
]

-- detector0.normChain.6.0.definition
@[expose] def row130 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 19 151⟩,
    ⟨-1, 0, .linear 151⟩,
    ⟨1, 0, .quadratic 167 167⟩,
    ⟨2, 0, .quadratic 168 168⟩,
    ⟨-1, 0, .linear 169⟩
]

-- detector0.normChain.6.1.definition
@[expose] def row131 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 20 151⟩,
    ⟨-2, 0, .quadratic 167 168⟩,
    ⟨1, 0, .linear 170⟩
]

-- detector0.normChain.7.0.definition
@[expose] def row132 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 23 151⟩,
    ⟨-1, 0, .linear 151⟩,
    ⟨1, 0, .quadratic 169 169⟩,
    ⟨2, 0, .quadratic 170 170⟩,
    ⟨-1, 0, .linear 171⟩
]

-- detector0.normChain.7.1.definition
@[expose] def row133 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 24 151⟩,
    ⟨-2, 0, .quadratic 169 170⟩,
    ⟨1, 0, .linear 172⟩
]

-- detector0.normChain.8.0.definition
@[expose] def row134 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 27 151⟩,
    ⟨-1, 0, .linear 151⟩,
    ⟨1, 0, .quadratic 171 171⟩,
    ⟨2, 0, .quadratic 172 172⟩,
    ⟨-1, 0, .linear 173⟩
]

-- detector0.normChain.8.1.definition
@[expose] def row135 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 28 151⟩,
    ⟨-2, 0, .quadratic 171 172⟩,
    ⟨1, 0, .linear 174⟩
]

-- detector0.normChain.9.0.definition
@[expose] def row136 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 31 151⟩,
    ⟨-1, 0, .linear 151⟩,
    ⟨1, 0, .quadratic 173 173⟩,
    ⟨2, 0, .quadratic 174 174⟩,
    ⟨-1, 0, .linear 175⟩
]

-- detector0.normChain.9.1.definition
@[expose] def row137 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 32 151⟩,
    ⟨-2, 0, .quadratic 173 174⟩,
    ⟨1, 0, .linear 176⟩
]

-- detector0.normChain.10.0.definition
@[expose] def row138 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 127 156⟩,
    ⟨1, 0, .quadratic 175 175⟩,
    ⟨2, 0, .quadratic 176 176⟩,
    ⟨-1, 0, .linear 177⟩
]

-- detector0.normChain.10.1.definition
@[expose] def row139 : List (SparseQuartic.Term 318) := [
    ⟨2, 0, .quadratic 128 156⟩,
    ⟨2, 0, .quadratic 175 176⟩,
    ⟨-1, 0, .linear 178⟩
]

-- detector0.normChain.11.0.definition
@[expose] def row140 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 129 158⟩,
    ⟨1, 0, .quadratic 177 177⟩,
    ⟨2, 0, .quadratic 178 178⟩,
    ⟨-1, 0, .linear 179⟩
]

-- detector0.normChain.11.1.definition
@[expose] def row141 : List (SparseQuartic.Term 318) := [
    ⟨2, 0, .quadratic 130 158⟩,
    ⟨2, 0, .quadratic 177 178⟩,
    ⟨-1, 0, .linear 180⟩
]

-- detector0.normChain.12.0.definition
@[expose] def row142 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 131 158⟩,
    ⟨1, 0, .quadratic 179 179⟩,
    ⟨2, 0, .quadratic 180 180⟩,
    ⟨-1, 0, .linear 181⟩
]

-- detector0.normChain.12.1.definition
@[expose] def row143 : List (SparseQuartic.Term 318) := [
    ⟨2, 0, .quadratic 132 158⟩,
    ⟨2, 0, .quadratic 179 180⟩,
    ⟨-1, 0, .linear 182⟩
]

-- detector0.normChain.13.0.definition
@[expose] def row144 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 133 158⟩,
    ⟨1, 0, .quadratic 181 181⟩,
    ⟨2, 0, .quadratic 182 182⟩,
    ⟨-1, 0, .linear 183⟩
]

-- detector0.normChain.13.1.definition
@[expose] def row145 : List (SparseQuartic.Term 318) := [
    ⟨2, 0, .quadratic 134 158⟩,
    ⟨2, 0, .quadratic 181 182⟩,
    ⟨-1, 0, .linear 184⟩
]

-- detector0.normChain.14.0.definition
@[expose] def row146 : List (SparseQuartic.Term 318) := [
    ⟨110885832, 0, .quadratic 0 156⟩,
    ⟨-7446, 0, .quadratic 102 156⟩,
    ⟨110885832, 0, .quadratic 118 156⟩,
    ⟨221771664, 0, .quadratic 135 156⟩,
    ⟨13860729, 0, .linear 156⟩,
    ⟨1, 0, .quadratic 183 183⟩,
    ⟨2, 0, .quadratic 184 184⟩,
    ⟨-1, 0, .linear 185⟩
]

-- detector0.normChain.14.1.definition
@[expose] def row147 : List (SparseQuartic.Term 318) := [
    ⟨7446, 0, .quadratic 103 156⟩,
    ⟨29784, 0, .quadratic 136 156⟩,
    ⟨-2, 0, .quadratic 183 184⟩,
    ⟨1, 0, .linear 186⟩
]

-- detector0.normChain.15.0.definition
@[expose] def row148 : List (SparseQuartic.Term 318) := [
    ⟨2, 0, .quadratic 123 158⟩,
    ⟨-1, 0, .quadratic 137 158⟩,
    ⟨-1, 0, .linear 158⟩,
    ⟨-1, 0, .quadratic 185 185⟩,
    ⟨-2, 0, .quadratic 186 186⟩,
    ⟨1, 0, .linear 187⟩
]

-- detector0.normChain.15.1.definition
@[expose] def row149 : List (SparseQuartic.Term 318) := [
    ⟨4, 0, .quadratic 124 158⟩,
    ⟨-4, 0, .quadratic 138 158⟩,
    ⟨-2, 0, .quadratic 185 186⟩,
    ⟨1, 0, .linear 188⟩
]

-- detector0.normOver2w0.definition
@[expose] def row150 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 187 187⟩,
    ⟨-2, 0, .quadratic 187 189⟩,
    ⟨-2, 0, .quadratic 188 188⟩
]

-- detector0.B.definition
@[expose] def row151 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 151 190⟩,
    ⟨1, 0, .quadratic 152 190⟩,
    ⟨-1, 0, .quadratic 153 190⟩,
    ⟨-1, 0, .quadratic 189 189⟩
]

-- detector0.normalizedH.definition
@[expose] def row152 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 39 190⟩,
    ⟨-1, 0, .linear 191⟩
]

-- detector0.normalizedS2.definition
@[expose] def row153 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 40 40⟩,
    ⟨-1, 0, .linear 192⟩
]

-- detector0.firstConic
@[expose] def row154 : List (SparseQuartic.Term 318) := [
    ⟨3, 0, .quadratic 39 191⟩,
    ⟨17, 0, .quadratic 41 41⟩,
    ⟨-289, 0, .linear 190⟩,
    ⟨-34, 0, .linear 191⟩
]

-- detector0.normalizedProduct.definition
@[expose] def row155 : List (SparseQuartic.Term 318) := [
    ⟨867, 0, .quadratic 39 39⟩,
    ⟨-102, 0, .quadratic 39 191⟩,
    ⟨-34, 0, .quadratic 39 192⟩,
    ⟨3, 0, .quadratic 191 191⟩,
    ⟨2, 0, .quadratic 191 192⟩,
    ⟨-1, 0, .quadratic 192 192⟩,
    ⟨-3, 0, .linear 193⟩
]

-- detector0.secondConic
@[expose] def row156 : List (SparseQuartic.Term 318) := [
    ⟨17, 0, .quadratic 42 42⟩,
    ⟨3, 0, .quadratic 190 193⟩
]

-- detector1.t.definition
@[expose] def row157 : List (SparseQuartic.Term 318) := [
    ⟨16777216, 0, .quadratic 143 143⟩,
    ⟨8192, 0, .quadratic 143 145⟩,
    ⟨1, 0, .quadratic 145 145⟩,
    ⟨-16777216, 0, .quadratic 146 194⟩
]

-- detector1.Fsquare.definition
@[expose] def row158 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 194 194⟩,
    ⟨-1, 0, .linear 195⟩
]

-- detector1.Fmiddle.definition
@[expose] def row159 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 194 195⟩,
    ⟨-1, 0, .linear 196⟩
]

-- detector1.F.definition
@[expose] def row160 : List (SparseQuartic.Term 318) := [
    ⟨1205412, 0, .quadratic 194 195⟩,
    ⟨3081901, 0, .quadratic 195 195⟩,
    ⟨1952786, 0, .quadratic 195 196⟩,
    ⟨-1205412, 0, .linear 197⟩
]

-- detector1.Adelta.definition
@[expose] def row161 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 146 194⟩,
    ⟨-1, 0, .quadratic 146 195⟩,
    ⟨-1, 0, .linear 198⟩
]

-- detector1.Adelta4.half.square.definition
@[expose] def row162 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 198 198⟩,
    ⟨-1, 0, .linear 199⟩
]

-- detector1.Adelta4.square.definition
@[expose] def row163 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 199 199⟩,
    ⟨-1, 0, .linear 200⟩
]

-- detector1.eWeight.definition
@[expose] def row164 : List (SparseQuartic.Term 318) := [
    ⟨32, 0, .quadratic 194 201⟩,
    ⟨-76265, 0, .quadratic 195 201⟩,
    ⟨-1205412, 0, .quadratic 197 201⟩,
    ⟨-1952786, 0, .quadratic 198 200⟩
]

-- detector1.delta3.definition
@[expose] def row165 : List (SparseQuartic.Term 318) := [
    ⟨2, 0, .quadratic 194 194⟩,
    ⟨-1, 0, .quadratic 194 195⟩,
    ⟨-2, 0, .linear 202⟩
]

-- detector1.q1.definition
@[expose] def row166 : List (SparseQuartic.Term 318) := [
    ⟨3, 0, .quadratic 194 203⟩,
    ⟨-1, 0, .quadratic 195 203⟩,
    ⟨-1, 0, .linear 201⟩,
    ⟨-2, 0, .quadratic 202 203⟩,
    ⟨-1, 0, .linear 203⟩
]

-- detector1.eDelta.definition
@[expose] def row167 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 194 201⟩,
    ⟨-1, 0, .linear 204⟩
]

-- detector1.e2.definition
@[expose] def row168 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 201 201⟩,
    ⟨-1, 0, .linear 205⟩
]

-- detector1.e4OverDelta.definition
@[expose] def row169 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 194 206⟩,
    ⟨-1, 0, .quadratic 205 205⟩,
    ⟨-1, 0, .linear 206⟩
]

-- detector1.q4.definition
@[expose] def row170 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 201 207⟩,
    ⟨-1, 0, .quadratic 204 207⟩,
    ⟨1, 0, .quadratic 206 206⟩
]

-- detector1.q7.definition
@[expose] def row171 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 203 208⟩,
    ⟨-1, 0, .quadratic 207 207⟩
]

-- detector1.q13.definition
@[expose] def row172 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 203 209⟩,
    ⟨-1, 0, .quadratic 208 208⟩
]

-- detector1.normChain.0.0.definition
@[expose] def row173 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .one⟩,
    ⟨1, 0, .quadratic 126 207⟩,
    ⟨-1, 0, .linear 210⟩
]

-- detector1.normChain.1.0.definition
@[expose] def row174 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 125 203⟩,
    ⟨1, 0, .quadratic 210 210⟩,
    ⟨-1, 0, .linear 211⟩
]

-- detector1.normChain.2.0.definition
@[expose] def row175 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 58 203⟩,
    ⟨1, 0, .quadratic 211 211⟩,
    ⟨-1, 0, .linear 212⟩
]

-- detector1.normChain.2.1.definition
@[expose] def row176 : List (SparseQuartic.Term 318) := [
    ⟨2, 0, .quadratic 59 203⟩,
    ⟨-1, 0, .linear 213⟩
]

-- detector1.normChain.3.0.definition
@[expose] def row177 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 60 203⟩,
    ⟨1, 0, .quadratic 212 212⟩,
    ⟨2, 0, .quadratic 213 213⟩,
    ⟨-1, 0, .linear 214⟩
]

-- detector1.normChain.3.1.definition
@[expose] def row178 : List (SparseQuartic.Term 318) := [
    ⟨2, 0, .quadratic 61 203⟩,
    ⟨2, 0, .quadratic 212 213⟩,
    ⟨-1, 0, .linear 215⟩
]

-- detector1.normChain.4.0.definition
@[expose] def row179 : List (SparseQuartic.Term 318) := [
    ⟨2, 0, .quadratic 62 203⟩,
    ⟨1, 0, .quadratic 214 214⟩,
    ⟨2, 0, .quadratic 215 215⟩,
    ⟨-1, 0, .linear 216⟩
]

-- detector1.normChain.4.1.definition
@[expose] def row180 : List (SparseQuartic.Term 318) := [
    ⟨2, 0, .quadratic 63 203⟩,
    ⟨2, 0, .quadratic 214 215⟩,
    ⟨-1, 0, .linear 217⟩
]

-- detector1.normChain.5.0.definition
@[expose] def row181 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 64 203⟩,
    ⟨1, 0, .quadratic 216 216⟩,
    ⟨2, 0, .quadratic 217 217⟩,
    ⟨-1, 0, .linear 218⟩
]

-- detector1.normChain.5.1.definition
@[expose] def row182 : List (SparseQuartic.Term 318) := [
    ⟨2, 0, .quadratic 65 203⟩,
    ⟨2, 0, .quadratic 216 217⟩,
    ⟨-1, 0, .linear 219⟩
]

-- detector1.normChain.6.0.definition
@[expose] def row183 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 19 203⟩,
    ⟨-1, 0, .linear 203⟩,
    ⟨1, 0, .quadratic 218 218⟩,
    ⟨2, 0, .quadratic 219 219⟩,
    ⟨-1, 0, .linear 220⟩
]

-- detector1.normChain.6.1.definition
@[expose] def row184 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 20 203⟩,
    ⟨-2, 0, .quadratic 218 219⟩,
    ⟨1, 0, .linear 221⟩
]

-- detector1.normChain.7.0.definition
@[expose] def row185 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 23 203⟩,
    ⟨-1, 0, .linear 203⟩,
    ⟨1, 0, .quadratic 220 220⟩,
    ⟨2, 0, .quadratic 221 221⟩,
    ⟨-1, 0, .linear 222⟩
]

-- detector1.normChain.7.1.definition
@[expose] def row186 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 24 203⟩,
    ⟨-2, 0, .quadratic 220 221⟩,
    ⟨1, 0, .linear 223⟩
]

-- detector1.normChain.8.0.definition
@[expose] def row187 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 27 203⟩,
    ⟨-1, 0, .linear 203⟩,
    ⟨1, 0, .quadratic 222 222⟩,
    ⟨2, 0, .quadratic 223 223⟩,
    ⟨-1, 0, .linear 224⟩
]

-- detector1.normChain.8.1.definition
@[expose] def row188 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 28 203⟩,
    ⟨-2, 0, .quadratic 222 223⟩,
    ⟨1, 0, .linear 225⟩
]

-- detector1.normChain.9.0.definition
@[expose] def row189 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 31 203⟩,
    ⟨-1, 0, .linear 203⟩,
    ⟨1, 0, .quadratic 224 224⟩,
    ⟨2, 0, .quadratic 225 225⟩,
    ⟨-1, 0, .linear 226⟩
]

-- detector1.normChain.9.1.definition
@[expose] def row190 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 32 203⟩,
    ⟨-2, 0, .quadratic 224 225⟩,
    ⟨1, 0, .linear 227⟩
]

-- detector1.normChain.10.0.definition
@[expose] def row191 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 127 207⟩,
    ⟨1, 0, .quadratic 226 226⟩,
    ⟨2, 0, .quadratic 227 227⟩,
    ⟨-1, 0, .linear 228⟩
]

-- detector1.normChain.10.1.definition
@[expose] def row192 : List (SparseQuartic.Term 318) := [
    ⟨2, 0, .quadratic 128 207⟩,
    ⟨2, 0, .quadratic 226 227⟩,
    ⟨-1, 0, .linear 229⟩
]

-- detector1.normChain.11.0.definition
@[expose] def row193 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 129 209⟩,
    ⟨1, 0, .quadratic 228 228⟩,
    ⟨2, 0, .quadratic 229 229⟩,
    ⟨-1, 0, .linear 230⟩
]

-- detector1.normChain.11.1.definition
@[expose] def row194 : List (SparseQuartic.Term 318) := [
    ⟨2, 0, .quadratic 130 209⟩,
    ⟨2, 0, .quadratic 228 229⟩,
    ⟨-1, 0, .linear 231⟩
]

-- detector1.normChain.12.0.definition
@[expose] def row195 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 131 209⟩,
    ⟨1, 0, .quadratic 230 230⟩,
    ⟨2, 0, .quadratic 231 231⟩,
    ⟨-1, 0, .linear 232⟩
]

-- detector1.normChain.12.1.definition
@[expose] def row196 : List (SparseQuartic.Term 318) := [
    ⟨2, 0, .quadratic 132 209⟩,
    ⟨2, 0, .quadratic 230 231⟩,
    ⟨-1, 0, .linear 233⟩
]

-- detector1.normChain.13.0.definition
@[expose] def row197 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 133 209⟩,
    ⟨1, 0, .quadratic 232 232⟩,
    ⟨2, 0, .quadratic 233 233⟩,
    ⟨-1, 0, .linear 234⟩
]

-- detector1.normChain.13.1.definition
@[expose] def row198 : List (SparseQuartic.Term 318) := [
    ⟨2, 0, .quadratic 134 209⟩,
    ⟨2, 0, .quadratic 232 233⟩,
    ⟨-1, 0, .linear 235⟩
]

-- detector1.normChain.14.0.definition
@[expose] def row199 : List (SparseQuartic.Term 318) := [
    ⟨110885832, 0, .quadratic 0 207⟩,
    ⟨-7446, 0, .quadratic 102 207⟩,
    ⟨110885832, 0, .quadratic 118 207⟩,
    ⟨221771664, 0, .quadratic 135 207⟩,
    ⟨13860729, 0, .linear 207⟩,
    ⟨1, 0, .quadratic 234 234⟩,
    ⟨2, 0, .quadratic 235 235⟩,
    ⟨-1, 0, .linear 236⟩
]

-- detector1.normChain.14.1.definition
@[expose] def row200 : List (SparseQuartic.Term 318) := [
    ⟨7446, 0, .quadratic 103 207⟩,
    ⟨29784, 0, .quadratic 136 207⟩,
    ⟨-2, 0, .quadratic 234 235⟩,
    ⟨1, 0, .linear 237⟩
]

-- detector1.normChain.15.0.definition
@[expose] def row201 : List (SparseQuartic.Term 318) := [
    ⟨2, 0, .quadratic 123 209⟩,
    ⟨-1, 0, .quadratic 137 209⟩,
    ⟨-1, 0, .linear 209⟩,
    ⟨-1, 0, .quadratic 236 236⟩,
    ⟨-2, 0, .quadratic 237 237⟩,
    ⟨1, 0, .linear 238⟩
]

-- detector1.normChain.15.1.definition
@[expose] def row202 : List (SparseQuartic.Term 318) := [
    ⟨4, 0, .quadratic 124 209⟩,
    ⟨-4, 0, .quadratic 138 209⟩,
    ⟨-2, 0, .quadratic 236 237⟩,
    ⟨1, 0, .linear 239⟩
]

-- detector1.normOver2w0.definition
@[expose] def row203 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 238 238⟩,
    ⟨-2, 0, .quadratic 238 240⟩,
    ⟨-2, 0, .quadratic 239 239⟩
]

-- detector1.B.definition
@[expose] def row204 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 201 241⟩,
    ⟨-1, 0, .quadratic 204 241⟩,
    ⟨1, 0, .quadratic 240 240⟩
]

-- detector1.normalizedH.definition
@[expose] def row205 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 43 241⟩,
    ⟨-1, 0, .linear 242⟩
]

-- detector1.normalizedS2.definition
@[expose] def row206 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 44 44⟩,
    ⟨-1, 0, .linear 243⟩
]

-- detector1.firstConic
@[expose] def row207 : List (SparseQuartic.Term 318) := [
    ⟨3, 0, .quadratic 43 242⟩,
    ⟨17, 0, .quadratic 45 45⟩,
    ⟨-289, 0, .linear 241⟩,
    ⟨-34, 0, .linear 242⟩
]

-- detector1.normalizedProduct.definition
@[expose] def row208 : List (SparseQuartic.Term 318) := [
    ⟨867, 0, .quadratic 43 43⟩,
    ⟨-102, 0, .quadratic 43 242⟩,
    ⟨-34, 0, .quadratic 43 243⟩,
    ⟨3, 0, .quadratic 242 242⟩,
    ⟨2, 0, .quadratic 242 243⟩,
    ⟨-1, 0, .quadratic 243 243⟩,
    ⟨-3, 0, .linear 244⟩
]

-- detector1.secondConic
@[expose] def row209 : List (SparseQuartic.Term 318) := [
    ⟨17, 0, .quadratic 46 46⟩,
    ⟨3, 0, .quadratic 241 244⟩
]

-- detector2.t.definition
@[expose] def row210 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 145 145⟩,
    ⟨-16777216, 0, .quadratic 146 245⟩
]

-- detector2.Fsquare.definition
@[expose] def row211 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 245 245⟩,
    ⟨-1, 0, .linear 246⟩
]

-- detector2.Fmiddle.definition
@[expose] def row212 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 245 246⟩,
    ⟨-1, 0, .linear 247⟩
]

-- detector2.F.definition
@[expose] def row213 : List (SparseQuartic.Term 318) := [
    ⟨1205412, 0, .quadratic 245 246⟩,
    ⟨3081901, 0, .quadratic 246 246⟩,
    ⟨1952786, 0, .quadratic 246 247⟩,
    ⟨-1205412, 0, .linear 248⟩
]

-- detector2.Adelta.definition
@[expose] def row214 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 146 245⟩,
    ⟨-1, 0, .quadratic 146 246⟩,
    ⟨-1, 0, .linear 249⟩
]

-- detector2.Adelta4.half.square.definition
@[expose] def row215 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 249 249⟩,
    ⟨-1, 0, .linear 250⟩
]

-- detector2.Adelta4.square.definition
@[expose] def row216 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 250 250⟩,
    ⟨-1, 0, .linear 251⟩
]

-- detector2.eWeight.definition
@[expose] def row217 : List (SparseQuartic.Term 318) := [
    ⟨32, 0, .quadratic 245 252⟩,
    ⟨-76265, 0, .quadratic 246 252⟩,
    ⟨-1205412, 0, .quadratic 248 252⟩,
    ⟨-1952786, 0, .quadratic 249 251⟩
]

-- detector2.delta3.definition
@[expose] def row218 : List (SparseQuartic.Term 318) := [
    ⟨2, 0, .quadratic 245 245⟩,
    ⟨-1, 0, .quadratic 245 246⟩,
    ⟨-2, 0, .linear 253⟩
]

-- detector2.q1.definition
@[expose] def row219 : List (SparseQuartic.Term 318) := [
    ⟨3, 0, .quadratic 245 254⟩,
    ⟨-1, 0, .quadratic 246 254⟩,
    ⟨-1, 0, .linear 252⟩,
    ⟨-2, 0, .quadratic 253 254⟩,
    ⟨-1, 0, .linear 254⟩
]

-- detector2.eDelta.definition
@[expose] def row220 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 245 252⟩,
    ⟨-1, 0, .linear 255⟩
]

-- detector2.e2.definition
@[expose] def row221 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 252 252⟩,
    ⟨-1, 0, .linear 256⟩
]

-- detector2.e4OverDelta.definition
@[expose] def row222 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 245 257⟩,
    ⟨-1, 0, .quadratic 256 256⟩,
    ⟨-1, 0, .linear 257⟩
]

-- detector2.q4.definition
@[expose] def row223 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 252 258⟩,
    ⟨-1, 0, .quadratic 255 258⟩,
    ⟨1, 0, .quadratic 257 257⟩
]

-- detector2.q7.definition
@[expose] def row224 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 254 259⟩,
    ⟨-1, 0, .quadratic 258 258⟩
]

-- detector2.q13.definition
@[expose] def row225 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 254 260⟩,
    ⟨-1, 0, .quadratic 259 259⟩
]

-- detector2.normChain.0.0.definition
@[expose] def row226 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .one⟩,
    ⟨1, 0, .quadratic 126 258⟩,
    ⟨-1, 0, .linear 261⟩
]

-- detector2.normChain.1.0.definition
@[expose] def row227 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 125 254⟩,
    ⟨1, 0, .quadratic 261 261⟩,
    ⟨-1, 0, .linear 262⟩
]

-- detector2.normChain.2.0.definition
@[expose] def row228 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 58 254⟩,
    ⟨1, 0, .quadratic 262 262⟩,
    ⟨-1, 0, .linear 263⟩
]

-- detector2.normChain.2.1.definition
@[expose] def row229 : List (SparseQuartic.Term 318) := [
    ⟨2, 0, .quadratic 59 254⟩,
    ⟨-1, 0, .linear 264⟩
]

-- detector2.normChain.3.0.definition
@[expose] def row230 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 60 254⟩,
    ⟨1, 0, .quadratic 263 263⟩,
    ⟨2, 0, .quadratic 264 264⟩,
    ⟨-1, 0, .linear 265⟩
]

-- detector2.normChain.3.1.definition
@[expose] def row231 : List (SparseQuartic.Term 318) := [
    ⟨2, 0, .quadratic 61 254⟩,
    ⟨2, 0, .quadratic 263 264⟩,
    ⟨-1, 0, .linear 266⟩
]

-- detector2.normChain.4.0.definition
@[expose] def row232 : List (SparseQuartic.Term 318) := [
    ⟨2, 0, .quadratic 62 254⟩,
    ⟨1, 0, .quadratic 265 265⟩,
    ⟨2, 0, .quadratic 266 266⟩,
    ⟨-1, 0, .linear 267⟩
]

-- detector2.normChain.4.1.definition
@[expose] def row233 : List (SparseQuartic.Term 318) := [
    ⟨2, 0, .quadratic 63 254⟩,
    ⟨2, 0, .quadratic 265 266⟩,
    ⟨-1, 0, .linear 268⟩
]

-- detector2.normChain.5.0.definition
@[expose] def row234 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 64 254⟩,
    ⟨1, 0, .quadratic 267 267⟩,
    ⟨2, 0, .quadratic 268 268⟩,
    ⟨-1, 0, .linear 269⟩
]

-- detector2.normChain.5.1.definition
@[expose] def row235 : List (SparseQuartic.Term 318) := [
    ⟨2, 0, .quadratic 65 254⟩,
    ⟨2, 0, .quadratic 267 268⟩,
    ⟨-1, 0, .linear 270⟩
]

-- detector2.normChain.6.0.definition
@[expose] def row236 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 19 254⟩,
    ⟨-1, 0, .linear 254⟩,
    ⟨1, 0, .quadratic 269 269⟩,
    ⟨2, 0, .quadratic 270 270⟩,
    ⟨-1, 0, .linear 271⟩
]

-- detector2.normChain.6.1.definition
@[expose] def row237 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 20 254⟩,
    ⟨-2, 0, .quadratic 269 270⟩,
    ⟨1, 0, .linear 272⟩
]

-- detector2.normChain.7.0.definition
@[expose] def row238 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 23 254⟩,
    ⟨-1, 0, .linear 254⟩,
    ⟨1, 0, .quadratic 271 271⟩,
    ⟨2, 0, .quadratic 272 272⟩,
    ⟨-1, 0, .linear 273⟩
]

-- detector2.normChain.7.1.definition
@[expose] def row239 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 24 254⟩,
    ⟨-2, 0, .quadratic 271 272⟩,
    ⟨1, 0, .linear 274⟩
]

-- detector2.normChain.8.0.definition
@[expose] def row240 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 27 254⟩,
    ⟨-1, 0, .linear 254⟩,
    ⟨1, 0, .quadratic 273 273⟩,
    ⟨2, 0, .quadratic 274 274⟩,
    ⟨-1, 0, .linear 275⟩
]

-- detector2.normChain.8.1.definition
@[expose] def row241 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 28 254⟩,
    ⟨-2, 0, .quadratic 273 274⟩,
    ⟨1, 0, .linear 276⟩
]

-- detector2.normChain.9.0.definition
@[expose] def row242 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 31 254⟩,
    ⟨-1, 0, .linear 254⟩,
    ⟨1, 0, .quadratic 275 275⟩,
    ⟨2, 0, .quadratic 276 276⟩,
    ⟨-1, 0, .linear 277⟩
]

-- detector2.normChain.9.1.definition
@[expose] def row243 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 32 254⟩,
    ⟨-2, 0, .quadratic 275 276⟩,
    ⟨1, 0, .linear 278⟩
]

-- detector2.normChain.10.0.definition
@[expose] def row244 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 127 258⟩,
    ⟨1, 0, .quadratic 277 277⟩,
    ⟨2, 0, .quadratic 278 278⟩,
    ⟨-1, 0, .linear 279⟩
]

-- detector2.normChain.10.1.definition
@[expose] def row245 : List (SparseQuartic.Term 318) := [
    ⟨2, 0, .quadratic 128 258⟩,
    ⟨2, 0, .quadratic 277 278⟩,
    ⟨-1, 0, .linear 280⟩
]

-- detector2.normChain.11.0.definition
@[expose] def row246 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 129 260⟩,
    ⟨1, 0, .quadratic 279 279⟩,
    ⟨2, 0, .quadratic 280 280⟩,
    ⟨-1, 0, .linear 281⟩
]

-- detector2.normChain.11.1.definition
@[expose] def row247 : List (SparseQuartic.Term 318) := [
    ⟨2, 0, .quadratic 130 260⟩,
    ⟨2, 0, .quadratic 279 280⟩,
    ⟨-1, 0, .linear 282⟩
]

-- detector2.normChain.12.0.definition
@[expose] def row248 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 131 260⟩,
    ⟨1, 0, .quadratic 281 281⟩,
    ⟨2, 0, .quadratic 282 282⟩,
    ⟨-1, 0, .linear 283⟩
]

-- detector2.normChain.12.1.definition
@[expose] def row249 : List (SparseQuartic.Term 318) := [
    ⟨2, 0, .quadratic 132 260⟩,
    ⟨2, 0, .quadratic 281 282⟩,
    ⟨-1, 0, .linear 284⟩
]

-- detector2.normChain.13.0.definition
@[expose] def row250 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 133 260⟩,
    ⟨1, 0, .quadratic 283 283⟩,
    ⟨2, 0, .quadratic 284 284⟩,
    ⟨-1, 0, .linear 285⟩
]

-- detector2.normChain.13.1.definition
@[expose] def row251 : List (SparseQuartic.Term 318) := [
    ⟨2, 0, .quadratic 134 260⟩,
    ⟨2, 0, .quadratic 283 284⟩,
    ⟨-1, 0, .linear 286⟩
]

-- detector2.normChain.14.0.definition
@[expose] def row252 : List (SparseQuartic.Term 318) := [
    ⟨110885832, 0, .quadratic 0 258⟩,
    ⟨-7446, 0, .quadratic 102 258⟩,
    ⟨110885832, 0, .quadratic 118 258⟩,
    ⟨221771664, 0, .quadratic 135 258⟩,
    ⟨13860729, 0, .linear 258⟩,
    ⟨1, 0, .quadratic 285 285⟩,
    ⟨2, 0, .quadratic 286 286⟩,
    ⟨-1, 0, .linear 287⟩
]

-- detector2.normChain.14.1.definition
@[expose] def row253 : List (SparseQuartic.Term 318) := [
    ⟨7446, 0, .quadratic 103 258⟩,
    ⟨29784, 0, .quadratic 136 258⟩,
    ⟨-2, 0, .quadratic 285 286⟩,
    ⟨1, 0, .linear 288⟩
]

-- detector2.normChain.15.0.definition
@[expose] def row254 : List (SparseQuartic.Term 318) := [
    ⟨2, 0, .quadratic 123 260⟩,
    ⟨-1, 0, .quadratic 137 260⟩,
    ⟨-1, 0, .linear 260⟩,
    ⟨-1, 0, .quadratic 287 287⟩,
    ⟨-2, 0, .quadratic 288 288⟩,
    ⟨1, 0, .linear 289⟩
]

-- detector2.normChain.15.1.definition
@[expose] def row255 : List (SparseQuartic.Term 318) := [
    ⟨4, 0, .quadratic 124 260⟩,
    ⟨-4, 0, .quadratic 138 260⟩,
    ⟨-2, 0, .quadratic 287 288⟩,
    ⟨1, 0, .linear 290⟩
]

-- detector2.normOver2w0.definition
@[expose] def row256 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 289 289⟩,
    ⟨-2, 0, .quadratic 289 291⟩,
    ⟨-2, 0, .quadratic 290 290⟩
]

-- detector2.B.definition
@[expose] def row257 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 252 292⟩,
    ⟨-1, 0, .quadratic 255 292⟩,
    ⟨1, 0, .quadratic 291 291⟩
]

-- detector2.normalizedH.definition
@[expose] def row258 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 47 292⟩,
    ⟨-1, 0, .linear 293⟩
]

-- detector2.normalizedS2.definition
@[expose] def row259 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 48 48⟩,
    ⟨-1, 0, .linear 294⟩
]

-- detector2.firstConic
@[expose] def row260 : List (SparseQuartic.Term 318) := [
    ⟨3, 0, .quadratic 47 293⟩,
    ⟨17, 0, .quadratic 49 49⟩,
    ⟨-289, 0, .linear 292⟩,
    ⟨-34, 0, .linear 293⟩
]

-- detector2.normalizedProduct.definition
@[expose] def row261 : List (SparseQuartic.Term 318) := [
    ⟨867, 0, .quadratic 47 47⟩,
    ⟨-102, 0, .quadratic 47 293⟩,
    ⟨-34, 0, .quadratic 47 294⟩,
    ⟨3, 0, .quadratic 293 293⟩,
    ⟨2, 0, .quadratic 293 294⟩,
    ⟨-1, 0, .quadratic 294 294⟩,
    ⟨-3, 0, .linear 295⟩
]

-- detector2.secondConic
@[expose] def row262 : List (SparseQuartic.Term 318) := [
    ⟨17, 0, .quadratic 50 50⟩,
    ⟨3, 0, .quadratic 292 295⟩
]

-- scalar.rPair1.definition
@[expose] def row263 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 0 0⟩,
    ⟨2, 0, .quadratic 0 118⟩,
    ⟨1, 0, .quadratic 118 118⟩,
    ⟨-1, 0, .linear 296⟩
]

-- scalar.r.definition
@[expose] def row264 : List (SparseQuartic.Term 318) := [
    ⟨100291113, 0, .quadratic 0 0⟩,
    ⟨200582226, 0, .quadratic 0 118⟩,
    ⟨496408687, 0, .quadratic 0 296⟩,
    ⟨100291113, 0, .quadratic 118 118⟩,
    ⟨496408687, 0, .quadratic 118 296⟩,
    ⟨591391104, 0, .quadratic 296 296⟩,
    ⟨-100291113, 0, .linear 297⟩
]

-- scalar.rInverse.definition
@[expose] def row265 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .one⟩,
    ⟨-101783690143177584, 0, .quadratic 0 298⟩,
    ⟨-101783690143177584, 0, .quadratic 118 298⟩,
    ⟨-267108917866935984, 0, .quadratic 296 298⟩,
    ⟨-533801448346128768, 0, .quadratic 297 298⟩,
    ⟨-4376874610839020, 0, .linear 298⟩
]

-- scalar.rInverse16.half.half.half.square.definition
@[expose] def row266 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 298 298⟩,
    ⟨-1, 0, .linear 299⟩
]

-- scalar.rInverse16.half.half.square.definition
@[expose] def row267 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 299 299⟩,
    ⟨-1, 0, .linear 300⟩
]

-- scalar.rInverse16.half.square.definition
@[expose] def row268 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 300 300⟩,
    ⟨-1, 0, .linear 301⟩
]

-- scalar.rInverse16.square.definition
@[expose] def row269 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 301 301⟩,
    ⟨-1, 0, .linear 302⟩
]

-- scalar.shiftedS.rootProduct.0.definition
@[expose] def row270 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 82 303⟩,
    ⟨2, 0, .quadratic 83 304⟩,
    ⟨-1, 0, .linear 305⟩
]

-- scalar.shiftedS.rootProduct.1.definition
@[expose] def row271 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 82 304⟩,
    ⟨1, 0, .quadratic 83 303⟩,
    ⟨-1, 0, .linear 306⟩
]

-- scalar.shiftedS.kummerEquation.0
@[expose] def row272 : List (SparseQuartic.Term 318) := [
    ⟨88, 0, .one⟩,
    ⟨57, 0, .quadratic 82 82⟩,
    ⟨-112, 0, .quadratic 82 83⟩,
    ⟨114, 0, .quadratic 83 83⟩,
    ⟨57, 0, .quadratic 303 303⟩,
    ⟨-112, 0, .quadratic 303 304⟩,
    ⟨114, 0, .quadratic 304 304⟩,
    ⟨78, 0, .linear 305⟩,
    ⟨-8, 0, .quadratic 305 305⟩,
    ⟨-144, 0, .linear 306⟩,
    ⟨-16, 0, .quadratic 306 306⟩
]

-- scalar.shiftedS.kummerEquation.1
@[expose] def row273 : List (SparseQuartic.Term 318) := [
    ⟨24, 0, .one⟩,
    ⟨14, 0, .quadratic 82 82⟩,
    ⟨-57, 0, .quadratic 82 83⟩,
    ⟨28, 0, .quadratic 83 83⟩,
    ⟨14, 0, .quadratic 303 303⟩,
    ⟨-57, 0, .quadratic 303 304⟩,
    ⟨28, 0, .quadratic 304 304⟩,
    ⟨36, 0, .linear 305⟩,
    ⟨8, 0, .quadratic 305 306⟩,
    ⟨-39, 0, .linear 306⟩
]

-- scalar.rootNormR.definition
@[expose] def row274 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 303 303⟩,
    ⟨-2, 0, .quadratic 304 304⟩,
    ⟨-1, 0, .linear 307⟩
]

-- scalar.normUR.definition
@[expose] def row275 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .one⟩,
    ⟨1, 1, .quadratic 145 307⟩,
    ⟨-1, 0, .quadratic 307 308⟩
]

-- scalar.scaledNormUH.definition
@[expose] def row276 : List (SparseQuartic.Term 318) := [
    ⟨101783690143177584, 0, .quadratic 0 309⟩,
    ⟨-1, 0, .linear 37⟩,
    ⟨101783690143177584, 0, .quadratic 118 309⟩,
    ⟨267108917866935984, 0, .quadratic 296 309⟩,
    ⟨533801448346128768, 0, .quadratic 297 309⟩,
    ⟨4376874610839020, 0, .linear 309⟩
]

-- scalar.normalizedNormRatio.definition
@[expose] def row277 : List (SparseQuartic.Term 318) := [
    ⟨1, 1, .quadratic 145 302⟩,
    ⟨-1, 0, .quadratic 302 308⟩,
    ⟨1, 0, .quadratic 309 310⟩
]

-- scalar.packedNormH.definition
@[expose] def row278 : List (SparseQuartic.Term 318) := [
    ⟨2, 0, .quadratic 33 298⟩,
    ⟨1, 0, .quadratic 309 309⟩,
    ⟨-1, 0, .linear 311⟩
]

-- scalar.normRatioSquare.definition
@[expose] def row279 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 310 310⟩,
    ⟨-1, 0, .linear 312⟩
]

-- scalar.normalizedW.definition
@[expose] def row280 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .one⟩,
    ⟨101783690143177584, 0, .quadratic 0 312⟩,
    ⟨-11648532634745815423296, 0, .quadratic 0 313⟩,
    ⟨101783690143177584, 0, .quadratic 118 312⟩,
    ⟨-11648532634745815423296, 0, .quadratic 118 313⟩,
    ⟨267108917866935984, 0, .quadratic 296 312⟩,
    ⟨-30569012996363621752896, 0, .quadratic 296 313⟩,
    ⟨533801448346128768, 0, .quadratic 297 312⟩,
    ⟨-61090372954524360724992, 0, .quadratic 297 313⟩,
    ⟨2, 0, .linear 311⟩,
    ⟨1, 0, .quadratic 311 311⟩,
    ⟨4376874610839020, 0, .linear 312⟩,
    ⟨-500907037962860804881, 0, .linear 313⟩
]

-- scalar.b.definition
@[expose] def row281 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 298 314⟩,
    ⟨-114444, 0, .quadratic 313 313⟩
]

-- scalar.zeroW.definition
@[expose] def row282 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 51 314⟩,
    ⟨-1, 0, .linear 315⟩
]

-- scalar.scaledS2.definition
@[expose] def row283 : List (SparseQuartic.Term 318) := [
    ⟨1, 0, .quadratic 52 52⟩,
    ⟨-1, 0, .linear 316⟩
]

-- scalar.scaledProduct.definition
@[expose] def row284 : List (SparseQuartic.Term 318) := [
    ⟨867, 0, .quadratic 51 51⟩,
    ⟨-102, 0, .quadratic 51 315⟩,
    ⟨-34, 0, .quadratic 51 316⟩,
    ⟨3, 0, .quadratic 315 315⟩,
    ⟨2, 0, .quadratic 315 316⟩,
    ⟨-1, 0, .quadratic 316 316⟩,
    ⟨-3, 0, .linear 317⟩
]

-- scalar.firstConic
@[expose] def row285 : List (SparseQuartic.Term 318) := [
    ⟨3, 0, .quadratic 51 315⟩,
    ⟨17, 0, .quadratic 53 53⟩,
    ⟨-289, 0, .linear 314⟩,
    ⟨-34, 0, .linear 315⟩
]

-- scalar.secondConic
@[expose] def row286 : List (SparseQuartic.Term 318) := [
    ⟨17, 0, .quadratic 54 54⟩,
    ⟨3, 0, .quadratic 314 317⟩
]

-- anchor.translatedEquation
@[expose] def row287 : List (SparseQuartic.Term 318) := [
    ⟨8, 1, .linear 55⟩,
    ⟨1, 0, .quadratic 55 55⟩,
    ⟨-6, 0, .quadratic 55 56⟩,
    ⟨6, 0, .quadratic 55 57⟩,
    ⟨15, 0, .quadratic 56 56⟩,
    ⟨-18, 0, .quadratic 56 57⟩,
    ⟨7, 0, .quadratic 57 57⟩,
    ⟨-48, 0, .quadratic 308 308⟩
]

@[expose] def rows : List (List (SparseQuartic.Term 318)) := [row0, row1, row2, row3, row4, row5, row6, row7, row8, row9, row10, row11, row12, row13, row14, row15, row16, row17, row18, row19, row20, row21, row22, row23, row24, row25, row26, row27, row28, row29, row30, row31, row32, row33, row34, row35, row36, row37, row38, row39, row40, row41, row42, row43, row44, row45, row46, row47, row48, row49, row50, row51, row52, row53, row54, row55, row56, row57, row58, row59, row60, row61, row62, row63, row64, row65, row66, row67, row68, row69, row70, row71, row72, row73, row74, row75, row76, row77, row78, row79, row80, row81, row82, row83, row84, row85, row86, row87, row88, row89, row90, row91, row92, row93, row94, row95, row96, row97, row98, row99, row100, row101, row102, row103, row104, row105, row106, row107, row108, row109, row110, row111, row112, row113, row114, row115, row116, row117, row118, row119, row120, row121, row122, row123, row124, row125, row126, row127, row128, row129, row130, row131, row132, row133, row134, row135, row136, row137, row138, row139, row140, row141, row142, row143, row144, row145, row146, row147, row148, row149, row150, row151, row152, row153, row154, row155, row156, row157, row158, row159, row160, row161, row162, row163, row164, row165, row166, row167, row168, row169, row170, row171, row172, row173, row174, row175, row176, row177, row178, row179, row180, row181, row182, row183, row184, row185, row186, row187, row188, row189, row190, row191, row192, row193, row194, row195, row196, row197, row198, row199, row200, row201, row202, row203, row204, row205, row206, row207, row208, row209, row210, row211, row212, row213, row214, row215, row216, row217, row218, row219, row220, row221, row222, row223, row224, row225, row226, row227, row228, row229, row230, row231, row232, row233, row234, row235, row236, row237, row238, row239, row240, row241, row242, row243, row244, row245, row246, row247, row248, row249, row250, row251, row252, row253, row254, row255, row256, row257, row258, row259, row260, row261, row262, row263, row264, row265, row266, row267, row268, row269, row270, row271, row272, row273, row274, row275, row276, row277, row278, row279, row280, row281, row282, row283, row284, row285, row286, row287]

def scale : ℤ := 3^(2^16)

@[expose] noncomputable def P : MvPolynomial (Fin 318) ℤ := SparseQuartic.polynomial scale rows

theorem row_count : rows.length = 288 := by decide

theorem coordinate_degree_le_four : P.totalDegree ≤ 4 := SparseQuartic.polynomial_degree scale rows

theorem zero_iff_constraints (w : Fin 318 → ℚ) :
    MvPolynomial.eval₂Hom (Int.castRingHom ℚ) w P = 0 ↔ SparseQuartic.Constraints scale rows w :=
  SparseQuartic.polynomial_zero_iff scale rows w

theorem input_projection_iff (q : ℚ) :
    (∃ w : Fin 317 → ℚ, MvPolynomial.eval₂Hom (Int.castRingHom ℚ) (Fin.cons q w) P = 0) ↔
    ∃ w : Fin 317 → ℚ, SparseQuartic.Constraints scale rows (Fin.cons q w) :=
  SparseQuartic.polynomial_witnesses_iff scale rows q

/-- This theorem explicitly requires the arithmetic characterization of the
concrete source residuals. The hypothesis is NOT proved in this module. -/
theorem defines_integers_of_source
    (source : ∀ q : ℚ, (∃ w : Fin 317 → ℚ, SparseQuartic.Constraints scale rows (Fin.cons q w)) ↔
      ∃ z : ℤ, (z : ℚ) = q) :
    ∀ q : ℚ, (∃ w : Fin 317 → ℚ, MvPolynomial.eval₂Hom (Int.castRingHom ℚ) (Fin.cons q w) P = 0) ↔
      ∃ z : ℤ, (z : ℚ) = q := by
  intro q
  exact (input_projection_iff q).trans (source q)

end Current318FinalPolynomial
