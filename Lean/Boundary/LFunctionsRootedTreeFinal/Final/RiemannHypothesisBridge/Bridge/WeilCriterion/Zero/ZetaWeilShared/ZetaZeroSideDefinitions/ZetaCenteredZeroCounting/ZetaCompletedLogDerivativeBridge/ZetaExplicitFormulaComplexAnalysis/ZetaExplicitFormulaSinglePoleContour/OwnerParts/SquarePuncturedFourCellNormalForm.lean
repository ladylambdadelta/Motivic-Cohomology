import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaSinglePoleContour.OwnerParts.SquarePuncturedBoundaryAlgebra

/-!
# Four-cell normal forms for the one-pole square-punctured boundary

This file records the explicit four-cell normal form used to compare the cell
boundary sum with the exposed outer-minus-inner edge expression.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The named four-cell boundary sum unfolds to the four oriented cell boundary
groups in the geometric order bottom, top, left, right. -/
theorem zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum_eq_groupedEdges
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ) :
    zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum g F T R =
    ((∫ x : ℝ in (1 - F.c)..F.c, g (x + ((-T : ℝ) : ℂ) * Complex.I)) -
        (∫ x : ℝ in (1 - F.c)..F.c, g (x + ((-R : ℝ) : ℂ) * Complex.I)) +
          Complex.I •
            (∫ y : ℝ in -T..(-R), g (F.c + y * Complex.I)) -
            Complex.I •
              (∫ y : ℝ in -T..(-R), g (((1 - F.c : ℝ) : ℂ) + y * Complex.I))) +
        ((∫ x : ℝ in (1 - F.c)..F.c, g (x + R * Complex.I)) -
          (∫ x : ℝ in (1 - F.c)..F.c, g (x + T * Complex.I)) +
            Complex.I •
              (∫ y : ℝ in R..T, g (F.c + y * Complex.I)) -
              Complex.I •
                (∫ y : ℝ in R..T, g (((1 - F.c : ℝ) : ℂ) + y * Complex.I))) +
          ((∫ x : ℝ in (1 - F.c)..(1 - R), g (x + ((-R : ℝ) : ℂ) * Complex.I)) -
            (∫ x : ℝ in (1 - F.c)..(1 - R), g (x + R * Complex.I)) +
              Complex.I •
                (∫ y : ℝ in -R..R, g (((1 - R : ℝ) : ℂ) + y * Complex.I)) -
                Complex.I •
                  (∫ y : ℝ in -R..R, g (((1 - F.c : ℝ) : ℂ) + y * Complex.I))) +
            ((∫ x : ℝ in (1 + R)..F.c, g (x + ((-R : ℝ) : ℂ) * Complex.I)) -
              (∫ x : ℝ in (1 + R)..F.c, g (x + R * Complex.I)) +
                Complex.I •
                  (∫ y : ℝ in -R..R, g (F.c + y * Complex.I)) -
                  Complex.I •
                    (∫ y : ℝ in -R..R, g (((1 + R : ℝ) : ℂ) + y * Complex.I))) := by
  exact zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum_eq_expandedCells
    g F T R

/-- The four-cell boundary sum expressed with the inner bottom and top
horizontal edges already split into left, center, and right pieces. -/
theorem zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum_eq_splitHorizontalEdges
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ)
    (hbottom :
      (∫ x : ℝ in (1 - F.c)..F.c, g (x + ((-R : ℝ) : ℂ) * Complex.I)) =
        ((∫ x : ℝ in (1 - F.c)..(1 - R), g (x + ((-R : ℝ) : ℂ) * Complex.I)) +
          (∫ x : ℝ in (1 - R)..(1 + R), g (x + ((-R : ℝ) : ℂ) * Complex.I))) +
            (∫ x : ℝ in (1 + R)..F.c, g (x + ((-R : ℝ) : ℂ) * Complex.I)))
    (htop :
      (∫ x : ℝ in (1 - F.c)..F.c, g (x + R * Complex.I)) =
        ((∫ x : ℝ in (1 - F.c)..(1 - R), g (x + R * Complex.I)) +
          (∫ x : ℝ in (1 - R)..(1 + R), g (x + R * Complex.I))) +
            (∫ x : ℝ in (1 + R)..F.c, g (x + R * Complex.I))) :
    zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum g F T R =
      ((∫ x : ℝ in (1 - F.c)..F.c, g (x + ((-T : ℝ) : ℂ) * Complex.I)) -
        (((∫ x : ℝ in (1 - F.c)..(1 - R), g (x + ((-R : ℝ) : ℂ) * Complex.I)) +
          (∫ x : ℝ in (1 - R)..(1 + R), g (x + ((-R : ℝ) : ℂ) * Complex.I))) +
            (∫ x : ℝ in (1 + R)..F.c, g (x + ((-R : ℝ) : ℂ) * Complex.I))) +
          Complex.I •
            (∫ y : ℝ in -T..(-R), g (F.c + y * Complex.I)) -
            Complex.I •
              (∫ y : ℝ in -T..(-R), g (((1 - F.c : ℝ) : ℂ) + y * Complex.I))) +
        (((∫ x : ℝ in (1 - F.c)..(1 - R), g (x + R * Complex.I)) +
          (∫ x : ℝ in (1 - R)..(1 + R), g (x + R * Complex.I))) +
            (∫ x : ℝ in (1 + R)..F.c, g (x + R * Complex.I)) -
          (∫ x : ℝ in (1 - F.c)..F.c, g (x + T * Complex.I)) +
            Complex.I •
              (∫ y : ℝ in R..T, g (F.c + y * Complex.I)) -
              Complex.I •
                (∫ y : ℝ in R..T, g (((1 - F.c : ℝ) : ℂ) + y * Complex.I))) +
          ((∫ x : ℝ in (1 - F.c)..(1 - R), g (x + ((-R : ℝ) : ℂ) * Complex.I)) -
            (∫ x : ℝ in (1 - F.c)..(1 - R), g (x + R * Complex.I)) +
              Complex.I •
                (∫ y : ℝ in -R..R, g (((1 - R : ℝ) : ℂ) + y * Complex.I)) -
                Complex.I •
                  (∫ y : ℝ in -R..R, g (((1 - F.c : ℝ) : ℂ) + y * Complex.I))) +
            ((∫ x : ℝ in (1 + R)..F.c, g (x + ((-R : ℝ) : ℂ) * Complex.I)) -
              (∫ x : ℝ in (1 + R)..F.c, g (x + R * Complex.I)) +
                Complex.I •
                  (∫ y : ℝ in -R..R, g (F.c + y * Complex.I)) -
                  Complex.I •
                    (∫ y : ℝ in -R..R, g (((1 + R : ℝ) : ℂ) + y * Complex.I))) := by
  have hgrouped :
      zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum g F T R =
        ((∫ x : ℝ in (1 - F.c)..F.c, g (x + ((-T : ℝ) : ℂ) * Complex.I)) -
          (∫ x : ℝ in (1 - F.c)..F.c, g (x + ((-R : ℝ) : ℂ) * Complex.I)) +
            Complex.I •
              (∫ y : ℝ in -T..(-R), g (F.c + y * Complex.I)) -
              Complex.I •
                (∫ y : ℝ in -T..(-R), g (((1 - F.c : ℝ) : ℂ) + y * Complex.I))) +
          ((∫ x : ℝ in (1 - F.c)..F.c, g (x + R * Complex.I)) -
            (∫ x : ℝ in (1 - F.c)..F.c, g (x + T * Complex.I)) +
              Complex.I •
                (∫ y : ℝ in R..T, g (F.c + y * Complex.I)) -
                Complex.I •
                  (∫ y : ℝ in R..T, g (((1 - F.c : ℝ) : ℂ) + y * Complex.I))) +
            ((∫ x : ℝ in (1 - F.c)..(1 - R), g (x + ((-R : ℝ) : ℂ) * Complex.I)) -
              (∫ x : ℝ in (1 - F.c)..(1 - R), g (x + R * Complex.I)) +
                Complex.I •
                  (∫ y : ℝ in -R..R, g (((1 - R : ℝ) : ℂ) + y * Complex.I)) -
                  Complex.I •
                    (∫ y : ℝ in -R..R, g (((1 - F.c : ℝ) : ℂ) + y * Complex.I))) +
              ((∫ x : ℝ in (1 + R)..F.c, g (x + ((-R : ℝ) : ℂ) * Complex.I)) -
                (∫ x : ℝ in (1 + R)..F.c, g (x + R * Complex.I)) +
                  Complex.I •
                    (∫ y : ℝ in -R..R, g (F.c + y * Complex.I)) -
                    Complex.I •
                      (∫ y : ℝ in -R..R, g (((1 + R : ℝ) : ℂ) + y * Complex.I))) :=
    zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum_eq_groupedEdges
      g F T R
  calc
    zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum g F T R =
        ((∫ x : ℝ in (1 - F.c)..F.c, g (x + ((-T : ℝ) : ℂ) * Complex.I)) -
          (∫ x : ℝ in (1 - F.c)..F.c, g (x + ((-R : ℝ) : ℂ) * Complex.I)) +
            Complex.I •
              (∫ y : ℝ in -T..(-R), g (F.c + y * Complex.I)) -
              Complex.I •
                (∫ y : ℝ in -T..(-R), g (((1 - F.c : ℝ) : ℂ) + y * Complex.I))) +
          ((∫ x : ℝ in (1 - F.c)..F.c, g (x + R * Complex.I)) -
            (∫ x : ℝ in (1 - F.c)..F.c, g (x + T * Complex.I)) +
              Complex.I •
                (∫ y : ℝ in R..T, g (F.c + y * Complex.I)) -
                Complex.I •
                  (∫ y : ℝ in R..T, g (((1 - F.c : ℝ) : ℂ) + y * Complex.I))) +
            ((∫ x : ℝ in (1 - F.c)..(1 - R), g (x + ((-R : ℝ) : ℂ) * Complex.I)) -
              (∫ x : ℝ in (1 - F.c)..(1 - R), g (x + R * Complex.I)) +
                Complex.I •
                  (∫ y : ℝ in -R..R, g (((1 - R : ℝ) : ℂ) + y * Complex.I)) -
                  Complex.I •
                    (∫ y : ℝ in -R..R, g (((1 - F.c : ℝ) : ℂ) + y * Complex.I))) +
              ((∫ x : ℝ in (1 + R)..F.c, g (x + ((-R : ℝ) : ℂ) * Complex.I)) -
                (∫ x : ℝ in (1 + R)..F.c, g (x + R * Complex.I)) +
                  Complex.I •
                    (∫ y : ℝ in -R..R, g (F.c + y * Complex.I)) -
                    Complex.I •
                      (∫ y : ℝ in -R..R, g (((1 + R : ℝ) : ℂ) + y * Complex.I))) :=
      hgrouped
    _ =
      ((∫ x : ℝ in (1 - F.c)..F.c, g (x + ((-T : ℝ) : ℂ) * Complex.I)) -
        (((∫ x : ℝ in (1 - F.c)..(1 - R), g (x + ((-R : ℝ) : ℂ) * Complex.I)) +
          (∫ x : ℝ in (1 - R)..(1 + R), g (x + ((-R : ℝ) : ℂ) * Complex.I))) +
            (∫ x : ℝ in (1 + R)..F.c, g (x + ((-R : ℝ) : ℂ) * Complex.I))) +
          Complex.I •
            (∫ y : ℝ in -T..(-R), g (F.c + y * Complex.I)) -
            Complex.I •
              (∫ y : ℝ in -T..(-R), g (((1 - F.c : ℝ) : ℂ) + y * Complex.I))) +
        (((∫ x : ℝ in (1 - F.c)..(1 - R), g (x + R * Complex.I)) +
          (∫ x : ℝ in (1 - R)..(1 + R), g (x + R * Complex.I))) +
            (∫ x : ℝ in (1 + R)..F.c, g (x + R * Complex.I)) -
          (∫ x : ℝ in (1 - F.c)..F.c, g (x + T * Complex.I)) +
            Complex.I •
              (∫ y : ℝ in R..T, g (F.c + y * Complex.I)) -
              Complex.I •
                (∫ y : ℝ in R..T, g (((1 - F.c : ℝ) : ℂ) + y * Complex.I))) +
          ((∫ x : ℝ in (1 - F.c)..(1 - R), g (x + ((-R : ℝ) : ℂ) * Complex.I)) -
            (∫ x : ℝ in (1 - F.c)..(1 - R), g (x + R * Complex.I)) +
              Complex.I •
                (∫ y : ℝ in -R..R, g (((1 - R : ℝ) : ℂ) + y * Complex.I)) -
                Complex.I •
                  (∫ y : ℝ in -R..R, g (((1 - F.c : ℝ) : ℂ) + y * Complex.I))) +
            ((∫ x : ℝ in (1 + R)..F.c, g (x + ((-R : ℝ) : ℂ) * Complex.I)) -
              (∫ x : ℝ in (1 + R)..F.c, g (x + R * Complex.I)) +
                Complex.I •
                  (∫ y : ℝ in -R..R, g (F.c + y * Complex.I)) -
                  Complex.I •
                    (∫ y : ℝ in -R..R, g (((1 + R : ℝ) : ℂ) + y * Complex.I))) := by
      have hbottomGroup :
          ((∫ x : ℝ in (1 - F.c)..F.c, g (x + ((-T : ℝ) : ℂ) * Complex.I)) -
              (∫ x : ℝ in (1 - F.c)..F.c, g (x + ((-R : ℝ) : ℂ) * Complex.I)) +
              Complex.I •
                (∫ y : ℝ in -T..(-R), g (F.c + y * Complex.I)) -
              Complex.I •
                (∫ y : ℝ in -T..(-R), g (((1 - F.c : ℝ) : ℂ) + y * Complex.I))) =
            ((∫ x : ℝ in (1 - F.c)..F.c, g (x + ((-T : ℝ) : ℂ) * Complex.I)) -
              (((∫ x : ℝ in (1 - F.c)..(1 - R), g (x + ((-R : ℝ) : ℂ) * Complex.I)) +
                (∫ x : ℝ in (1 - R)..(1 + R), g (x + ((-R : ℝ) : ℂ) * Complex.I))) +
                  (∫ x : ℝ in (1 + R)..F.c, g (x + ((-R : ℝ) : ℂ) * Complex.I))) +
              Complex.I •
                (∫ y : ℝ in -T..(-R), g (F.c + y * Complex.I)) -
              Complex.I •
                (∫ y : ℝ in -T..(-R), g (((1 - F.c : ℝ) : ℂ) + y * Complex.I))) :=
        congrArg
          (fun z : ℂ =>
            (∫ x : ℝ in (1 - F.c)..F.c, g (x + ((-T : ℝ) : ℂ) * Complex.I)) -
              z +
              Complex.I •
                (∫ y : ℝ in -T..(-R), g (F.c + y * Complex.I)) -
              Complex.I •
                (∫ y : ℝ in -T..(-R), g (((1 - F.c : ℝ) : ℂ) + y * Complex.I)))
          hbottom
      have htopGroup :
          ((∫ x : ℝ in (1 - F.c)..F.c, g (x + R * Complex.I)) -
              (∫ x : ℝ in (1 - F.c)..F.c, g (x + T * Complex.I)) +
              Complex.I •
                (∫ y : ℝ in R..T, g (F.c + y * Complex.I)) -
              Complex.I •
                (∫ y : ℝ in R..T, g (((1 - F.c : ℝ) : ℂ) + y * Complex.I))) =
            (((∫ x : ℝ in (1 - F.c)..(1 - R), g (x + R * Complex.I)) +
                (∫ x : ℝ in (1 - R)..(1 + R), g (x + R * Complex.I))) +
                  (∫ x : ℝ in (1 + R)..F.c, g (x + R * Complex.I)) -
              (∫ x : ℝ in (1 - F.c)..F.c, g (x + T * Complex.I)) +
              Complex.I •
                (∫ y : ℝ in R..T, g (F.c + y * Complex.I)) -
              Complex.I •
                (∫ y : ℝ in R..T, g (((1 - F.c : ℝ) : ℂ) + y * Complex.I))) :=
        congrArg
          (fun z : ℂ =>
            z -
              (∫ x : ℝ in (1 - F.c)..F.c, g (x + T * Complex.I)) +
              Complex.I •
                (∫ y : ℝ in R..T, g (F.c + y * Complex.I)) -
              Complex.I •
                (∫ y : ℝ in R..T, g (((1 - F.c : ℝ) : ℂ) + y * Complex.I)))
          htop
      exact congrArg
        (fun z : ℂ =>
          z +
            ((∫ x : ℝ in (1 - F.c)..(1 - R), g (x + ((-R : ℝ) : ℂ) * Complex.I)) -
              (∫ x : ℝ in (1 - F.c)..(1 - R), g (x + R * Complex.I)) +
                Complex.I •
                  (∫ y : ℝ in -R..R, g (((1 - R : ℝ) : ℂ) + y * Complex.I)) -
                Complex.I •
                  (∫ y : ℝ in -R..R, g (((1 - F.c : ℝ) : ℂ) + y * Complex.I))) +
            ((∫ x : ℝ in (1 + R)..F.c, g (x + ((-R : ℝ) : ℂ) * Complex.I)) -
              (∫ x : ℝ in (1 + R)..F.c, g (x + R * Complex.I)) +
                Complex.I •
                  (∫ y : ℝ in -R..R, g (F.c + y * Complex.I)) -
                Complex.I •
                  (∫ y : ℝ in -R..R, g (((1 + R : ℝ) : ℂ) + y * Complex.I))))
        (congrArg₂ Add.add hbottomGroup htopGroup)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
