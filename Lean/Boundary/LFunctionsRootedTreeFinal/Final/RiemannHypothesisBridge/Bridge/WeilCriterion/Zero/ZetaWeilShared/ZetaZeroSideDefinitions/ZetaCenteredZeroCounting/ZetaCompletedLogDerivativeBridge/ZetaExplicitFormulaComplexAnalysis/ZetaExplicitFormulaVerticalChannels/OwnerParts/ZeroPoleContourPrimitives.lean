import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaGeometry.Owner

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology Interval

namespace ZetaAdmissibleFunction

/-- The canonical puncture radius around the `s = 0` correction pole.

The radius is half the minimum of the two horizontal margins from `0` to the
vertical contour edges and the vertical height. -/
noncomputable def zetaExplicitFormulaZeroPolePunctureRadius
    (F : ExplicitFormulaContourFamily) (T : ℝ) : ℝ :=
  min (min F.c (F.c - 1)) T / 2

/-- The zero-pole puncture radius is positive at positive height. -/
theorem zetaExplicitFormulaZeroPolePunctureRadius_pos
    (F : ExplicitFormulaContourFamily) {T : ℝ} (hT : 0 < T) :
    0 < zetaExplicitFormulaZeroPolePunctureRadius F T := by
  have hright : 0 < F.c :=
    F.c_pos
  have hleft : 0 < F.c - 1 :=
    sub_pos.mpr F.c_gt_one
  have hhorizontal : 0 < min F.c (F.c - 1) :=
    lt_min hright hleft
  have hall : 0 < min (min F.c (F.c - 1)) T :=
    lt_min hhorizontal hT
  exact half_pos hall

/-- The zero-pole puncture radius is bounded by the right horizontal margin. -/
theorem zetaExplicitFormulaZeroPolePunctureRadius_lt_rightMargin
    (F : ExplicitFormulaContourFamily) {T : ℝ} (hT : 0 < T) :
    zetaExplicitFormulaZeroPolePunctureRadius F T < F.c := by
  have hmin_le : min (min F.c (F.c - 1)) T ≤ F.c :=
    le_trans (min_le_left (min F.c (F.c - 1)) T)
      (min_le_left F.c (F.c - 1))
  have hhalf_le :
      zetaExplicitFormulaZeroPolePunctureRadius F T ≤ F.c / 2 := by
    exact div_le_div_of_nonneg_right hmin_le (show (0 : ℝ) ≤ 2 from zero_le_two)
  have hmargin_pos : 0 < F.c :=
    F.c_pos
  have hhalf_lt : F.c / 2 < F.c := by
    calc
      F.c / 2 < F.c / 1 := by
        exact div_lt_div_of_pos_left hmargin_pos zero_lt_one one_lt_two
      _ = F.c := by
        exact div_one F.c
  exact lt_of_le_of_lt hhalf_le hhalf_lt

/-- The zero-pole puncture radius is bounded by the left horizontal margin. -/
theorem zetaExplicitFormulaZeroPolePunctureRadius_lt_leftMargin
    (F : ExplicitFormulaContourFamily) {T : ℝ} (hT : 0 < T) :
    zetaExplicitFormulaZeroPolePunctureRadius F T < F.c - 1 := by
  have hmin_le : min (min F.c (F.c - 1)) T ≤ F.c - 1 :=
    le_trans (min_le_left (min F.c (F.c - 1)) T)
      (min_le_right F.c (F.c - 1))
  have hhalf_le :
      zetaExplicitFormulaZeroPolePunctureRadius F T ≤ (F.c - 1) / 2 := by
    exact div_le_div_of_nonneg_right hmin_le (show (0 : ℝ) ≤ 2 from zero_le_two)
  have hmargin_pos : 0 < F.c - 1 :=
    sub_pos.mpr F.c_gt_one
  have hhalf_lt : (F.c - 1) / 2 < F.c - 1 := by
    calc
      (F.c - 1) / 2 < (F.c - 1) / 1 := by
        exact div_lt_div_of_pos_left hmargin_pos zero_lt_one one_lt_two
      _ = F.c - 1 := by
        exact div_one (F.c - 1)
  exact lt_of_le_of_lt hhalf_le hhalf_lt

/-- The zero-pole puncture radius is bounded by the vertical height. -/
theorem zetaExplicitFormulaZeroPolePunctureRadius_lt_height
    (F : ExplicitFormulaContourFamily) {T : ℝ} (hT : 0 < T) :
    zetaExplicitFormulaZeroPolePunctureRadius F T < T := by
  have hmin_le : min (min F.c (F.c - 1)) T ≤ T :=
    min_le_right (min F.c (F.c - 1)) T
  have hhalf_le :
      zetaExplicitFormulaZeroPolePunctureRadius F T ≤ T / 2 := by
    exact div_le_div_of_nonneg_right hmin_le (show (0 : ℝ) ≤ 2 from zero_le_two)
  have hhalf_lt : T / 2 < T := by
    calc
      T / 2 < T / 1 := by
        exact div_lt_div_of_pos_left hT zero_lt_one one_lt_two
      _ = T := by
        exact div_one T
  exact lt_of_le_of_lt hhalf_le hhalf_lt

end ZetaAdmissibleFunction

end

end LFunctions
end Boundary
