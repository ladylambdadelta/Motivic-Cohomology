import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.SectorialLog.PowerNorm
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.SectorialLog.VerticalStripGeometry

/-!
# Vertical recurrence: sectorial support lemmas

This file owns the small shifted-strip support facts shared by the sectorial
Stirling transport and the shifted denominator comparison.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

/-- The deterministic transport shift moves the strip into the closed right
half-plane. -/
theorem Complex.verticalStripTransportShift_closedRightHalfPlaneSector
    {A x y : ℝ}
    (hx : A ≤ x) :
    Complex.closedRightHalfPlaneSector
      (Complex.fixedRealPartVerticalPoint
        (x + Complex.verticalStripTransportShift A) y) := by
  exact
    Complex.fixedRealPartVerticalPoint_verticalStripRightShift_closedRightHalfPlaneSector
      hx

/-- The deterministic transport shift moves the strip into the strict right
half-plane. -/
theorem Complex.verticalStripTransportShift_re_pos
    {A x y : ℝ}
    (hx : A ≤ x) :
    0 <
      (Complex.fixedRealPartVerticalPoint
        (x + Complex.verticalStripTransportShift A) y).re := by
  exact
    Complex.fixedRealPartVerticalPoint_verticalStripRightShift_re_pos
      hx

/-- Large vertical height gives the sectorial radius cutoff after the
deterministic transport shift. -/
theorem Complex.verticalStripTransportShift_radius_ge_of_height_ge
    {A x y H : ℝ}
    (hH : H ≤ ‖y‖) :
    H ≤
      ‖Complex.fixedRealPartVerticalPoint
        (x + Complex.verticalStripTransportShift A) y‖ := by
  exact
    Complex.fixedRealPartVerticalPoint_verticalStripRightShift_radius_ge_of_height_ge
      hH

/-- Positivity of the exponential/power denominator in normalized Stirling away
from the origin. -/
theorem Complex.stirlingDenominator_pos_of_ne_zero
    {w : ℂ}
    (hw_ne : w ≠ 0) :
    0 < ‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖ := by
  have hexp_pos : 0 < ‖Complex.exp w‖ :=
    norm_pos_iff.mpr (Complex.exp_ne_zero w)
  have hcpow_ne : w ^ ((1 / 2 : ℂ) - w) ≠ 0 := by
    intro hzero
    have hbase_zero : w = 0 :=
      ((Complex.cpow_eq_zero_iff w ((1 / 2 : ℂ) - w)).mp hzero).1
    exact hw_ne hbase_zero
  have hcpow_pos : 0 < ‖w ^ ((1 / 2 : ℂ) - w)‖ :=
    norm_pos_iff.mpr hcpow_ne
  exact mul_pos hexp_pos hcpow_pos

end

end LFunctions
end Boundary
