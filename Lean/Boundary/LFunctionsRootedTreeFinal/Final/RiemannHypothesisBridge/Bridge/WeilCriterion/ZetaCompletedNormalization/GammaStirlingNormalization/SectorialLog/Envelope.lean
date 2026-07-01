import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.SectorialLog.FixedVerticalPoint
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Sectorial log: vertical Stirling envelopes

This subowner contains the fixed-real-part vertical envelope definitions used
by the Gamma Stirling recurrence transport.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

/-- The direct fixed-real-part vertical Stirling envelope. -/
def Complex.fixedRealPartVerticalStirlingEnvelope (a b : ℝ) : ℝ :=
  Real.exp (-(Real.pi / 2) * ‖b‖) * (1 + ‖b‖) ^ (a - 1 / 2)

/-- The fixed-real-part direct Stirling envelope is positive. -/
theorem Complex.fixedRealPartVerticalStirlingEnvelope_pos
    (a b : ℝ) :
    0 < Complex.fixedRealPartVerticalStirlingEnvelope a b := by
  have hbase_pos : 0 < 1 + ‖b‖ :=
    lt_of_lt_of_le zero_lt_one
      (le_add_of_nonneg_right (norm_nonneg b))
  exact mul_pos
    (Real.exp_pos (-(Real.pi / 2) * ‖b‖))
    (Real.rpow_pos_of_pos hbase_pos (a - 1 / 2))

/-- The fixed-real-part direct Stirling envelope is nonnegative. -/
theorem Complex.fixedRealPartVerticalStirlingEnvelope_nonneg
    (a b : ℝ) :
    0 ≤ Complex.fixedRealPartVerticalStirlingEnvelope a b :=
  le_of_lt (Complex.fixedRealPartVerticalStirlingEnvelope_pos a b)

end

end LFunctions
end Boundary
