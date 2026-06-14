import LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase

/-!
# Reciprocal-density estimates

This file owns the decreasing reciprocal weight `n⁻¹` and its continuum
density in the partial-summation argument.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Reciprocal weights are monotone decreasing along the positive natural tail. -/
theorem positive_nat_reciprocal_antitone
    {m n : ℕ}
    (hm : 0 < m)
    (hmn : m ≤ n) :
    (1 : ℝ) / (n : ℝ) ≤ (1 : ℝ) / (m : ℝ) := by
  have hm_real_pos : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast hm
  have hmn_real : (m : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hmn
  exact one_div_le_one_div_of_le hm_real_pos hmn_real

end

end LFunctions
end Boundary
