import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Analytic order lemmas for zeta-side zero multiplicities

This file owns the local analytic-order facts used by the zeta zero-side
multiplicity bookkeeping.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- An analytic zero which is not locally identically zero has positive finite
order. -/
theorem analyticAt_order_toNat_pos_of_zero_not_eventually_zero
    {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z)
    (hz : f z = 0)
    (hnot : ¬ ∀ᶠ w in 𝓝 z, f w = 0) :
    0 < hf.order.toNat := by
  sorry

end

end LFunctions
end Boundary
