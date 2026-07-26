import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Instances.Real
import Mathlib.Data.Real.Basic

/-!
# Finite-window bounds from diagonal-debt summation

This file owns the finite-subtrace transport used by the completed
prime diagonal-debt window proofs.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- A finite nonnegative subtrace is bounded by the sum reconstructed by a
`HasSum` witness. -/
theorem finite_window_sum_le_hasSum_of_nonnegative
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι)
    (u : ι → ℝ)
    (hu : ∀ index : ι, 0 ≤ u index)
    {value : ℝ}
    (hvalue : HasSum u value) :
    (∑ index in s, u index) ≤ value :=
  sum_le_hasSum
    s
    (fun index membership => hu index)
    hvalue

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
