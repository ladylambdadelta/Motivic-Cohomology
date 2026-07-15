import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Summable norm majorants

A summable nonnegative scalar family controls both absolute summability and the
norm of the corresponding Banach-valued infinite sum.  This is the common
assembly step used by the oscillatory-tail owners.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem tsum_norm_le
    {ι E : Type*}
    [NormedAddCommGroup E]
    {f : ι → E} {majorant : ι → ℝ}
    (hmajorant : Summable majorant)
    (hpointwise : ∀ i, ‖f i‖ ≤ majorant i) :
    ‖∑' i, f i‖ ≤ ∑' i, majorant i := by
  exact tsum_of_norm_bounded hmajorant.hasSum hpointwise

end
end LFunctions
end Boundary
