import Mathlib.Analysis.Complex.Basic

/-!
# Finite complex-sum norm bounds

This file owns the generic cardinality bounds used by finite oscillatory
packet decompositions.  It is independent of every phase model.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- A finite complex sum is bounded by a uniform summand bound times its
cardinality. -/
theorem Complex.finite_sum_norm_le_card_mul_of_norm_le
    {ι : Type*}
    (s : Finset ι)
    (u : ι → ℂ)
    {M : ℝ}
    (_hM : 0 ≤ M)
    (hu : ∀ i : ι, i ∈ s → ‖u i‖ ≤ M) :
    ‖∑ i ∈ s, u i‖ ≤ ((s.card : ℝ) * M) := by
  have hsum_norm :
      ‖∑ i ∈ s, u i‖ ≤ ∑ i ∈ s, ‖u i‖ :=
    norm_sum_le s u
  have hsum_bound :
      (∑ i ∈ s, ‖u i‖) ≤ ∑ i ∈ s, M :=
    Finset.sum_le_sum (fun i hi => hu i hi)
  have hconstant_sum :
      (∑ i ∈ s, M) = ((s.card : ℝ) * M) :=
    Eq.trans (Finset.sum_const M) (nsmul_eq_mul s.card M)
  exact le_trans hsum_norm (le_trans hsum_bound (le_of_eq hconstant_sum))

/-- Unit-bounded finite complex sums are bounded by their cardinality. -/
theorem Complex.finite_sum_norm_le_card_of_norm_le_one
    {ι : Type*}
    (s : Finset ι)
    (u : ι → ℂ)
    (hu : ∀ i : ι, i ∈ s → ‖u i‖ ≤ 1) :
    ‖∑ i ∈ s, u i‖ ≤ (s.card : ℝ) := by
  have hbound :
      ‖∑ i ∈ s, u i‖ ≤ ((s.card : ℝ) * 1) :=
    Complex.finite_sum_norm_le_card_mul_of_norm_le s u zero_le_one hu
  exact le_trans hbound (le_of_eq (mul_one (s.card : ℝ)))

end

end LFunctions
end Boundary
