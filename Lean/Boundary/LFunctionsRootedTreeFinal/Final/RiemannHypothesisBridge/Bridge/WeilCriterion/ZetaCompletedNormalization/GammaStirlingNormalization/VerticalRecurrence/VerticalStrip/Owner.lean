import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.VerticalRecurrence.Factors.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.SectorialLog.Owner

/-!
# Vertical recurrence: product composition and largeness

This file owns the finite product norm equations, upper/lower bound
composition from per-factor estimates, and nonzero preservation at large heights.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

      Eq.subst
        (motive := fun t : ℝ =>
          t ≤
            ‖Complex.gammaRecurrenceProduct
              (Complex.fixedRealPartVerticalPoint x y) N‖)
        hlower_target
        (Eq.subst
          (motive := fun t : ℝ => (c * R) ^ N ≤ t)
          hprod_norm
          hlower_prod)
  exact ⟨H, C ^ N, c ^ N, hH_pos, hC_pow_pos, hc_pow_pos, hpointwise⟩

/-- The exact finite-product geometry estimate for deterministic Gamma
recurrence factors on a fixed vertical strip.

The per-factor strip geometry is proved above; this theorem packages those
factor estimates with the finite product algebra over `j < N`. -/
theorem Complex.gammaRecurrenceProduct_verticalStrip_twoSided_bounds_finiteProductEstimate
    (A B : ℝ)
    (N : ℕ) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          ‖Complex.gammaRecurrenceProduct
              (Complex.fixedRealPartVerticalPoint x y) N‖ ≤
            C * (1 + ‖y‖) ^ (N : ℝ) ∧
          c * (1 + ‖y‖) ^ (N : ℝ) ≤
            ‖Complex.gammaRecurrenceProduct
              (Complex.fixedRealPartVerticalPoint x y) N‖ := by
  exact
    Complex.gammaRecurrenceProduct_verticalStrip_twoSided_bounds_of_factor_bounds
      A B N
      (Complex.gammaRecurrenceProduct_factor_twoSided_bounds_on_verticalStrip
        A B N)

/-- Finite recurrence products have uniform polynomial upper/lower bounds on a
fixed vertical strip after a deterministic shift.

This is the exact finite-product estimate needed for recurrence transport: for
fixed `N`, bounded real part and large `|y|` make each factor `x + i y + j`
comparable to `1 + |y|`, and therefore the whole product is comparable to
`(1 + |y|)^N`. -/
theorem Complex.gammaRecurrenceProduct_verticalStrip_twoSided_bounds
    (A B : ℝ)
    (N : ℕ) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          ‖Complex.gammaRecurrenceProduct
              (Complex.fixedRealPartVerticalPoint x y) N‖ ≤
            C * (1 + ‖y‖) ^ (N : ℝ) ∧
          c * (1 + ‖y‖) ^ (N : ℝ) ≤
            ‖Complex.gammaRecurrenceProduct
              (Complex.fixedRealPartVerticalPoint x y) N‖ := by
  exact
    Complex.gammaRecurrenceProduct_verticalStrip_twoSided_bounds_finiteProductEstimate
      A B N

/-- Large vertical height keeps all deterministic recurrence factors nonzero. -/
theorem Complex.gammaRecurrenceProduct_factors_ne_zero_on_verticalStrip_largeHeight

end

end LFunctions
end Boundary
