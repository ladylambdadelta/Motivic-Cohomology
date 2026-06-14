import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.SectorialLogNorm

/-!
# Fixed-vertical-line Gamma bounds

This file owns fixed-real-part vertical upper and reciprocal bounds for Gamma.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Fixed-real-part vertical upper bound obtained by combining open-sector
Binet estimates for large `|t|` with compact-interval boundedness. -/
theorem Complex.Gamma_fixedRealPart_vertical_upper_bound_from_openSector_and_compact
    (σ : ℝ)
    (hσ : 0 < σ) :
    ∃ C : ℝ, ∃ m : ℕ,
      0 < C ∧
      ∀ t : ℝ,
        ‖Complex.Gamma (σ + t * Complex.I)‖ ≤
          C * (1 + ‖t‖) ^ m := by
  sorry

/-- Fixed-real-part vertical upper bound for Gamma. -/
theorem Complex.Gamma_fixedRealPart_vertical_upper_bound_classical
    (σ : ℝ)
    (hσ : 0 < σ) :
    ∃ C : ℝ, ∃ m : ℕ,
      0 < C ∧
      ∀ t : ℝ,
        ‖Complex.Gamma (σ + t * Complex.I)‖ ≤
          C * (1 + ‖t‖) ^ m := by
  exact
    Complex.Gamma_fixedRealPart_vertical_upper_bound_from_openSector_and_compact
      σ hσ

/-- Fixed-real-part reciprocal bound from nonvanishing, compact-interval
control, and the large-vertical Stirling/Binet estimate. -/
theorem Complex.Gamma_fixedRealPart_vertical_reciprocal_bound_from_nonvanishing_and_stirling
    (σ : ℝ)
    (hσ : 0 < σ) :
    ∃ C : ℝ, ∃ A : ℝ,
      0 < C ∧ 0 < A ∧
      ∀ t : ℝ,
        ‖(Complex.Gamma (σ + t * Complex.I))⁻¹‖ ≤
          C * Real.exp (A * ‖t‖) := by
  sorry

/-- Fixed-real-part vertical reciprocal bound for Gamma.

The reciprocal has exponential, not polynomial, vertical growth:
`1 / Γ(σ + it)` grows like `exp (π |t| / 2)` up to powers of `|t|`.
This owner statement records the correct classical growth scale. -/
theorem Complex.Gamma_fixedRealPart_vertical_lower_bound_classical
    (σ : ℝ)
    (hσ : 0 < σ) :
    ∃ C : ℝ, ∃ A : ℝ,
      0 < C ∧ 0 < A ∧
      ∀ t : ℝ,
        ‖(Complex.Gamma (σ + t * Complex.I))⁻¹‖ ≤
          C * Real.exp (A * ‖t‖) := by
  exact
    Complex.Gamma_fixedRealPart_vertical_reciprocal_bound_from_nonvanishing_and_stirling
      σ hσ

end

end LFunctions
end Boundary
