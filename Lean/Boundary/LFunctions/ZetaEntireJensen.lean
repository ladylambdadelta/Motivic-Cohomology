import Boundary.LFunctions.ZetaZeroSideDefinitions

/-!
# Jensen counting for entire functions

This file owns the general Jensen finite-order counting theorem used by the
completed-zeta zero side.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Zeros of an entire function. -/
abbrev EntireFunctionZero
    (F : ℂ → ℂ) : Type :=
  {z : ℂ // F z = 0}

/-- Analytic multiplicity of a zero of an entire function. -/
noncomputable def entireFunctionZeroMultiplicity
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (z : ℂ) : ℕ :=
  (hF z).order.toNat

/-- Multiplicity summand for entire-function zeros inside a closed disk. -/
noncomputable def entireFunctionZeroMultiplicityClosedDiskSummand
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (R : ℝ)
    (z : EntireFunctionZero F) : ℝ :=
  if ‖(z : ℂ)‖ ≤ R then
    (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ)
  else
    0

/-- Multiplicity count for entire-function zeros inside a closed disk. -/
noncomputable def entireFunctionZeroMultiplicityCountingInClosedDisk
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (R : ℝ) : ℝ :=
  ∑' z : EntireFunctionZero F,
    entireFunctionZeroMultiplicityClosedDiskSummand F hF R z

/-- Jensen finite-order counting theorem for nonzero entire functions.

This is the analytic owner theorem: a nontrivial entire function of polynomial
finite order has polynomially bounded zero count in closed disks, counted with
analytic multiplicity. -/
theorem entireFunctionZeroMultiplicityCounting_closedDisk_bound_by_jensen_owner
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (hfinite :
      ∃ A : ℝ, ∃ m : ℕ,
        0 < A ∧
        ∀ z : ℂ,
          ‖F z‖ ≤ A * (1 + ‖z‖) ^ m) :
    ∃ C : ℝ, ∃ d : ℕ,
      0 < C ∧
      ∀ R : ℝ,
        1 ≤ R →
        entireFunctionZeroMultiplicityCountingInClosedDisk F hF R ≤
          C * R ^ d := by
  sorry

/-- Jensen finite-order counting theorem for nonzero entire functions.

This is the analytic owner theorem: a nontrivial entire function of polynomial
finite order has polynomially bounded zero count in closed disks, counted with
analytic multiplicity. -/
theorem entireFunctionZeroMultiplicityCounting_closedDisk_bound_by_jensen
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (hfinite :
      ∃ A : ℝ, ∃ m : ℕ,
        0 < A ∧
        ∀ z : ℂ,
          ‖F z‖ ≤ A * (1 + ‖z‖) ^ m) :
    ∃ C : ℝ, ∃ d : ℕ,
      0 < C ∧
      ∀ R : ℝ,
        1 ≤ R →
        entireFunctionZeroMultiplicityCountingInClosedDisk F hF R ≤
          C * R ^ d := by
  exact
    entireFunctionZeroMultiplicityCounting_closedDisk_bound_by_jensen_owner
      F hF hnontrivial hfinite

end

end LFunctions
end Boundary
