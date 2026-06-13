import Boundary.LFunctions.ZetaZeroSideDefinitions

/-!
# Centered-zero vertical strip

This file owns the zero-geometry bridge needed to apply Paley-Wiener vertical-strip
decay to evaluations on the completed zero side.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The centered completed-zero spectral evaluation points lie in one fixed vertical
strip.

This is the coarse critical-strip input for completed zeros after the normalizations used by
the zero-side transform. -/
theorem exists_zetaCenteredZero_fixed_vertical_strip :
    ∃ a : ℝ, ∃ b : ℝ,
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        a ≤ (zetaCenteredZero (ρ : ℂ)).re ∧
          (zetaCenteredZero (ρ : ℂ)).re ≤ b := by
  sorry

end

end LFunctions
end Boundary
