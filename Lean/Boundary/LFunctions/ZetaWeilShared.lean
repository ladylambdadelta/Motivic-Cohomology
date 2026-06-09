import Boundary.LFunctions.ProbeInterface
import Boundary.LFunctions.AutocorrelationInterface
import Boundary.LFunctions.ZetaZeroSideDefinitions

/-!
# Boundary Weil shared definitions

This file owns the probe-level Weil form definitions and the basic
autocorrelation positivity wrappers that are shared by the Weil criterion file
and the explicit-formula transport file.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The completed zero-side sum in real-valued form. -/
noncomputable def zetaCompletedZeroSideRe
    (φ : ZetaProbe) : ℝ :=
  Complex.re <|
    ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ},
      zetaZeroSideContribution (ρ : ℂ) φ

/-- The completed spectral Weil form on the zero side. -/
noncomputable def zetaCompletedSpectralWeilForm
    (φ : ZetaProbe) : ℝ :=
  zetaCompletedZeroSideRe φ

/-- The completed Weil form on the probe class. -/
noncomputable def zetaWeilFormCompleted (φ : ZetaProbe) : ℝ :=
  zetaCompletedSpectralWeilForm φ

/-- The completed spectral Weil form is definitionally the completed zero-side sum. -/
theorem zetaCompletedSpectralWeilForm_def
    (φ : ZetaProbe) :
    zetaCompletedSpectralWeilForm φ = zetaCompletedZeroSideRe φ := by
  rfl

/-- The completed Weil form is definitionally the completed spectral form. -/
theorem zetaWeilFormCompleted_def
    (φ : ZetaProbe) :
    zetaWeilFormCompleted φ = zetaCompletedSpectralWeilForm φ := by
  rfl

/-- The completed spectral Weil form is the completed zero-side real sum. -/
theorem zetaCompletedSpectralWeilForm_eq_zeroSide
    (φ : ZetaProbe) :
    zetaCompletedSpectralWeilForm φ = zetaCompletedZeroSideRe φ := by
  rfl

/-- The completed Weil form is the completed zero-side real sum. -/
theorem zetaWeilFormCompleted_eq_zeroSide
    (φ : ZetaProbe) :
    zetaWeilFormCompleted φ = zetaCompletedZeroSideRe φ := by
  rw [zetaWeilFormCompleted_def, zetaCompletedSpectralWeilForm_eq_zeroSide]

end
end LFunctions
end Boundary
