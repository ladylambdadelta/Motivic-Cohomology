import Boundary.LFunctions.ProbeInterface
import Boundary.LFunctions.AutocorrelationInterface
import Boundary.LFunctions.ZetaZeroSideDefinitions

/-!
# Boundary Weil shared definitions

This file owns the probe-level Weil form definitions and the basic
convolution-autocorrelation positivity wrappers shared by the Weil criterion
file and the explicit-formula transport file.
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

/-- The completed zero-side real form depends only on the underlying test function. -/
theorem zetaCompletedZeroSideRe_congr_toZetaTestFunction
    {φ ψ : ZetaProbe}
    (h : φ.toZetaTestFunction' = ψ.toZetaTestFunction') :
    zetaCompletedZeroSideRe φ = zetaCompletedZeroSideRe ψ := by
  have hφψ : φ = ψ := by
    apply ZetaAdmissibleFunction.ext
    intro x
    have htest_fun :
        φ.toZetaTestFunction'.toFun = ψ.toZetaTestFunction'.toFun :=
      congrArg ZetaTestFunction.toFun h
    have htest_x : φ.toZetaTestFunction' x = ψ.toZetaTestFunction' x :=
      congrFun htest_fun x
    calc
      φ x = φ.toZetaTestFunction' x := by
        exact (ZetaAdmissibleFunction.toZetaTestFunction'_apply φ x).symm
      _ = ψ.toZetaTestFunction' x := htest_x
      _ = ψ x := by
        exact ZetaAdmissibleFunction.toZetaTestFunction'_apply ψ x
  cases hφψ
  rfl

/-- The completed Weil form depends only on the underlying test function. -/
theorem zetaWeilFormCompleted_congr_toZetaTestFunction
    {φ ψ : ZetaProbe}
    (h : φ.toZetaTestFunction' = ψ.toZetaTestFunction') :
    zetaWeilFormCompleted φ = zetaWeilFormCompleted ψ := by
  have hzero :
      zetaCompletedZeroSideRe φ = zetaCompletedZeroSideRe ψ :=
    zetaCompletedZeroSideRe_congr_toZetaTestFunction h
  exact congrArg id <|
    (zetaWeilFormCompleted_eq_zeroSide φ).trans
      (hzero.trans (zetaWeilFormCompleted_eq_zeroSide ψ).symm)

/-- The raw completed Weil-positivity statement on all probes. -/
def ZetaWeilPositivity : Prop :=
  ∀ φ : ZetaProbe, 0 ≤ zetaWeilFormCompleted φ

/-- The completed Weil-positivity statement restricted to convolution-autocorrelation probes. -/
def ZetaConvolutionAutocorrelationWeilPositivity : Prop :=
  ∀ φ : ZetaProbe, IsZetaConvolutionAutocorrelationProbe φ →
    0 ≤ zetaWeilFormCompleted φ

/-- Historical name for positivity on convolution-autocorrelation probes. -/
abbrev ZetaAutocorrelationWeilPositivity : Prop :=
  ZetaConvolutionAutocorrelationWeilPositivity

/-- The quadratic Weil-positivity statement: every seed has nonnegative completed Weil form
after passing to its convolution autocorrelation. This is the criterion-facing positivity cone,
not the stronger raw all-probe positivity predicate. -/
def ZetaWeilQuadraticPositivity : Prop :=
  ∀ f : ZetaAdmissibleFunction,
    0 ≤ zetaWeilFormCompleted (ZetaAdmissibleFunction.convolutionAutocorrelation f)

/-- Convolution-autocorrelation probes have the same completed Weil form as their zero-side
real sum. -/
theorem zetaWeilFormCompleted_convolutionAutocorrelation_eq_zeroSide
    (f : ZetaAdmissibleFunction) :
    zetaWeilFormCompleted (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      zetaCompletedZeroSideRe (ZetaAdmissibleFunction.convolutionAutocorrelation f) := by
  exact zetaWeilFormCompleted_eq_zeroSide
    (ZetaAdmissibleFunction.convolutionAutocorrelation f)

/-- Historical name for the convolution-autocorrelation zero-side bridge. -/
theorem zetaWeilFormCompleted_autocorrelation_eq_zeroSide
    (f : ZetaAdmissibleFunction) :
    zetaWeilFormCompleted (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      zetaCompletedZeroSideRe (ZetaAdmissibleFunction.convolutionAutocorrelation f) := by
  exact zetaWeilFormCompleted_convolutionAutocorrelation_eq_zeroSide f

end
end LFunctions
end Boundary
