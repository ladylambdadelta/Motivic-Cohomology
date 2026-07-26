import Mathlib.Analysis.Distribution.SchwartzSpace
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.KernelDensity.AtomicDistributionGaussianKernel

/-!
# Schwartz probe owner

The compactly supported admissible probe is not the right carrier for the
prime-power tail: its Fourier decay is only polynomial.  This owner exposes
Mathlib's genuine Schwartz carrier for the Gaussian/rapid-decay lane, without
identifying it with the compactly supported carrier.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- A rapid-decay probe on the logarithmic line. -/
abbrev ZetaSchwartzFunction := SchwartzMap ℝ ℂ

namespace ZetaSchwartzFunction

/-- The scalar exponential carrier owned by the rapid-decay lane. -/
noncomputable def gaussianLaplaceKernel (z : ℂ) : ℂ :=
  ((Real.pi : ℂ) / (1 : ℂ)) ^ (1 / 2 : ℂ) * Complex.exp z

theorem gaussianLaplaceKernel_norm_eq_exp_re (z : ℂ) :
    ‖gaussianLaplaceKernel z‖ =
      ZetaAdmissibleFunction.fullGaussianLaplaceKernelNormalizationNorm *
        Real.exp z.re := by
  have hexponentialNorm : ‖Complex.exp z‖ = Real.exp z.re :=
    Eq.trans
      (Complex.norm_eq_abs (Complex.exp z))
      (Complex.abs_exp z)
  exact Eq.trans
    (norm_mul
      (((Real.pi : ℂ) / (1 : ℂ)) ^ (1 / 2 : ℂ))
      (Complex.exp z))
    (congrArg₂
      (fun left right : ℝ => left * right)
      (Eq.refl ZetaAdmissibleFunction.fullGaussianLaplaceKernelNormalizationNorm)
      hexponentialNorm)

theorem gaussianLaplaceKernel_negReal_norm_eq_exp_neg (x : ℝ) :
    ‖gaussianLaplaceKernel (-(x : ℂ))‖ =
      ZetaAdmissibleFunction.fullGaussianLaplaceKernelNormalizationNorm *
        Real.exp (-x) := by
  have hnorm :
      ‖gaussianLaplaceKernel (-(x : ℂ))‖ =
        ZetaAdmissibleFunction.fullGaussianLaplaceKernelNormalizationNorm *
          Real.exp (-(x : ℂ)).re :=
    gaussianLaplaceKernel_norm_eq_exp_re (-(x : ℂ))
  have hre : (-(x : ℂ)).re = -x :=
    rfl
  exact Eq.trans
    hnorm
    (congrArg
      (fun value : ℝ =>
        ZetaAdmissibleFunction.fullGaussianLaplaceKernelNormalizationNorm *
          Real.exp value)
      hre)

end ZetaSchwartzFunction

end
end LFunctions
end Boundary
