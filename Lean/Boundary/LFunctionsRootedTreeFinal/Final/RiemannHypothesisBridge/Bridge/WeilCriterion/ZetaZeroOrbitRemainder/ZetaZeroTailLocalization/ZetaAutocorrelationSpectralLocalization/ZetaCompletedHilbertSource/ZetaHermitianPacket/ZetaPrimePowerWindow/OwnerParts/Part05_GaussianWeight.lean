import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.ZetaPrimePowerWindow.OwnerParts.Part04
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ProbeInterface.ZetaSchwartzFunction.Owner

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaPrimePowerIndex

/- The Gaussian owner exposes the exact scalar majorant before any inequality is
  applied.  Keeping this equality here prevents later summability arguments from
  silently replacing the Gaussian transform by a merely bounded surrogate. -/
theorem weight_mul_gaussianLaplaceKernel_neg_center_eq_normalization_mul_exp
    (ι : ZetaPrimePowerIndex) :
    weight ι *
        ‖ZetaSchwartzFunction.gaussianLaplaceKernel (-(center ι : ℂ))‖ =
      ZetaAdmissibleFunction.fullGaussianLaplaceKernelNormalizationNorm *
        (weight ι * Real.exp (-center ι)) := by
  have hkernel :=
    ZetaSchwartzFunction.gaussianLaplaceKernel_negReal_norm_eq_exp_neg
      (center ι)
  exact Eq.trans
    (congrArg (fun value : ℝ => weight ι * value) hkernel)
    (Eq.trans
      (mul_assoc (weight ι)
        ZetaAdmissibleFunction.fullGaussianLaplaceKernelNormalizationNorm
        (Real.exp (-center ι))).symm
      (Eq.trans
        (congrArg
          (fun value : ℝ => value * Real.exp (-center ι))
          (mul_comm (weight ι)
            ZetaAdmissibleFunction.fullGaussianLaplaceKernelNormalizationNorm))
        (mul_assoc
          ZetaAdmissibleFunction.fullGaussianLaplaceKernelNormalizationNorm
          (weight ι)
          (Real.exp (-center ι)))))

theorem weight_mul_gaussianLaplaceKernel_neg_center_le_of_exp_bound
    (ι : ZetaPrimePowerIndex)
    (hbound : weight ι * Real.exp (-center ι) ≤ 2) :
    weight ι *
        ‖ZetaSchwartzFunction.gaussianLaplaceKernel (-(center ι : ℂ))‖ ≤
      2 * ZetaAdmissibleFunction.fullGaussianLaplaceKernelNormalizationNorm := by
  have hconst :
      0 ≤ ZetaAdmissibleFunction.fullGaussianLaplaceKernelNormalizationNorm :=
    norm_nonneg _
  have hbound' :
      ZetaAdmissibleFunction.fullGaussianLaplaceKernelNormalizationNorm *
          (weight ι * Real.exp (-center ι)) ≤
        ZetaAdmissibleFunction.fullGaussianLaplaceKernelNormalizationNorm * 2 :=
    mul_le_mul_of_nonneg_left hbound hconst
  have hright :
      ZetaAdmissibleFunction.fullGaussianLaplaceKernelNormalizationNorm * 2 =
        2 * ZetaAdmissibleFunction.fullGaussianLaplaceKernelNormalizationNorm :=
    mul_comm ZetaAdmissibleFunction.fullGaussianLaplaceKernelNormalizationNorm 2
  have hbound'' :
      ZetaAdmissibleFunction.fullGaussianLaplaceKernelNormalizationNorm *
          (weight ι * Real.exp (-center ι)) ≤
        2 * ZetaAdmissibleFunction.fullGaussianLaplaceKernelNormalizationNorm :=
    Eq.subst
      (motive := fun value : ℝ =>
        ZetaAdmissibleFunction.fullGaussianLaplaceKernelNormalizationNorm *
            (weight ι * Real.exp (-center ι)) ≤ value)
      hright
      hbound'
  exact Eq.subst
    (motive := fun value : ℝ => value ≤
      2 * ZetaAdmissibleFunction.fullGaussianLaplaceKernelNormalizationNorm)
    (weight_mul_gaussianLaplaceKernel_neg_center_eq_normalization_mul_exp ι).symm
    hbound''

theorem weight_mul_gaussianLaplaceKernel_neg_center_le
    (ι : ZetaPrimePowerIndex) (hι : IsGenuine ι) :
      weight ι *
        ‖ZetaSchwartzFunction.gaussianLaplaceKernel (-(center ι : ℂ))‖ ≤
      2 * ZetaAdmissibleFunction.fullGaussianLaplaceKernelNormalizationNorm := by
  have hweight :
      weight ι * Real.exp ((-1 : ℝ) * center ι) ≤ 2 :=
    weight_mul_exp_mul_center_le_two_of_nonpos ι hι (-1)
      (le_of_lt neg_one_lt_zero)
  have hnegative : (-1 : ℝ) * center ι = -center ι :=
    neg_one_mul (center ι)
  have hbound :
      weight ι * Real.exp (-center ι) ≤ 2 :=
    Eq.subst
      (motive := fun value : ℝ => weight ι * Real.exp value ≤ 2)
      hnegative
      hweight
  exact weight_mul_gaussianLaplaceKernel_neg_center_le_of_exp_bound
    ι hbound

theorem weight_mul_gaussianLaplaceKernel_neg_center_le_raw
    (ι : ZetaPrimePowerIndex) :
      weight ι *
        ‖ZetaSchwartzFunction.gaussianLaplaceKernel (-(center ι : ℂ))‖ ≤
      2 * ZetaAdmissibleFunction.fullGaussianLaplaceKernelNormalizationNorm := by
  by_cases hι : IsGenuine ι
  · exact weight_mul_gaussianLaplaceKernel_neg_center_le ι hι
  · have hweight : weight ι = 0 := weight_eq_zero_of_not_isGenuine ι hι
    have hzero :
        weight ι *
            ‖ZetaSchwartzFunction.gaussianLaplaceKernel (-(center ι : ℂ))‖ = 0 := by
      have hproduct :
          weight ι *
              ‖ZetaSchwartzFunction.gaussianLaplaceKernel (-(center ι : ℂ))‖ =
            0 *
              ‖ZetaSchwartzFunction.gaussianLaplaceKernel (-(center ι : ℂ))‖ :=
        congrArg
          (fun value : ℝ => value *
            ‖ZetaSchwartzFunction.gaussianLaplaceKernel (-(center ι : ℂ))‖)
          hweight
      exact Eq.trans hproduct
        (zero_mul
          ‖ZetaSchwartzFunction.gaussianLaplaceKernel (-(center ι : ℂ))‖)
    exact Eq.subst
      (motive := fun value : ℝ => value ≤
        2 * ZetaAdmissibleFunction.fullGaussianLaplaceKernelNormalizationNorm)
      hzero.symm
      (mul_nonneg zero_le_two (norm_nonneg _))

end ZetaPrimePowerIndex

end
end LFunctions
end Boundary
