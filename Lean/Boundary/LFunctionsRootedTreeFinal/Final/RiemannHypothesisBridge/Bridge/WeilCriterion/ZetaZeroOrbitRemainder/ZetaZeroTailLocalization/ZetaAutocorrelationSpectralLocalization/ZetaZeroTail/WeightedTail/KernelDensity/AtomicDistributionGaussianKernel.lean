import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.KernelDensity.AtomicDistributionGaussianGeometry
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.KernelDensity.AtomicDistributionGaussianProbe

/-!
# Full Gaussian Laplace kernel

This file records the exact bilateral Laplace transform of the physical
Gaussian in the normalization used by completed-zero spectral evaluation.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

/-- The full Gaussian bilateral Laplace kernel. -/
noncomputable def fullGaussianLaplaceKernel (z : ℂ) : ℂ :=
  ∫ t : ℝ, physicalGaussian t * Complex.exp (z * (t : ℂ))

/-- The physical-Gaussian Laplace integrand is a complex quadratic
exponential in the form consumed by `integral_cexp_quadratic`. -/
theorem physicalGaussian_mul_exp_eq_quadraticExp
    (z : ℂ)
    (t : ℝ) :
    physicalGaussian t * Complex.exp (z * (t : ℂ)) =
      Complex.exp
        ((-(1 : ℂ)) * (t : ℂ) ^ 2 + z * (t : ℂ) + 0) := by
  have hpower : ((t ^ 2 : ℝ) : ℂ) = (t : ℂ) ^ 2 :=
    Complex.ofReal_pow t 2
  have hnegativeCast :
      (((-(t ^ 2) : ℝ) : ℂ)) = -(((t ^ 2 : ℝ) : ℂ)) :=
    Complex.ofReal_neg (t ^ 2)
  have hnegativeSquare :
      (((-(t ^ 2) : ℝ) : ℂ)) = (-(1 : ℂ)) * (t : ℂ) ^ 2 :=
    Eq.trans hnegativeCast
      (Eq.trans
        (congrArg Neg.neg hpower)
        (neg_one_mul ((t : ℂ) ^ 2)).symm)
  have hsum :
      (((-(t ^ 2) : ℝ) : ℂ)) + z * (t : ℂ) =
        (-(1 : ℂ)) * (t : ℂ) ^ 2 + z * (t : ℂ) + 0 :=
    Eq.trans
      (congrArg (fun value : ℂ => value + z * (t : ℂ)) hnegativeSquare)
      (add_zero ((-(1 : ℂ)) * (t : ℂ) ^ 2 + z * (t : ℂ))).symm
  exact Eq.trans
    (Complex.exp_add
      (((-(t ^ 2) : ℝ) : ℂ))
      (z * (t : ℂ))).symm
    (congrArg Complex.exp hsum)

/-- The full Gaussian Laplace kernel has its standard closed form. -/
theorem fullGaussianLaplaceKernel_eq
    (z : ℂ) :
    fullGaussianLaplaceKernel z =
      ((Real.pi : ℂ) / (1 : ℂ)) ^ (1 / 2 : ℂ) *
        Complex.exp (z ^ 2 / 4) := by
  have hintegrand :
      (fun t : ℝ =>
        physicalGaussian t * Complex.exp (z * (t : ℂ))) =
      (fun t : ℝ =>
        Complex.exp
          ((-(1 : ℂ)) * (t : ℂ) ^ 2 + z * (t : ℂ) + 0)) := by
    funext t
    exact physicalGaussian_mul_exp_eq_quadraticExp z t
  have hquadratic :=
    integral_cexp_quadratic
      (b := (-(1 : ℂ)))
      (show (-(1 : ℂ)).re < 0 from neg_lt_zero.mpr zero_lt_one)
      z
      0
  have hnegativeNegative : -(-(1 : ℂ)) = (1 : ℂ) :=
    neg_neg (1 : ℂ)
  have hzeroSub :
      (0 : ℂ) - z ^ 2 / (4 * (-(1 : ℂ))) = z ^ 2 / 4 := by
    have hfourNegative : (4 : ℂ) * (-(1 : ℂ)) = -(4 : ℂ) :=
      mul_neg_one (4 : ℂ)
    have hdivideNegative : z ^ 2 / (-(4 : ℂ)) = -(z ^ 2 / 4) :=
      (div_neg (z ^ 2) : z ^ 2 / (-(4 : ℂ)) = -(z ^ 2 / 4))
    exact Eq.trans
      (congrArg (fun denominator : ℂ =>
        (0 : ℂ) - z ^ 2 / denominator) hfourNegative)
      (Eq.trans
        (congrArg (fun value : ℂ => (0 : ℂ) - value) hdivideNegative)
        (Eq.trans
          (zero_sub (-(z ^ 2 / 4)))
          (neg_neg (z ^ 2 / 4))))
  have hnormalizedQuadratic :
      (∫ t : ℝ,
        Complex.exp
          ((-(1 : ℂ)) * (t : ℂ) ^ 2 + z * (t : ℂ) + 0)) =
        ((Real.pi : ℂ) / (1 : ℂ)) ^ (1 / 2 : ℂ) *
          Complex.exp (z ^ 2 / 4) :=
    Eq.trans hquadratic
      (congrArg₂ Mul.mul
        (congrArg
          (fun denominator : ℂ =>
            ((Real.pi : ℂ) / denominator) ^ (1 / 2 : ℂ))
          hnegativeNegative)
        (congrArg Complex.exp hzeroSub))
  exact Eq.trans
    (congrArg
      (fun function : ℝ → ℂ => ∫ t : ℝ, function t)
      hintegrand)
    hnormalizedQuadratic

/-- The full Gaussian kernel at spectral zero is the physical Gaussian
integral. -/
theorem fullGaussianLaplaceKernel_zero :
    fullGaussianLaplaceKernel 0 = ∫ t : ℝ, physicalGaussian t := by
  have hintegrand :
      (fun t : ℝ =>
        physicalGaussian t * Complex.exp ((0 : ℂ) * (t : ℂ))) =
      physicalGaussian := by
    funext t
    have hzeroProduct : (0 : ℂ) * (t : ℂ) = 0 :=
      zero_mul (t : ℂ)
    have hexponential : Complex.exp ((0 : ℂ) * (t : ℂ)) = 1 :=
      Eq.trans (congrArg Complex.exp hzeroProduct) Complex.exp_zero
    exact Eq.trans
      (congrArg (fun value : ℂ => physicalGaussian t * value) hexponential)
      (mul_one (physicalGaussian t))
  exact congrArg
    (fun function : ℝ → ℂ => ∫ t : ℝ, function t)
    hintegrand

/-- The full Gaussian kernel is nonzero at spectral zero. -/
theorem fullGaussianLaplaceKernel_zero_ne_zero :
    fullGaussianLaplaceKernel 0 ≠ 0 :=
  Eq.subst
    (motive := fun value : ℂ => value ≠ 0)
    fullGaussianLaplaceKernel_zero.symm
    integral_physicalGaussian_ne_zero

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
