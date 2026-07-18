import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.KernelDensity.AtomicDistributionGaussianHermiteIntegrability
import Mathlib.MeasureTheory.Group.Integral

/-!
# Horizontal twists of the physical Gaussian

Completion of the square turns every bounded horizontal Laplace twist into a
translated physical Gaussian.  This is the owner normalization used by the
uniform derivative estimates for the compact Gaussian sequence.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

open scoped ContDiff

/-- Doubling the half of a real number recovers the number. -/
theorem two_mul_half
    (x : ℝ) :
    2 * (x / 2) = x := by
  have hhalfSum : x / 2 + x / 2 = x :=
    add_halves x
  exact Eq.trans
    (two_mul (x / 2))
    hhalfSum

/-- The cross term in the completed square has the required normalization. -/
theorem two_mul_mul_half
    (x t : ℝ) :
    2 * t * (x / 2) = x * t := by
  have hmoveTwo : 2 * t * (x / 2) = t * (2 * (x / 2)) := by
    exact Eq.trans
      (congrArg (fun value : ℝ => value * (x / 2))
        (mul_comm 2 t))
      (mul_assoc t 2 (x / 2))
  exact Eq.trans hmoveTwo
    (Eq.trans
      (congrArg (fun value : ℝ => t * value) (two_mul_half x))
      (mul_comm t x))

/-- Subtracting a sum ending in the initial term cancels that term. -/
theorem sub_add_self_right_eq_neg
    (a b : ℝ) :
    a - (b + a) = -b := by
  have hsplit : a - (b + a) = a - b - a :=
    sub_add_eq_sub_sub a b a
  have hswap : a - b - a = a - a - b :=
    sub_right_comm a b a
  exact Eq.trans hsplit
    (Eq.trans hswap
      (Eq.trans
        (congrArg (fun value : ℝ => value - b) (sub_self a))
        (zero_sub b)))

/-- Completion of the square for the real physical Gaussian exponent. -/
theorem neg_square_add_linear_eq_halfSquare_sub_shiftSquare
    (x t : ℝ) :
    -(t ^ 2) + x * t =
      (x / 2) ^ 2 - (t - x / 2) ^ 2 := by
  have hshiftSquare :
      (t - x / 2) ^ 2 =
        t ^ 2 - 2 * t * (x / 2) + (x / 2) ^ 2 :=
    sub_sq t (x / 2)
  have hcancel :
      (x / 2) ^ 2 -
          (t ^ 2 - 2 * t * (x / 2) + (x / 2) ^ 2) =
        -(t ^ 2 - 2 * t * (x / 2)) :=
    sub_add_self_right_eq_neg
      ((x / 2) ^ 2)
      (t ^ 2 - 2 * t * (x / 2))
  have hnegativeDifference :
      -(t ^ 2 - 2 * t * (x / 2)) =
        2 * t * (x / 2) - t ^ 2 :=
    neg_sub (t ^ 2) (2 * t * (x / 2))
  have hcross :
      2 * t * (x / 2) - t ^ 2 = x * t + -(t ^ 2) := by
    exact Eq.trans
      (congrArg (fun value : ℝ => value - t ^ 2)
        (two_mul_mul_half x t))
      (sub_eq_add_neg (x * t) (t ^ 2))
  have hreorder : x * t + -(t ^ 2) = -(t ^ 2) + x * t :=
    add_comm (x * t) (-(t ^ 2))
  have hright :
      (x / 2) ^ 2 - (t - x / 2) ^ 2 =
        -(t ^ 2) + x * t := by
    exact Eq.trans
      (congrArg (fun value : ℝ => (x / 2) ^ 2 - value)
        hshiftSquare)
      (Eq.trans hcancel
        (Eq.trans hnegativeDifference
          (Eq.trans hcross hreorder)))
  exact hright.symm

/-- The real Gaussian multiplied by a horizontal exponential twist. -/
noncomputable def realPhysicalGaussianHorizontalTwist
    (x t : ℝ) : ℝ :=
  realPhysicalGaussian t * Real.exp (x * t)

/-- A horizontal Gaussian twist is a positive constant times a translate of
the physical Gaussian. -/
theorem realPhysicalGaussianHorizontalTwist_eq_translate
    (x t : ℝ) :
    realPhysicalGaussianHorizontalTwist x t =
      Real.exp ((x / 2) ^ 2) *
        realPhysicalGaussian (t - x / 2) := by
  have hexponent :
      -(t ^ 2) + x * t =
        (x / 2) ^ 2 + -((t - x / 2) ^ 2) :=
    Eq.trans
      (neg_square_add_linear_eq_halfSquare_sub_shiftSquare x t)
      (sub_eq_add_neg ((x / 2) ^ 2) ((t - x / 2) ^ 2))
  have hexponentialProduct :
      Real.exp (-(t ^ 2)) * Real.exp (x * t) =
        Real.exp ((x / 2) ^ 2) *
          Real.exp (-((t - x / 2) ^ 2)) := by
    exact Eq.trans
      (Real.exp_add (-(t ^ 2)) (x * t)).symm
      (Eq.trans
        (congrArg Real.exp hexponent)
        (Real.exp_add ((x / 2) ^ 2) (-((t - x / 2) ^ 2))))
  exact hexponentialProduct

/-- Function-level completion of the square for a horizontal twist. -/
theorem realPhysicalGaussianHorizontalTwist_function_eq_translate
    (x : ℝ) :
    realPhysicalGaussianHorizontalTwist x =
      (fun t : ℝ =>
        Real.exp ((x / 2) ^ 2) *
          realPhysicalGaussian (t - x / 2)) := by
  funext t
  exact realPhysicalGaussianHorizontalTwist_eq_translate x t

/-- Every horizontal twist of the real physical Gaussian is smooth. -/
theorem realPhysicalGaussianHorizontalTwist_contDiff
    (x : ℝ) :
    ContDiff ℝ ∞ (realPhysicalGaussianHorizontalTwist x) := by
  have hlinear : ContDiff ℝ ∞ (fun t : ℝ => x * t) :=
    contDiff_const.mul contDiff_id
  have hexponential : ContDiff ℝ ∞ (fun t : ℝ => Real.exp (x * t)) :=
    Real.contDiff_exp.comp hlinear
  exact realPhysicalGaussian_contDiff.mul hexponential

/-- Translating the physical Gaussian commutes with every iterated
derivative. -/
theorem iteratedDeriv_realPhysicalGaussian_sub_half
    (order : ℕ)
    (x t : ℝ) :
    iteratedDeriv order
        (fun u : ℝ => realPhysicalGaussian (u - x / 2)) t =
      iteratedDeriv order realPhysicalGaussian (t - x / 2) := by
  have htranslation :=
    congrFun
      (iteratedDeriv_comp_add_const
        order
        realPhysicalGaussian
        (-(x / 2)))
      t
  have hsourceFunction :
      (fun u : ℝ => realPhysicalGaussian (u - x / 2)) =
        (fun u : ℝ => realPhysicalGaussian (u + -(x / 2))) := by
    funext u
    exact congrArg realPhysicalGaussian
      (sub_eq_add_neg u (x / 2))
  have htargetArgument : t + -(x / 2) = t - x / 2 :=
    (sub_eq_add_neg t (x / 2)).symm
  exact Eq.subst
    (motive := fun source : ℝ → ℝ =>
      iteratedDeriv order source t =
        iteratedDeriv order realPhysicalGaussian (t - x / 2))
    hsourceFunction.symm
    (Eq.trans htranslation
      (congrArg
        (iteratedDeriv order realPhysicalGaussian)
        htargetArgument))

/-- Constant multiplication in the codomain commutes with an iterated real
derivative. -/
theorem iteratedDeriv_real_const_mul
    (order : ℕ)
    (constant : ℝ)
    (function : ℝ → ℝ)
    (hsmooth : ContDiff ℝ order function)
    (t : ℝ) :
    iteratedDeriv order (fun u : ℝ => constant * function u) t =
      constant * iteratedDeriv order function t := by
  have hwithin :
      iteratedDerivWithin order
          (fun u : ℝ => constant * function u) Set.univ t =
        constant * iteratedDerivWithin order function Set.univ t :=
    iteratedDerivWithin_const_mul
      (Set.mem_univ t)
      uniqueDiffOn_univ
      constant
      hsmooth.contDiffOn
  have hsourceUniv :
      iteratedDerivWithin order
          (fun u : ℝ => constant * function u) Set.univ t =
        iteratedDeriv order (fun u : ℝ => constant * function u) t :=
    congrFun iteratedDerivWithin_univ t
  have htargetUniv :
      iteratedDerivWithin order function Set.univ t =
        iteratedDeriv order function t :=
    congrFun iteratedDerivWithin_univ t
  exact Eq.trans hsourceUniv.symm
    (Eq.trans hwithin
      (congrArg (fun value : ℝ => constant * value) htargetUniv))

/-- Exact derivative transport for every horizontal Gaussian twist. -/
theorem iteratedDeriv_realPhysicalGaussianHorizontalTwist
    (order : ℕ)
    (x t : ℝ) :
    iteratedDeriv order
        (realPhysicalGaussianHorizontalTwist x) t =
      Real.exp ((x / 2) ^ 2) *
        iteratedDeriv order realPhysicalGaussian (t - x / 2) := by
  let translated : ℝ → ℝ :=
    fun u : ℝ => realPhysicalGaussian (u - x / 2)
  have htranslatedSmooth : ContDiff ℝ order translated := by
    have hfullSmooth : ContDiff ℝ ∞ translated := by
      have hshift : ContDiff ℝ ∞ (fun u : ℝ => u - x / 2) :=
        contDiff_id.sub contDiff_const
      exact realPhysicalGaussian_contDiff.comp hshift
    exact hfullSmooth.of_le
      (naturalOrder_le_contDiffInfinity order)
  have hfunctionEquality :=
    realPhysicalGaussianHorizontalTwist_function_eq_translate x
  have hconstantDerivative :=
    iteratedDeriv_real_const_mul
      order
      (Real.exp ((x / 2) ^ 2))
      translated
      htranslatedSmooth
      t
  have htranslatedDerivative :=
    iteratedDeriv_realPhysicalGaussian_sub_half order x t
  exact Eq.subst
    (motive := fun source : ℝ → ℝ =>
      iteratedDeriv order source t =
        Real.exp ((x / 2) ^ 2) *
          iteratedDeriv order realPhysicalGaussian (t - x / 2))
    hfunctionEquality.symm
    (Eq.trans hconstantDerivative
      (congrArg
        (fun value : ℝ => Real.exp ((x / 2) ^ 2) * value)
        htranslatedDerivative))

/-- Norm form of the horizontal-twist derivative identity. -/
theorem norm_iteratedDeriv_realPhysicalGaussianHorizontalTwist
    (order : ℕ)
    (x t : ℝ) :
    ‖iteratedDeriv order
        (realPhysicalGaussianHorizontalTwist x) t‖ =
      Real.exp ((x / 2) ^ 2) *
        ‖iteratedDeriv order realPhysicalGaussian (t - x / 2)‖ := by
  have hidentity :=
    iteratedDeriv_realPhysicalGaussianHorizontalTwist order x t
  have hexponentialNorm :
      ‖Real.exp ((x / 2) ^ 2)‖ = Real.exp ((x / 2) ^ 2) :=
    Real.norm_of_nonneg
      (le_of_lt (Real.exp_pos ((x / 2) ^ 2)))
  exact Eq.trans
    (congrArg norm hidentity)
    (Eq.trans
      (norm_mul
        (Real.exp ((x / 2) ^ 2))
        (iteratedDeriv order realPhysicalGaussian (t - x / 2)))
      (congrArg
        (fun value : ℝ =>
          value *
            ‖iteratedDeriv order realPhysicalGaussian (t - x / 2)‖)
        hexponentialNorm))

/-- Every derivative norm of a horizontal Gaussian twist is integrable. -/
theorem integrable_norm_iteratedDeriv_realPhysicalGaussianHorizontalTwist
    (order : ℕ)
    (x : ℝ) :
    MeasureTheory.Integrable
      (fun t : ℝ =>
        ‖iteratedDeriv order
          (realPhysicalGaussianHorizontalTwist x) t‖) := by
  have htranslated :
      MeasureTheory.Integrable
        (fun t : ℝ =>
          ‖iteratedDeriv order realPhysicalGaussian (t - x / 2)‖) :=
    (integrable_norm_iteratedDeriv_realPhysicalGaussian order).comp_sub_right
      (x / 2)
  have hscaled :
      MeasureTheory.Integrable
        (fun t : ℝ =>
          Real.exp ((x / 2) ^ 2) *
            ‖iteratedDeriv order realPhysicalGaussian (t - x / 2)‖) :=
    htranslated.const_mul (Real.exp ((x / 2) ^ 2))
  have hfunction :
      (fun t : ℝ =>
        ‖iteratedDeriv order
          (realPhysicalGaussianHorizontalTwist x) t‖) =
      (fun t : ℝ =>
        Real.exp ((x / 2) ^ 2) *
          ‖iteratedDeriv order realPhysicalGaussian (t - x / 2)‖) := by
    funext t
    exact norm_iteratedDeriv_realPhysicalGaussianHorizontalTwist order x t
  exact Eq.mp
    (congrArg
      (fun function : ℝ → ℝ =>
        MeasureTheory.Integrable function MeasureTheory.volume)
      hfunction.symm)
    hscaled

/-- The derivative `L1` norm of a horizontal twist is exactly the untranslated
Gaussian derivative norm times the completion-of-square factor. -/
theorem integral_norm_iteratedDeriv_realPhysicalGaussianHorizontalTwist
    (order : ℕ)
    (x : ℝ) :
    (∫ t : ℝ,
        ‖iteratedDeriv order
          (realPhysicalGaussianHorizontalTwist x) t‖) =
      Real.exp ((x / 2) ^ 2) *
        ∫ t : ℝ,
          ‖iteratedDeriv order realPhysicalGaussian t‖ := by
  have hfunction :
      (fun t : ℝ =>
        ‖iteratedDeriv order
          (realPhysicalGaussianHorizontalTwist x) t‖) =
      (fun t : ℝ =>
        Real.exp ((x / 2) ^ 2) *
          ‖iteratedDeriv order realPhysicalGaussian (t - x / 2)‖) := by
    funext t
    exact norm_iteratedDeriv_realPhysicalGaussianHorizontalTwist order x t
  have htranslatedIntegral :
      (∫ t : ℝ,
          ‖iteratedDeriv order realPhysicalGaussian (t - x / 2)‖) =
        ∫ t : ℝ,
          ‖iteratedDeriv order realPhysicalGaussian t‖ := by
    let derivativeNorm : ℝ → ℝ :=
      fun t : ℝ => ‖iteratedDeriv order realPhysicalGaussian t‖
    have hsubFunction :
        (fun t : ℝ => derivativeNorm (t - x / 2)) =
          (fun t : ℝ => derivativeNorm (t + -(x / 2))) := by
      funext t
      exact congrArg derivativeNorm (sub_eq_add_neg t (x / 2))
    have htranslation :
        (∫ t : ℝ, derivativeNorm (t + -(x / 2))) =
          ∫ t : ℝ, derivativeNorm t :=
      MeasureTheory.integral_add_right_eq_self
        derivativeNorm
        (-(x / 2))
    exact Eq.trans
      (congrArg (fun function : ℝ → ℝ => ∫ t : ℝ, function t) hsubFunction)
      htranslation
  exact Eq.trans
    (congrArg (fun function : ℝ → ℝ => ∫ t : ℝ, function t) hfunction)
    (Eq.trans
      (MeasureTheory.integral_smul
        (Real.exp ((x / 2) ^ 2))
        (fun t : ℝ =>
          ‖iteratedDeriv order realPhysicalGaussian (t - x / 2)‖))
      (congrArg
        (fun value : ℝ => Real.exp ((x / 2) ^ 2) * value)
        htranslatedIntegral))

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
