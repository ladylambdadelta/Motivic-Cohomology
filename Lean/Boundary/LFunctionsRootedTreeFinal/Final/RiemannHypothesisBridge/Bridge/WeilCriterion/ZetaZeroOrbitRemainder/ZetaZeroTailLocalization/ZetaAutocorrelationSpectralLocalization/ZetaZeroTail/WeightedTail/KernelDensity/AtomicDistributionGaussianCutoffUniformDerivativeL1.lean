import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.KernelDensity.AtomicDistributionGaussianCutoffDerivativeBounds

/-!
# Uniform derivative L1 bounds for Gaussian cutoffs

Finite binomial derivative majorants are integrated term by term.  Translation
invariance removes the horizontal displacement, and completion of the square
provides one constant on the fixed horizontal strip.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

/-- One horizontal Gaussian derivative has a uniform `L1` bound on a symmetric
strip. -/
theorem integral_norm_iteratedDeriv_physicalGaussianHorizontalTwist_le_strip
    (order : ℕ)
    (scale x : ℝ)
    (hscale : 0 < scale)
    (hx : |x| ≤ scale) :
    (∫ t : ℝ,
        ‖iteratedDeriv order
          (physicalGaussianHorizontalTwist x) t‖) ≤
      Real.exp (scale ^ 2) *
        ∫ t : ℝ,
          ‖iteratedDeriv order realPhysicalGaussian t‖ := by
  have hexponential :=
    exp_halfSquare_le_exp_scaleSquare scale x hscale hx
  have hintegralNonnegative :
      0 ≤ ∫ t : ℝ,
        ‖iteratedDeriv order realPhysicalGaussian t‖ :=
    MeasureTheory.integral_nonneg
      (fun t : ℝ =>
        norm_nonneg (iteratedDeriv order realPhysicalGaussian t))
  have hscaled :=
    mul_le_mul_of_nonneg_right
      hexponential
      hintegralNonnegative
  exact Eq.subst
    (motive := fun left : ℝ =>
      left ≤
        Real.exp (scale ^ 2) *
          ∫ t : ℝ,
            ‖iteratedDeriv order realPhysicalGaussian t‖)
    (integral_norm_iteratedDeriv_physicalGaussianHorizontalTwist
      order x).symm
    hscaled

/-- The explicit uniform `L1` majorant before adding a positive margin. -/
noncomputable def admissibleGaussianCutoffHorizontalTwistDerivativeRawL1Bound
    (order : ℕ)
    (scale : ℝ) : ℝ :=
  ∑ index ∈ Finset.range (order + 1),
    ((order.choose index : ℝ) *
      admissibleGaussianScaledUnitBumpDerivativeBound index) *
      (Real.exp (scale ^ 2) *
        ∫ t : ℝ,
          ‖iteratedDeriv (order - index) realPhysicalGaussian t‖)

/-- The raw uniform derivative bound is nonnegative. -/
theorem admissibleGaussianCutoffHorizontalTwistDerivativeRawL1Bound_nonnegative
    (order : ℕ)
    (scale : ℝ) :
    0 ≤
      admissibleGaussianCutoffHorizontalTwistDerivativeRawL1Bound
        order scale := by
  exact Finset.sum_nonneg
    (fun index hindex =>
      mul_nonneg
        (mul_nonneg
          (Nat.cast_nonneg (order.choose index))
          (le_of_lt
            (admissibleGaussianScaledUnitBumpDerivativeBound_pos index)))
        (mul_nonneg
          (le_of_lt (Real.exp_pos (scale ^ 2)))
          (MeasureTheory.integral_nonneg
            (fun t : ℝ =>
              norm_nonneg
                (iteratedDeriv (order - index)
                  realPhysicalGaussian t)))))

/-- The positive uniform derivative `L1` bound. -/
noncomputable def admissibleGaussianCutoffHorizontalTwistDerivativeL1Bound
    (order : ℕ)
    (scale : ℝ) : ℝ :=
  admissibleGaussianCutoffHorizontalTwistDerivativeRawL1Bound order scale + 1

/-- The uniform derivative `L1` bound is positive. -/
theorem admissibleGaussianCutoffHorizontalTwistDerivativeL1Bound_pos
    (order : ℕ)
    (scale : ℝ) :
    0 <
      admissibleGaussianCutoffHorizontalTwistDerivativeL1Bound
        order scale :=
  add_pos_of_nonneg_of_pos
    (admissibleGaussianCutoffHorizontalTwistDerivativeRawL1Bound_nonnegative
      order scale)
    zero_lt_one

/-- Integrating the finite pointwise majorant gives the corresponding finite
sum of derivative `L1` norms. -/
theorem integral_admissibleGaussianCutoffHorizontalTwistDerivativeMajorant
    (order : ℕ)
    (x : ℝ) :
    (∫ t : ℝ,
      ∑ index ∈ Finset.range (order + 1),
        ((order.choose index : ℝ) *
          admissibleGaussianScaledUnitBumpDerivativeBound index) *
          ‖iteratedDeriv (order - index)
            (physicalGaussianHorizontalTwist x) t‖) =
      ∑ index ∈ Finset.range (order + 1),
        ((order.choose index : ℝ) *
          admissibleGaussianScaledUnitBumpDerivativeBound index) *
          (∫ t : ℝ,
            ‖iteratedDeriv (order - index)
              (physicalGaussianHorizontalTwist x) t‖) := by
  have htermIntegrable :
      ∀ index ∈ Finset.range (order + 1),
        MeasureTheory.Integrable
          (fun t : ℝ =>
            ((order.choose index : ℝ) *
              admissibleGaussianScaledUnitBumpDerivativeBound index) *
              ‖iteratedDeriv (order - index)
                (physicalGaussianHorizontalTwist x) t‖) := by
    intro index hindex
    exact
      (integrable_norm_iteratedDeriv_physicalGaussianHorizontalTwist
        (order - index) x).const_mul
          ((order.choose index : ℝ) *
            admissibleGaussianScaledUnitBumpDerivativeBound index)
  have hsumIntegral :=
    MeasureTheory.integral_finset_sum
      (s := Finset.range (order + 1))
      (f := fun (index : ℕ) (t : ℝ) =>
        ((order.choose index : ℝ) *
          admissibleGaussianScaledUnitBumpDerivativeBound index) *
          ‖iteratedDeriv (order - index)
            (physicalGaussianHorizontalTwist x) t‖)
      htermIntegrable
  have htermIntegral :
      ∀ index ∈ Finset.range (order + 1),
        (∫ t : ℝ,
          ((order.choose index : ℝ) *
            admissibleGaussianScaledUnitBumpDerivativeBound index) *
            ‖iteratedDeriv (order - index)
              (physicalGaussianHorizontalTwist x) t‖) =
          ((order.choose index : ℝ) *
            admissibleGaussianScaledUnitBumpDerivativeBound index) *
            (∫ t : ℝ,
              ‖iteratedDeriv (order - index)
                (physicalGaussianHorizontalTwist x) t‖) := by
    intro index hindex
    exact MeasureTheory.integral_smul
      ((order.choose index : ℝ) *
        admissibleGaussianScaledUnitBumpDerivativeBound index)
      (fun t : ℝ =>
        ‖iteratedDeriv (order - index)
          (physicalGaussianHorizontalTwist x) t‖)
  exact Eq.trans hsumIntegral
    (Finset.sum_congr rfl htermIntegral)

/-- The integrated finite derivative majorant is uniformly bounded on the
symmetric strip. -/
theorem integral_admissibleGaussianCutoffHorizontalTwistDerivativeMajorant_le_rawBound
    (order : ℕ)
    (scale x : ℝ)
    (hscale : 0 < scale)
    (hx : |x| ≤ scale) :
    (∫ t : ℝ,
      ∑ index ∈ Finset.range (order + 1),
        ((order.choose index : ℝ) *
          admissibleGaussianScaledUnitBumpDerivativeBound index) *
          ‖iteratedDeriv (order - index)
            (physicalGaussianHorizontalTwist x) t‖) ≤
      admissibleGaussianCutoffHorizontalTwistDerivativeRawL1Bound
        order scale := by
  have hintegralIdentity :=
    integral_admissibleGaussianCutoffHorizontalTwistDerivativeMajorant
      order x
  have hsumBound :
      (∑ index ∈ Finset.range (order + 1),
        ((order.choose index : ℝ) *
          admissibleGaussianScaledUnitBumpDerivativeBound index) *
          (∫ t : ℝ,
            ‖iteratedDeriv (order - index)
              (physicalGaussianHorizontalTwist x) t‖)) ≤
      ∑ index ∈ Finset.range (order + 1),
        ((order.choose index : ℝ) *
          admissibleGaussianScaledUnitBumpDerivativeBound index) *
          (Real.exp (scale ^ 2) *
            ∫ t : ℝ,
              ‖iteratedDeriv (order - index)
                realPhysicalGaussian t‖) := by
    exact Finset.sum_le_sum
      (fun index hindex =>
        mul_le_mul_of_nonneg_left
          (integral_norm_iteratedDeriv_physicalGaussianHorizontalTwist_le_strip
            (order - index) scale x hscale hx)
          (mul_nonneg
            (Nat.cast_nonneg (order.choose index))
            (le_of_lt
              (admissibleGaussianScaledUnitBumpDerivativeBound_pos index))))
  exact Eq.subst
    (motive := fun left : ℝ =>
      left ≤
        admissibleGaussianCutoffHorizontalTwistDerivativeRawL1Bound
          order scale)
    hintegralIdentity.symm
    hsumBound

/-- All natural cutoff horizontal twists have one derivative `L1` bound on a
fixed symmetric strip. -/
theorem integral_norm_iteratedDeriv_zetaPaleyWienerHorizontalTwist_admissibleGaussianCutoffNat_le
    (order : ℕ)
    (scale : ℝ)
    (hscale : 0 < scale)
    (n : ℕ)
    (x : ℝ)
    (hx : |x| ≤ scale) :
    (∫ t : ℝ,
      ‖iteratedDeriv order
        (fun u : ℝ =>
          zetaPaleyWienerHorizontalTwist
            (admissibleGaussianCutoffNat n) x u)
        t‖) ≤
      admissibleGaussianCutoffHorizontalTwistDerivativeL1Bound
        order scale := by
  let source : ℝ → ℂ :=
    fun u : ℝ =>
      zetaPaleyWienerHorizontalTwist
        (admissibleGaussianCutoffNat n) x u
  let majorant : ℝ → ℝ :=
    fun t : ℝ =>
      ∑ index ∈ Finset.range (order + 1),
        ((order.choose index : ℝ) *
          admissibleGaussianScaledUnitBumpDerivativeBound index) *
          ‖iteratedDeriv (order - index)
            (physicalGaussianHorizontalTwist x) t‖
  have hsourceIntegrable :
      MeasureTheory.Integrable
        (fun t : ℝ => ‖iteratedDeriv order source t‖) :=
    integrable_norm_iteratedDeriv_zetaPaleyWienerHorizontalTwist_admissibleGaussianCutoffNat
      order n x
  have hmajorantIntegrable : MeasureTheory.Integrable majorant := by
    exact MeasureTheory.integrable_finset_sum
      (Finset.range (order + 1))
      (fun index hindex =>
        (integrable_norm_iteratedDeriv_physicalGaussianHorizontalTwist
          (order - index) x).const_mul
            ((order.choose index : ℝ) *
              admissibleGaussianScaledUnitBumpDerivativeBound index))
  have hpointwise : ∀ t : ℝ, ‖iteratedDeriv order source t‖ ≤ majorant t :=
    fun t =>
      norm_iteratedDeriv_zetaPaleyWienerHorizontalTwist_admissibleGaussianCutoffNat_le_majorant
        order n x t
  have hintegralBound :
      (∫ t : ℝ, ‖iteratedDeriv order source t‖) ≤
        ∫ t : ℝ, majorant t :=
    MeasureTheory.integral_mono
      hsourceIntegrable
      hmajorantIntegrable
      hpointwise
  have hmajorantBound :
      (∫ t : ℝ, majorant t) ≤
        admissibleGaussianCutoffHorizontalTwistDerivativeRawL1Bound
          order scale :=
    integral_admissibleGaussianCutoffHorizontalTwistDerivativeMajorant_le_rawBound
      order scale x hscale hx
  have hmargin :
      admissibleGaussianCutoffHorizontalTwistDerivativeRawL1Bound order scale ≤
        admissibleGaussianCutoffHorizontalTwistDerivativeL1Bound order scale :=
    le_add_of_nonneg_right zero_le_one
  exact le_trans hintegralBound
    (le_trans hmajorantBound hmargin)

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
