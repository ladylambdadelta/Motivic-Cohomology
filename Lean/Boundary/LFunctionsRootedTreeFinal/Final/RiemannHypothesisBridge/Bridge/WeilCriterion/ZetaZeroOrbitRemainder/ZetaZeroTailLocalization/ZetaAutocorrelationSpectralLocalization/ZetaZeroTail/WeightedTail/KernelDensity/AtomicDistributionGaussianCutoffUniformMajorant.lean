import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.KernelDensity.AtomicDistributionGaussianAtomicTerm
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.KernelDensity.AtomicDistributionGaussianCutoffUniformPaleyWiener
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ProbeInterface.ZetaAdmissibleFunction.ZetaAdmissibleNormalizedScale

/-!
# Uniform completed-zero majorants for compact Gaussian cutoffs

This file owns the concrete targeted cutoff probe, its exact spectral
factorization, and the radius-uniform summable majorant required by Tannery's
theorem.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

/-- Real coordinate of a real-scaled completed-zero displacement. -/
theorem completedZero_scaledDisplacement_re
    (target rho : ZetaCompletedZeroCoordinate)
    (scale : ℝ) :
    ((scale : ℂ) * ((rho : ℂ) - (target : ℂ))).re =
      scale * ((rho : ℂ).re - (target : ℂ).re) := by
  exact Eq.trans
    (Complex.mul_re (scale : ℂ) ((rho : ℂ) - (target : ℂ)))
    (Eq.trans
      (congrArg₂ Sub.sub
        (congrArg₂ Mul.mul
          (Complex.ofReal_re scale)
          (Complex.sub_re (rho : ℂ) (target : ℂ)))
        (congrArg₂ Mul.mul
          (Complex.ofReal_im scale)
          (Complex.sub_im (rho : ℂ) (target : ℂ))))
      (Eq.trans
        (congrArg₂ Sub.sub
          (Eq.refl (scale * ((rho : ℂ).re - (target : ℂ).re)))
          (zero_mul ((rho : ℂ).im - (target : ℂ).im)))
        (sub_zero (scale * ((rho : ℂ).re - (target : ℂ).re)))))

/-- Imaginary coordinate of a real-scaled completed-zero displacement. -/
theorem completedZero_scaledDisplacement_im
    (target rho : ZetaCompletedZeroCoordinate)
    (scale : ℝ) :
    ((scale : ℂ) * ((rho : ℂ) - (target : ℂ))).im =
      scale * ((rho : ℂ).im - (target : ℂ).im) := by
  exact Eq.trans
    (Complex.mul_im (scale : ℂ) ((rho : ℂ) - (target : ℂ)))
    (Eq.trans
      (congrArg₂ Add.add
        (congrArg₂ Mul.mul
          (Complex.ofReal_re scale)
          (Complex.sub_im (rho : ℂ) (target : ℂ)))
        (congrArg₂ Mul.mul
          (Complex.ofReal_im scale)
          (Complex.sub_re (rho : ℂ) (target : ℂ))))
      (Eq.trans
        (congrArg₂ Add.add
          (Eq.refl (scale * ((rho : ℂ).im - (target : ℂ).im)))
          (zero_mul ((rho : ℂ).re - (target : ℂ).re)))
        (add_zero (scale * ((rho : ℂ).im - (target : ℂ).im)))))

/-- Cartesian decomposition of a real-scaled completed-zero displacement. -/
theorem completedZero_scaledDisplacement_eq_re_add_im_mul_I
    (target rho : ZetaCompletedZeroCoordinate)
    (scale : ℝ) :
    (scale : ℂ) * ((rho : ℂ) - (target : ℂ)) =
      (scale * ((rho : ℂ).re - (target : ℂ).re) : ℝ) +
        ((scale * ((rho : ℂ).im - (target : ℂ).im) : ℝ) : ℂ) *
          Complex.I := by
  let displacement : ℂ :=
    (scale : ℂ) * ((rho : ℂ) - (target : ℂ))
  exact Eq.trans
    (Complex.re_add_im displacement).symm
    (congrArg₂
      (fun realPart imaginaryPart : ℝ =>
        (realPart : ℂ) + (imaginaryPart : ℂ) * Complex.I)
      (completedZero_scaledDisplacement_re target rho scale)
      (completedZero_scaledDisplacement_im target rho scale))

/-- A positive real scale controls the horizontal completed-zero displacement. -/
theorem completedZero_scaledHorizontalDisplacement_abs_le
    (target rho : ZetaCompletedZeroCoordinate)
    (scale : ℝ)
    (hscale : 0 < scale) :
    |scale * ((rho : ℂ).re - (target : ℂ).re)| ≤ scale := by
  have hscaleAbsolute : |scale| = scale :=
    abs_of_pos hscale
  have hdisplacement :
      |(rho : ℂ).re - (target : ℂ).re| ≤ 1 :=
    completedZero_realDisplacement_abs_le_one rho target
  have hproduct :
      scale * |(rho : ℂ).re - (target : ℂ).re| ≤ scale * 1 :=
    mul_le_mul_of_nonneg_left hdisplacement (le_of_lt hscale)
  have hleft :
      |scale * ((rho : ℂ).re - (target : ℂ).re)| =
        scale * |(rho : ℂ).re - (target : ℂ).re| :=
    Eq.trans
      (abs_mul scale ((rho : ℂ).re - (target : ℂ).re))
      (congrArg
        (fun value : ℝ =>
          value * |(rho : ℂ).re - (target : ℂ).re|)
        hscaleAbsolute)
  have hright : scale * 1 = scale :=
    mul_one scale
  have hproposition :
      (scale * |(rho : ℂ).re - (target : ℂ).re| ≤ scale * 1) =
        (|scale * ((rho : ℂ).re - (target : ℂ).re)| ≤ scale) :=
    congrArg₂ LE.le hleft.symm hright
  exact Eq.mp hproposition hproduct

/-- Transport a shifted vertical spectral bound to centered-height coordinates. -/
theorem completedZero_shiftedVerticalBound_transport
    (target rho : ZetaCompletedZeroCoordinate)
    (scale bound : ℝ)
    (degree n : ℕ)
    (hspectralBound :
      ‖zetaSpectralEval
          (admissibleGaussianCutoffNat n)
          ((scale * ((rho : ℂ).re - (target : ℂ).re) : ℝ) +
            ((scale * ((rho : ℂ).im - (target : ℂ).im) : ℝ) : ℂ) *
              Complex.I)‖ ≤
        bound * (1 + |(rho : ℂ).im|) ^ (-(degree : ℤ))) :
    ‖zetaSpectralEval
        (admissibleGaussianCutoffNat n)
        ((scale : ℂ) * ((rho : ℂ) - (target : ℂ)))‖ ≤
      bound * zetaCompletedZeroCenteredHeight rho ^ (-(degree : ℤ)) := by
  have hargument :=
    completedZero_scaledDisplacement_eq_re_add_im_mul_I target rho scale
  have hleft :
      ‖zetaSpectralEval
          (admissibleGaussianCutoffNat n)
          ((scale * ((rho : ℂ).re - (target : ℂ).re) : ℝ) +
            ((scale * ((rho : ℂ).im - (target : ℂ).im) : ℝ) : ℂ) *
              Complex.I)‖ =
        ‖zetaSpectralEval
          (admissibleGaussianCutoffNat n)
          ((scale : ℂ) * ((rho : ℂ) - (target : ℂ)))‖ :=
    congrArg
      (fun argument : ℂ =>
        ‖zetaSpectralEval (admissibleGaussianCutoffNat n) argument‖)
      hargument.symm
  have hheight :
      zetaCompletedZeroCenteredHeight rho = 1 + |(rho : ℂ).im| :=
    Eq.trans
      (zetaCompletedZeroCenteredHeight_eq_one_add_norm_im rho)
      (congrArg (fun value : ℝ => 1 + value)
        (Real.norm_eq_abs (rho : ℂ).im))
  have hright :
      bound * (1 + |(rho : ℂ).im|) ^ (-(degree : ℤ)) =
        bound * zetaCompletedZeroCenteredHeight rho ^ (-(degree : ℤ)) :=
    congrArg
      (fun height : ℝ => bound * height ^ (-(degree : ℤ)))
      hheight.symm
  have hproposition := congrArg₂ LE.le hleft hright
  exact Eq.mp hproposition hspectralBound

/-- The concrete admissible compact probe approximating one scaled targeted
full Gaussian. -/
noncomputable def completedZeroTargetScaledGaussianCutoffProbe
    (target : ZetaCompletedZeroCoordinate)
    (scale : ℝ)
    (n : ℕ) : ZetaAdmissibleFunction :=
  finiteSpectralZeroOperator
    (completedZeroTargetExceptionalValues target 2 zero_le_two)
    (complexExponentialModulate
      (target : ℂ)
      (normalizedScale scale (admissibleGaussianCutoffNat n)))

/-- Exact completed-zero evaluation of the targeted scaled compact Gaussian
probe. -/
theorem zetaSpectralEval_completedZeroTargetScaledGaussianCutoffProbe
    (target rho : ZetaCompletedZeroCoordinate)
    (scale : ℝ)
    (hscale : 0 < scale)
    (n : ℕ) :
    zetaSpectralEval
        (completedZeroTargetScaledGaussianCutoffProbe target scale n)
        (rho : ℂ) =
      completedZeroTargetGaussianMultiplier target rho *
        zetaSpectralEval
          (admissibleGaussianCutoffNat n)
          ((scale : ℂ) * ((rho : ℂ) - (target : ℂ))) := by
  have hoperator :=
    zetaSpectralEval_finiteSpectralZeroOperator
      (completedZeroTargetExceptionalValues target 2 zero_le_two)
      (complexExponentialModulate
        (target : ℂ)
        (normalizedScale scale (admissibleGaussianCutoffNat n)))
      (rho : ℂ)
  have hmodulation :=
    zetaSpectralEval_complexExponentialModulate
      (target : ℂ)
      (rho : ℂ)
      (normalizedScale scale (admissibleGaussianCutoffNat n))
  have hscaleEvaluation :=
    zetaSpectralEval_normalizedScale
      scale hscale
      (admissibleGaussianCutoffNat n)
      ((rho : ℂ) - (target : ℂ))
  exact Eq.trans hoperator
    (Eq.trans
      (congrArg
        (fun value : ℂ =>
          completedZeroTargetGaussianMultiplier target rho * value)
        hmodulation)
      (congrArg
        (fun value : ℂ =>
          completedZeroTargetGaussianMultiplier target rho * value)
        hscaleEvaluation))

/-- Natural Gaussian cutoffs have vertical rapid-decay constants uniform in
the cutoff radius after a fixed positive scaling and completed-zero shift. -/
theorem zetaSpectralEval_admissibleGaussianCutoffNat_scaled_completedZero_uniformRapidDecay
    (target : ZetaCompletedZeroCoordinate)
    (scale : ℝ)
    (hscale : 0 < scale)
    (degree : ℕ) :
    ∃ bound : ℝ,
      0 < bound ∧
        ∀ n : ℕ,
          ∀ rho : ZetaCompletedZeroCoordinate,
            ‖zetaSpectralEval
                (admissibleGaussianCutoffNat n)
                ((scale : ℂ) * ((rho : ℂ) - (target : ℂ)))‖ ≤
              bound *
                zetaCompletedZeroCenteredHeight rho ^
                  (-(degree : ℤ)) := by
  obtain ⟨bound, hboundPositive, hbound⟩ :=
    admissibleGaussianCutoffNat_uniformPaleyWiener_shiftedScale
      (target : ℂ).im scale hscale degree
  have huniform :
      ∀ n : ℕ,
        ∀ rho : ZetaCompletedZeroCoordinate,
          ‖zetaSpectralEval
              (admissibleGaussianCutoffNat n)
              ((scale : ℂ) * ((rho : ℂ) - (target : ℂ)))‖ ≤
            bound *
              zetaCompletedZeroCenteredHeight rho ^
                (-(degree : ℤ)) := by
    intro n rho
    let horizontal : ℝ :=
      scale * ((rho : ℂ).re - (target : ℂ).re)
    have hhorizontal : |horizontal| ≤ scale :=
      completedZero_scaledHorizontalDisplacement_abs_le
        target rho scale hscale
    have hspectralBound :=
      hbound n horizontal (rho : ℂ).im hhorizontal
    exact completedZero_shiftedVerticalBound_transport
      target rho scale bound degree n hspectralBound
  
  exact ⟨bound, hboundPositive, huniform⟩

/-- Polynomial-growth atomic coefficients multiplied by all natural compact
Gaussian cutoffs have one summable completed-zero majorant, independent of
the cutoff radius. -/
theorem completedZeroTargetScaledGaussianCutoff_exists_summable_majorant
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (coefficient : ZetaCompletedZeroCoordinate → ℂ)
    (hgrowth : CompletedZeroAtomicPolynomialGrowth coefficient)
    (target : ZetaCompletedZeroCoordinate)
    (scale : ℝ)
    (hscale : 0 < scale) :
    ∃ majorant : ZetaCompletedZeroCoordinate → ℝ,
      Summable majorant ∧
        ∀ n : ℕ,
          ∀ rho : ZetaCompletedZeroCoordinate,
            ‖coefficient rho *
                zetaSpectralEval
                  (completedZeroTargetScaledGaussianCutoffProbe
                    target scale n)
                  (rho : ℂ)‖ ≤
              majorant rho := by
  have hmultiplierGrowth :
      CompletedZeroAtomicPolynomialGrowth
        (fun rho : ZetaCompletedZeroCoordinate =>
          completedZeroTargetGaussianMultiplier target rho) :=
    finiteSpectralZeroMultiplier_polynomialGrowth
      (completedZeroTargetExceptionalValues target 2 zero_le_two)
  have hcombinedGrowth :
      CompletedZeroAtomicPolynomialGrowth
        (fun rho : ZetaCompletedZeroCoordinate =>
          coefficient rho *
            completedZeroTargetGaussianMultiplier target rho) :=
    CompletedZeroAtomicPolynomialGrowth.mul
      coefficient
      (fun rho : ZetaCompletedZeroCoordinate =>
        completedZeroTargetGaussianMultiplier target rho)
      hgrowth
      hmultiplierGrowth
  let cutoffFamily :
      ℕ → ZetaCompletedZeroCoordinate → ℂ :=
    fun n rho =>
      zetaSpectralEval
        (admissibleGaussianCutoffNat n)
        ((scale : ℂ) * ((rho : ℂ) - (target : ℂ)))
  have hfamilyDecay :
      ∀ degree : ℕ,
        ∃ bound : ℝ,
          0 < bound ∧
            ∀ n : ℕ,
              ∀ rho : ZetaCompletedZeroCoordinate,
                ‖cutoffFamily n rho‖ ≤
                  bound *
                    zetaCompletedZeroCenteredHeight rho ^
                      (-(degree : ℤ)) :=
    fun degree =>
      zetaSpectralEval_admissibleGaussianCutoffNat_scaled_completedZero_uniformRapidDecay
        target scale hscale degree
  obtain ⟨majorant, hmajorantSummable, hcombinedBound⟩ :=
    CompletedZeroAtomicPolynomialGrowth.exists_summable_majorant_mul_of_uniformRapidDecay
      hbranch hpartialOneTwo hcompactOneTwo hfinite
      hpartialLeft hcompactBoundary
      (fun rho : ZetaCompletedZeroCoordinate =>
        coefficient rho *
          completedZeroTargetGaussianMultiplier target rho)
      cutoffFamily
      hcombinedGrowth
      hfamilyDecay
  have htargetBound :
      ∀ n : ℕ,
        ∀ rho : ZetaCompletedZeroCoordinate,
          ‖coefficient rho *
              zetaSpectralEval
                (completedZeroTargetScaledGaussianCutoffProbe
                  target scale n)
                (rho : ℂ)‖ ≤
            majorant rho := by
    intro n rho
    have hevaluation :=
      zetaSpectralEval_completedZeroTargetScaledGaussianCutoffProbe
        target rho scale hscale n
    have htermEquality :
        coefficient rho *
            zetaSpectralEval
              (completedZeroTargetScaledGaussianCutoffProbe
                target scale n)
              (rho : ℂ) =
          (coefficient rho *
              completedZeroTargetGaussianMultiplier target rho) *
            cutoffFamily n rho :=
      Eq.trans
        (congrArg (fun value : ℂ => coefficient rho * value) hevaluation)
        (mul_assoc
          (coefficient rho)
          (completedZeroTargetGaussianMultiplier target rho)
          (cutoffFamily n rho)).symm
    exact Eq.subst
      (motive := fun value : ℂ => ‖value‖ ≤ majorant rho)
      htermEquality.symm
      (hcombinedBound n rho)
  exact ⟨majorant, hmajorantSummable, htargetBound⟩

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
