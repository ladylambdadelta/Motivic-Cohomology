import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.KernelDensity.AtomicDistributionGaussianDecay

/-!
# Summability of polynomial-growth atomic families

Jensen counting converts arbitrary negative-height decay into summability after
it is multiplied by a completed-zero coefficient of polynomial growth.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

/-- Polynomial atomic coefficients multiplied by any sufficiently rapid
completed-zero decay family are summable under the Jensen counting bound. -/
theorem CompletedZeroAtomicPolynomialGrowth.summable_mul_of_rapidDecay
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (coefficient decay : ZetaCompletedZeroCoordinate → ℂ)
    (hgrowth : CompletedZeroAtomicPolynomialGrowth coefficient)
    (hdecay :
      ∀ degree : ℕ,
        ∃ bound : ℝ,
          0 < bound ∧
          ∀ rho : ZetaCompletedZeroCoordinate,
            ‖decay rho‖ ≤
              bound *
                zetaCompletedZeroCenteredHeight rho ^ (-(degree : ℤ))) :
    Summable (fun rho => coefficient rho * decay rho) := by
  obtain ⟨countBound, countDegree, hcountBoundPositive, hcount⟩ :=
    exists_completedZeroMultiplicityCounting_height_bound
      hbranch hpartialOneTwo hcompactOneTwo hfinite
      hpartialLeft hcompactBoundary
  obtain ⟨growthBound, growthDegree,
      hgrowthBoundNonnegative, hgrowthEstimate⟩ := hgrowth
  let positiveGrowthBound : ℝ := growthBound + 1
  have hpositiveGrowthBound : 0 < positiveGrowthBound :=
    add_pos_of_nonneg_of_pos hgrowthBoundNonnegative zero_lt_one
  have hgrowthEstimatePositive :
      ∀ rho : ZetaCompletedZeroCoordinate,
        ‖coefficient rho‖ ≤
          positiveGrowthBound *
            zetaCompletedZeroCenteredHeight rho ^ (growthDegree : ℤ) := by
    intro rho
    have hpowerNonnegative :
        0 ≤ zetaCompletedZeroCenteredHeight rho ^ growthDegree :=
      pow_nonneg
        (le_trans zero_le_one
          (zetaCompletedZeroCenteredHeight_ge_one rho))
        growthDegree
    have hboundIncrease :
        growthBound * zetaCompletedZeroCenteredHeight rho ^ growthDegree ≤
          positiveGrowthBound *
            zetaCompletedZeroCenteredHeight rho ^ growthDegree :=
      mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right zero_le_one)
        hpowerNonnegative
    have hnaturalIntegerPower :
        zetaCompletedZeroCenteredHeight rho ^ growthDegree =
          zetaCompletedZeroCenteredHeight rho ^ (growthDegree : ℤ) :=
      (zpow_natCast
        (zetaCompletedZeroCenteredHeight rho) growthDegree).symm
    exact le_trans (hgrowthEstimate rho)
      (Eq.subst
        (motive := fun value : ℝ =>
          growthBound * zetaCompletedZeroCenteredHeight rho ^ growthDegree ≤
            positiveGrowthBound * value)
        hnaturalIntegerPower.symm
        hboundIncrease)
  let decayDegree : ℕ := growthDegree + (countDegree + 3) + 1
  obtain ⟨decayBound, hdecayBoundPositive, hdecayEstimate⟩ :=
    hdecay decayDegree
  have henvelopeSummable :
      Summable
        (fun rho : ZetaCompletedZeroCoordinate =>
          zetaZeroMultiplicityTransformEnvelope
            (positiveGrowthBound * decayBound) countDegree rho) :=
    summable_zetaZeroMultiplicityTransformEnvelope_of_counting_bound
      (positiveGrowthBound * decayBound)
      countBound countDegree 0 hcountBoundPositive hcount
  have htermBound :
      ∀ rho : ZetaCompletedZeroCoordinate,
        ‖coefficient rho * decay rho‖ ≤
          zetaZeroMultiplicityTransformEnvelope
            (positiveGrowthBound * decayBound) countDegree rho := by
    intro rho
    have hdecayNormNonnegative : 0 ≤ ‖decay rho‖ :=
      norm_nonneg (decay rho)
    have hgrowthEnvelopeNonnegative :
        0 ≤ positiveGrowthBound *
          zetaCompletedZeroCenteredHeight rho ^ (growthDegree : ℤ) :=
      mul_nonneg (le_of_lt hpositiveGrowthBound)
        (zpow_nonneg
          (le_trans zero_le_one
            (zetaCompletedZeroCenteredHeight_ge_one rho))
          (growthDegree : ℤ))
    have hproductBound :
        ‖coefficient rho‖ * ‖decay rho‖ ≤
          (positiveGrowthBound *
              zetaCompletedZeroCenteredHeight rho ^ (growthDegree : ℤ)) *
            (decayBound *
              zetaCompletedZeroCenteredHeight rho ^ (-(decayDegree : ℤ))) :=
      mul_le_mul
        (hgrowthEstimatePositive rho)
        (hdecayEstimate rho)
        hdecayNormNonnegative
        hgrowthEnvelopeNonnegative
    have hproductEnvelope :
        (positiveGrowthBound *
              zetaCompletedZeroCenteredHeight rho ^ (growthDegree : ℤ)) *
            (decayBound *
              zetaCompletedZeroCenteredHeight rho ^ (-(decayDegree : ℤ))) =
          zetaZeroGrowthDecayProductEnvelope
            positiveGrowthBound growthDegree decayBound decayDegree rho :=
      (zetaZeroGrowthDecayProductEnvelope_eq_factorProduct
        positiveGrowthBound growthDegree decayBound decayDegree rho).symm
    have hlargeDecay :
        zetaZeroGrowthDecayProductEnvelope
            positiveGrowthBound growthDegree decayBound decayDegree rho ≤
          zetaZeroMultiplicityTransformEnvelope
            (positiveGrowthBound * decayBound) countDegree rho :=
      zetaZeroGrowthDecayProductEnvelope_le_transformEnvelope_of_largeDecay
        positiveGrowthBound growthDegree decayBound countDegree
        hpositiveGrowthBound hdecayBoundPositive rho
    exact le_trans
      (Eq.subst
        (motive := fun value : ℝ =>
          value ≤
            zetaZeroGrowthDecayProductEnvelope
              positiveGrowthBound growthDegree decayBound decayDegree rho)
        (norm_mul (coefficient rho) (decay rho)).symm
        (Eq.subst
          (motive := fun value : ℝ =>
            ‖coefficient rho‖ * ‖decay rho‖ ≤ value)
          hproductEnvelope.symm
          hproductBound))
      hlargeDecay
  exact Summable.of_norm_bounded
    (fun rho : ZetaCompletedZeroCoordinate =>
      zetaZeroMultiplicityTransformEnvelope
        (positiveGrowthBound * decayBound) countDegree rho)
    henvelopeSummable
    htermBound

/-- A polynomial-growth atomic coefficient multiplied by a family with one
uniform rapid-decay estimate has a summable norm majorant independent of the
family parameter. -/
theorem CompletedZeroAtomicPolynomialGrowth.exists_summable_majorant_mul_of_uniformRapidDecay
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (coefficient : ZetaCompletedZeroCoordinate → ℂ)
    (family : ℕ → ZetaCompletedZeroCoordinate → ℂ)
    (hgrowth : CompletedZeroAtomicPolynomialGrowth coefficient)
    (hdecay :
      ∀ degree : ℕ,
        ∃ bound : ℝ,
          0 < bound ∧
          ∀ n : ℕ,
            ∀ rho : ZetaCompletedZeroCoordinate,
              ‖family n rho‖ ≤
                bound *
                  zetaCompletedZeroCenteredHeight rho ^ (-(degree : ℤ))) :
    ∃ majorant : ZetaCompletedZeroCoordinate → ℝ,
      Summable majorant ∧
        ∀ n : ℕ,
          ∀ rho : ZetaCompletedZeroCoordinate,
            ‖coefficient rho * family n rho‖ ≤ majorant rho := by
  obtain ⟨countBound, countDegree, hcountBoundPositive, hcount⟩ :=
    exists_completedZeroMultiplicityCounting_height_bound
      hbranch hpartialOneTwo hcompactOneTwo hfinite
      hpartialLeft hcompactBoundary
  obtain ⟨growthBound, growthDegree,
      hgrowthBoundNonnegative, hgrowthEstimate⟩ := hgrowth
  let positiveGrowthBound : ℝ := growthBound + 1
  have hpositiveGrowthBound : 0 < positiveGrowthBound :=
    add_pos_of_nonneg_of_pos hgrowthBoundNonnegative zero_lt_one
  have hgrowthEstimatePositive :
      ∀ rho : ZetaCompletedZeroCoordinate,
        ‖coefficient rho‖ ≤
          positiveGrowthBound *
            zetaCompletedZeroCenteredHeight rho ^ (growthDegree : ℤ) := by
    intro rho
    have hpowerNonnegative :
        0 ≤ zetaCompletedZeroCenteredHeight rho ^ growthDegree :=
      pow_nonneg
        (le_trans zero_le_one
          (zetaCompletedZeroCenteredHeight_ge_one rho))
        growthDegree
    have hboundIncrease :
        growthBound * zetaCompletedZeroCenteredHeight rho ^ growthDegree ≤
          positiveGrowthBound *
            zetaCompletedZeroCenteredHeight rho ^ growthDegree :=
      mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right zero_le_one)
        hpowerNonnegative
    have hnaturalIntegerPower :
        zetaCompletedZeroCenteredHeight rho ^ growthDegree =
          zetaCompletedZeroCenteredHeight rho ^ (growthDegree : ℤ) :=
      (zpow_natCast
        (zetaCompletedZeroCenteredHeight rho) growthDegree).symm
    exact le_trans (hgrowthEstimate rho)
      (Eq.subst
        (motive := fun value : ℝ =>
          growthBound * zetaCompletedZeroCenteredHeight rho ^ growthDegree ≤
            positiveGrowthBound * value)
        hnaturalIntegerPower.symm
        hboundIncrease)
  let decayDegree : ℕ := growthDegree + (countDegree + 3) + 1
  obtain ⟨decayBound, hdecayBoundPositive, hdecayEstimate⟩ :=
    hdecay decayDegree
  let majorant : ZetaCompletedZeroCoordinate → ℝ :=
    fun rho =>
      zetaZeroMultiplicityTransformEnvelope
        (positiveGrowthBound * decayBound) countDegree rho
  have hmajorantSummable : Summable majorant :=
    summable_zetaZeroMultiplicityTransformEnvelope_of_counting_bound
      (positiveGrowthBound * decayBound)
      countBound countDegree 0 hcountBoundPositive hcount
  have htermBound :
      ∀ n : ℕ,
        ∀ rho : ZetaCompletedZeroCoordinate,
          ‖coefficient rho * family n rho‖ ≤ majorant rho := by
    intro n rho
    have hdecayNormNonnegative : 0 ≤ ‖family n rho‖ :=
      norm_nonneg (family n rho)
    have hgrowthEnvelopeNonnegative :
        0 ≤ positiveGrowthBound *
          zetaCompletedZeroCenteredHeight rho ^ (growthDegree : ℤ) :=
      mul_nonneg (le_of_lt hpositiveGrowthBound)
        (zpow_nonneg
          (le_trans zero_le_one
            (zetaCompletedZeroCenteredHeight_ge_one rho))
          (growthDegree : ℤ))
    have hproductBound :
        ‖coefficient rho‖ * ‖family n rho‖ ≤
          (positiveGrowthBound *
              zetaCompletedZeroCenteredHeight rho ^ (growthDegree : ℤ)) *
            (decayBound *
              zetaCompletedZeroCenteredHeight rho ^ (-(decayDegree : ℤ))) :=
      mul_le_mul
        (hgrowthEstimatePositive rho)
        (hdecayEstimate n rho)
        hdecayNormNonnegative
        hgrowthEnvelopeNonnegative
    have hproductEnvelope :
        (positiveGrowthBound *
              zetaCompletedZeroCenteredHeight rho ^ (growthDegree : ℤ)) *
            (decayBound *
              zetaCompletedZeroCenteredHeight rho ^ (-(decayDegree : ℤ))) =
          zetaZeroGrowthDecayProductEnvelope
            positiveGrowthBound growthDegree decayBound decayDegree rho :=
      (zetaZeroGrowthDecayProductEnvelope_eq_factorProduct
        positiveGrowthBound growthDegree decayBound decayDegree rho).symm
    have hlargeDecay :
        zetaZeroGrowthDecayProductEnvelope
            positiveGrowthBound growthDegree decayBound decayDegree rho ≤
          majorant rho :=
      zetaZeroGrowthDecayProductEnvelope_le_transformEnvelope_of_largeDecay
        positiveGrowthBound growthDegree decayBound countDegree
        hpositiveGrowthBound hdecayBoundPositive rho
    exact le_trans
      (Eq.subst
        (motive := fun value : ℝ =>
          value ≤
            zetaZeroGrowthDecayProductEnvelope
              positiveGrowthBound growthDegree decayBound decayDegree rho)
        (norm_mul (coefficient rho) (family n rho)).symm
        (Eq.subst
          (motive := fun value : ℝ =>
            ‖coefficient rho‖ * ‖family n rho‖ ≤ value)
          hproductEnvelope.symm
          hproductBound))
      hlargeDecay
  exact ⟨majorant, hmajorantSummable, htermBound⟩

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
