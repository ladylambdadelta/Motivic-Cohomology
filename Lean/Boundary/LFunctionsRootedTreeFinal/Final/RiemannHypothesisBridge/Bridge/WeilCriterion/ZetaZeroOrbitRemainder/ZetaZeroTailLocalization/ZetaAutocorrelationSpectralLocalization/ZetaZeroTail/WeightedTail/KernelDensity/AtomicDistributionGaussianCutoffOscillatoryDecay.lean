import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.KernelDensity.AtomicDistributionGaussianCutoffUniformDerivativeL1
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.IteratedOscillatoryKernel.Owner

/-!
# Uniform oscillatory decay for Gaussian cutoffs

The existing Paley-Wiener integration-by-parts recurrence is applied uniformly
to the natural cutoff family.  Its terminal estimate is the derivative `L1`
bound, not a support-length seminorm.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

/-- An iterated oscillatory integral is bounded by the `L1` norm of its source
derivative. -/
theorem norm_zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_le_derivativeL1
    (f : ZetaAdmissibleFunction)
    (order : ℕ)
    (x frequency : ℝ) :
    ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral
        f order x frequency‖ ≤
      ∫ t : ℝ,
        ‖zetaPaleyWienerHorizontalTwistIteratedDerivative
          f order x t‖ := by
  let kernel : ℝ → ℂ :=
    fun t : ℝ =>
      zetaPaleyWienerHorizontalTwistIteratedDerivative f order x t *
        zetaPaleyWienerVerticalOscillation frequency t
  have hnormIntegral :
      ‖∫ t : ℝ, kernel t‖ ≤ ∫ t : ℝ, ‖kernel t‖ :=
    MeasureTheory.norm_integral_le_integral_norm kernel
  have hdefinition :
      zetaPaleyWienerIteratedDerivativeOscillatoryIntegral
          f order x frequency =
        ∫ t : ℝ, kernel t :=
    Eq.refl _
  have hkernelNorm :
      (fun t : ℝ => ‖kernel t‖) =
        (fun t : ℝ =>
          ‖zetaPaleyWienerHorizontalTwistIteratedDerivative
            f order x t‖) := by
    funext t
    have hoscillation :
        ‖zetaPaleyWienerVerticalOscillation frequency t‖ = 1 :=
      zetaPaleyWienerVerticalOscillation_norm_eq_one frequency t
    exact Eq.trans
      (norm_mul
        (zetaPaleyWienerHorizontalTwistIteratedDerivative f order x t)
        (zetaPaleyWienerVerticalOscillation frequency t))
      (Eq.trans
        (congrArg
          (fun value : ℝ =>
            ‖zetaPaleyWienerHorizontalTwistIteratedDerivative
              f order x t‖ * value)
          hoscillation)
        (mul_one
          ‖zetaPaleyWienerHorizontalTwistIteratedDerivative
            f order x t‖))
  exact Eq.subst
    (motive := fun left : ℂ =>
      ‖left‖ ≤
        ∫ t : ℝ,
          ‖zetaPaleyWienerHorizontalTwistIteratedDerivative
            f order x t‖)
    hdefinition.symm
    (Eq.subst
      (motive := fun right : ℝ =>
        ‖∫ t : ℝ, kernel t‖ ≤ right)
      (congrArg (fun function : ℝ → ℝ => ∫ t : ℝ, function t)
        hkernelNorm)
      hnormIntegral)

/-- The project iterated derivative source is definitionally the ordinary
iterated derivative used by the cutoff `L1` owner. -/
theorem zetaPaleyWienerHorizontalTwistIteratedDerivative_cutoff_eq
    (order n : ℕ)
    (x t : ℝ) :
    zetaPaleyWienerHorizontalTwistIteratedDerivative
        (admissibleGaussianCutoffNat n) order x t =
      iteratedDeriv order
        (fun u : ℝ =>
          zetaPaleyWienerHorizontalTwist
            (admissibleGaussianCutoffNat n) x u)
        t :=
  Eq.refl _

/-- Uniform zero-order oscillatory control for an arbitrary starting
derivative from a supplied derivative `L1` bound. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_cutoff_uniformBound_of_l1Bound
    (scale : ℝ)
    (start : ℕ)
    (derivativeL1Bound : ℝ)
    (hderivativeL1Bound :
      ∀ n : ℕ,
        ∀ x : ℝ,
          |x| ≤ scale →
            (∫ t : ℝ,
              ‖iteratedDeriv start
                (fun u : ℝ =>
                  zetaPaleyWienerHorizontalTwist
                    (admissibleGaussianCutoffNat n) x u)
                t‖) ≤ derivativeL1Bound) :
    ∀ n : ℕ,
      ∀ x frequency : ℝ,
        |x| ≤ scale →
          ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral
              (admissibleGaussianCutoffNat n) start x frequency‖ ≤
            derivativeL1Bound := by
  intro n x frequency hx
  have hoscillatory :=
    norm_zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_le_derivativeL1
      (admissibleGaussianCutoffNat n) start x frequency
  have hsourceIntegral :
      (∫ t : ℝ,
        ‖zetaPaleyWienerHorizontalTwistIteratedDerivative
          (admissibleGaussianCutoffNat n) start x t‖) =
      ∫ t : ℝ,
        ‖iteratedDeriv start
          (fun u : ℝ =>
            zetaPaleyWienerHorizontalTwist
              (admissibleGaussianCutoffNat n) x u)
          t‖ := by
    exact congrArg
      (fun function : ℝ → ℝ => ∫ t : ℝ, function t)
      (funext
        (fun t =>
          congrArg norm
            (zetaPaleyWienerHorizontalTwistIteratedDerivative_cutoff_eq
              start n x t)))
  have hderivativeIntegral :=
    hderivativeL1Bound n x hx
  exact le_trans hoscillatory
    (Eq.subst
      (motive := fun left : ℝ =>
        left ≤ derivativeL1Bound)
      hsourceIntegral.symm
      hderivativeIntegral)

/-- High-frequency decay for the natural cutoff family, uniform in the cutoff
radius and horizontal strip coordinate. -/
theorem admissibleGaussianCutoffNat_iteratedOscillatoryIntegral_uniform_highFrequency_decay
    (scale : ℝ)
    (hscale : 0 < scale)
    (start degree : ℕ) :
    ∃ bound : ℝ,
      0 < bound ∧
        ∀ n : ℕ,
          ∀ x frequency : ℝ,
            |x| ≤ scale →
              1 ≤ ‖frequency‖ →
                ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral
                    (admissibleGaussianCutoffNat n)
                    start x frequency‖ ≤
                  bound *
                    (1 + ‖frequency‖) ^ (-(degree : ℤ)) := by
  induction degree generalizing start with
  | zero =>
      match
          exists_admissibleGaussianCutoffHorizontalTwistDerivativeL1Bound
            start scale hscale with
      | ⟨bound, hboundPositive, hboundControls⟩ =>
          exact Exists.intro bound (And.intro hboundPositive (by
            intro n x frequency hx hfrequency
            have hraw :=
              zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_cutoff_uniformBound_of_l1Bound
                scale start bound hboundControls n x frequency hx
            have hweight :
                bound * (1 + ‖frequency‖) ^ (-(0 : ℤ)) = bound :=
              Eq.trans
                (congrArg (fun value : ℝ => bound * value)
                  (zetaPaleyWiener_zeroDecayWeight frequency))
                (mul_one bound)
            exact Eq.subst
              (motive := fun right : ℝ =>
                ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral
                  (admissibleGaussianCutoffNat n) start x frequency‖ ≤ right)
              hweight.symm
              hraw))
  | succ degree ih =>
      obtain ⟨nextBound, hnextBoundPositive, hnextBound⟩ :=
        ih (start + 1)
      let bound : ℝ := nextBound * 2
      have hboundPositive : 0 < bound :=
        mul_pos hnextBoundPositive zero_lt_two
      have hdecay :
          ∀ n : ℕ,
            ∀ x frequency : ℝ,
              |x| ≤ scale →
                1 ≤ ‖frequency‖ →
                  ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral
                      (admissibleGaussianCutoffNat n)
                      start x frequency‖ ≤
                    bound *
                      (1 + ‖frequency‖) ^ (-((Nat.succ degree : ℕ) : ℤ)) := by
        intro n x frequency hx hfrequency
        obtain ⟨supportInterval⟩ :=
          exists_zetaPaleyWienerSupportInterval
            (admissibleGaussianCutoffNat n)
        have hfrequencyNonzero : (frequency : ℂ) ≠ 0 :=
          zetaPaleyWienerVerticalFrequency_ne_zero_of_high hfrequency
        have hparts :=
          zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_norm_le_inverse_mul_succ
            (admissibleGaussianCutoffNat n)
            supportInterval
            start x frequency hfrequencyNonzero
        have hnext :=
          hnextBound n x frequency hx hfrequency
        have hinverseNonnegative : 0 ≤ ‖(frequency : ℂ)⁻¹‖ :=
          norm_nonneg ((frequency : ℂ)⁻¹)
        have hscaledNext :
            ‖(frequency : ℂ)⁻¹‖ *
                ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral
                  (admissibleGaussianCutoffNat n)
                  (start + 1) x frequency‖ ≤
              ‖(frequency : ℂ)⁻¹‖ *
                (nextBound *
                  (1 + ‖frequency‖) ^ (-(degree : ℤ))) :=
          mul_le_mul_of_nonneg_left hnext hinverseNonnegative
        have hweight :=
          zetaPaleyWiener_inverseReal_mul_realWeight_le_successor_highFrequency
            frequency degree hfrequency
        have hnextBoundNonnegative : 0 ≤ nextBound :=
          le_of_lt hnextBoundPositive
        have hreassociate :
            ‖(frequency : ℂ)⁻¹‖ *
                (nextBound *
                  (1 + ‖frequency‖) ^ (-(degree : ℤ))) =
              nextBound *
                (‖(frequency : ℂ)⁻¹‖ *
                  (1 + ‖frequency‖) ^ (-(degree : ℤ))) := by
          have hfirstAssociation :
              ‖(frequency : ℂ)⁻¹‖ *
                  (nextBound *
                    (1 + ‖frequency‖) ^ (-(degree : ℤ))) =
                (‖(frequency : ℂ)⁻¹‖ * nextBound) *
                  (1 + ‖frequency‖) ^ (-(degree : ℤ)) :=
            (mul_assoc
              ‖(frequency : ℂ)⁻¹‖ nextBound
              ((1 + ‖frequency‖) ^ (-(degree : ℤ)))).symm
          exact Eq.trans
            hfirstAssociation
            (Eq.trans
              (congrArg
                (fun value : ℝ =>
                  value * (1 + ‖frequency‖) ^ (-(degree : ℤ)))
                (mul_comm ‖(frequency : ℂ)⁻¹‖ nextBound))
              (mul_assoc nextBound ‖(frequency : ℂ)⁻¹‖
                ((1 + ‖frequency‖) ^ (-(degree : ℤ)))))
        have hweighted :
            nextBound *
                (‖(frequency : ℂ)⁻¹‖ *
                  (1 + ‖frequency‖) ^ (-(degree : ℤ))) ≤
              nextBound *
                (2 *
                  (1 + ‖frequency‖) ^
                    (-((Nat.succ degree : ℕ) : ℤ))) :=
          mul_le_mul_of_nonneg_left hweight hnextBoundNonnegative
        have htarget :
            nextBound *
                (2 *
                  (1 + ‖frequency‖) ^
                    (-((Nat.succ degree : ℕ) : ℤ))) =
              bound *
                (1 + ‖frequency‖) ^
                  (-((Nat.succ degree : ℕ) : ℤ)) :=
          (mul_assoc nextBound 2
            ((1 + ‖frequency‖) ^
              (-((Nat.succ degree : ℕ) : ℤ)))).symm
        exact le_trans hparts
          (le_trans hscaledNext
            (Eq.subst
              (motive := fun left : ℝ =>
                left ≤
                  bound *
                    (1 + ‖frequency‖) ^
                      (-((Nat.succ degree : ℕ) : ℤ)))
              hreassociate.symm
              (le_trans hweighted (le_of_eq htarget))))
      exact Exists.intro bound (And.intro hboundPositive hdecay)

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
