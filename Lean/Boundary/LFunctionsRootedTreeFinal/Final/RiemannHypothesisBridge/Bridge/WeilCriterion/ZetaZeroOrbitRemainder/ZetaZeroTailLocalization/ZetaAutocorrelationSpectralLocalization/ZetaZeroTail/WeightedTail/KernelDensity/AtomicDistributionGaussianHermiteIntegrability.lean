import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.KernelDensity.AtomicDistributionGaussianHermite
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.KernelDensity.AtomicDistributionGaussianRealDecay

/-!
# Polynomially weighted Gaussian integrability

Splitting a positive Gaussian rate in half leaves one half to absorb every
polynomial height and one integrable half as the final majorant.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

/-- Every natural power of the canonical height is integrable against a
positive-rate real Gaussian. -/
theorem integrable_centeredHeight_pow_mul_realGaussian
    (rate : ℝ)
    (hrate : 0 < rate)
    (degree : ℕ) :
    MeasureTheory.Integrable
      (fun t : ℝ =>
        (1 + |t|) ^ degree * Real.exp (-rate * t ^ 2)) := by
  let halfRate : ℝ := rate / 2
  have hhalfRatePositive : 0 < halfRate :=
    div_pos hrate zero_lt_two
  obtain ⟨bound, hboundPositive, hhalfDecay⟩ :=
    exists_shiftedRealGaussian_centeredHeight_decay
      halfRate 0 hhalfRatePositive degree
  have hweightedHalfBound :
      ∀ t : ℝ,
        (1 + |t|) ^ degree *
            Real.exp (-halfRate * t ^ 2) ≤
          bound := by
    intro t
    let height : ℝ := 1 + |t|
    have hheightPositive : 0 < height :=
      add_pos_of_pos_of_nonneg zero_lt_one (abs_nonneg t)
    have hheightPowerPositive : 0 < height ^ degree :=
      pow_pos hheightPositive degree
    have hdecay := hhalfDecay t
    have hshiftZero : (t - 0) ^ 2 = t ^ 2 :=
      congrArg (fun value : ℝ => value ^ 2) (sub_zero t)
    have hnormalizedDecay :
        Real.exp (-halfRate * t ^ 2) ≤
          bound * height ^ (-(degree : ℤ)) :=
      Eq.subst
        (motive := fun square : ℝ =>
          Real.exp (-halfRate * square) ≤
            bound * height ^ (-(degree : ℤ)))
        hshiftZero
        hdecay
    have hmultiplied :
        height ^ degree * Real.exp (-halfRate * t ^ 2) ≤
          height ^ degree *
            (bound * height ^ (-(degree : ℤ))) :=
      mul_le_mul_of_nonneg_left
        hnormalizedDecay
        (le_of_lt hheightPowerPositive)
    have hnegativePower :
        height ^ (-(degree : ℤ)) = (height ^ degree)⁻¹ :=
      Eq.trans
        (zpow_neg height (degree : ℤ))
        (congrArg Inv.inv (zpow_natCast height degree))
    have hcancellation :
        height ^ degree *
            (bound * height ^ (-(degree : ℤ))) =
          bound := by
      have hreassociate :
          height ^ degree *
              (bound * height ^ (-(degree : ℤ))) =
            bound *
              (height ^ degree * height ^ (-(degree : ℤ))) := by
        exact Eq.trans
          (mul_assoc
            (height ^ degree)
            bound
            (height ^ (-(degree : ℤ)))).symm
          (Eq.trans
            (congrArg
              (fun value : ℝ =>
                value * height ^ (-(degree : ℤ)))
              (mul_comm (height ^ degree) bound))
            (mul_assoc
              bound
              (height ^ degree)
              (height ^ (-(degree : ℤ)))))
      have hinverseCancellation :
          height ^ degree * height ^ (-(degree : ℤ)) = 1 :=
        Eq.trans
          (congrArg
            (fun value : ℝ => height ^ degree * value)
            hnegativePower)
          (mul_inv_cancel₀ (ne_of_gt hheightPowerPositive))
      exact Eq.trans hreassociate
        (Eq.trans
          (congrArg (fun value : ℝ => bound * value)
            hinverseCancellation)
          (mul_one bound))
    exact Eq.mp
      (congrArg
        (fun right : ℝ =>
          height ^ degree * Real.exp (-halfRate * t ^ 2) ≤ right)
        hcancellation)
      hmultiplied
  have hrateSplit :
      ∀ t : ℝ,
        Real.exp (-rate * t ^ 2) =
          Real.exp (-halfRate * t ^ 2) *
            Real.exp (-halfRate * t ^ 2) := by
    intro t
    have hhalves : halfRate + halfRate = rate :=
      add_halves rate
    have hargument :
        -rate * t ^ 2 =
          -halfRate * t ^ 2 + -halfRate * t ^ 2 := by
      have hcombine :
          -halfRate * t ^ 2 + -halfRate * t ^ 2 =
            (-(halfRate + halfRate)) * t ^ 2 := by
        exact Eq.trans
          (add_mul (-halfRate) (-halfRate) (t ^ 2)).symm
          (congrArg
            (fun value : ℝ => value * t ^ 2)
            (neg_add halfRate halfRate).symm)
      exact Eq.trans
        (congrArg
          (fun value : ℝ => -value * t ^ 2)
          hhalves.symm)
        hcombine.symm
    exact Eq.trans
      (congrArg Real.exp hargument)
      (Real.exp_add
        (-halfRate * t ^ 2)
        (-halfRate * t ^ 2))
  have htargetMeasurable :
      MeasureTheory.AEStronglyMeasurable
        (fun t : ℝ =>
          (1 + |t|) ^ degree * Real.exp (-rate * t ^ 2)) := by
    have hheight : Continuous (fun t : ℝ => 1 + |t|) :=
      continuous_const.add continuous_abs
    have hheightPower : Continuous (fun t : ℝ => (1 + |t|) ^ degree) :=
      hheight.pow degree
    have hsquare : Continuous (fun t : ℝ => t ^ 2) :=
      continuous_id.pow 2
    have hargument : Continuous (fun t : ℝ => -rate * t ^ 2) :=
      continuous_const.mul hsquare
    exact (hheightPower.mul
      (Real.continuous_exp.comp hargument)).aestronglyMeasurable
  have hmajorantIntegrable :
      MeasureTheory.Integrable
        (fun t : ℝ => bound * Real.exp (-halfRate * t ^ 2)) :=
    (integrable_exp_neg_mul_sq hhalfRatePositive).const_mul bound
  have hpointwise :
      ∀ t : ℝ,
        ‖(1 + |t|) ^ degree * Real.exp (-rate * t ^ 2)‖ ≤
          bound * Real.exp (-halfRate * t ^ 2) := by
    intro t
    have htargetNonnegative :
        0 ≤ (1 + |t|) ^ degree * Real.exp (-rate * t ^ 2) :=
      mul_nonneg
        (pow_nonneg (add_nonneg zero_le_one (abs_nonneg t)) degree)
        (le_of_lt (Real.exp_pos (-rate * t ^ 2)))
    have hfactorNonnegative :
        0 ≤ Real.exp (-halfRate * t ^ 2) :=
      le_of_lt (Real.exp_pos (-halfRate * t ^ 2))
    have hfactorBound :
        ((1 + |t|) ^ degree * Real.exp (-halfRate * t ^ 2)) *
            Real.exp (-halfRate * t ^ 2) ≤
          bound * Real.exp (-halfRate * t ^ 2) :=
      mul_le_mul_of_nonneg_right
        (hweightedHalfBound t)
        hfactorNonnegative
    have htargetFactorization :
        (1 + |t|) ^ degree * Real.exp (-rate * t ^ 2) =
          ((1 + |t|) ^ degree * Real.exp (-halfRate * t ^ 2)) *
            Real.exp (-halfRate * t ^ 2) :=
      Eq.trans
        (congrArg
          (fun value : ℝ => (1 + |t|) ^ degree * value)
          (hrateSplit t))
        (mul_assoc
          ((1 + |t|) ^ degree)
          (Real.exp (-halfRate * t ^ 2))
          (Real.exp (-halfRate * t ^ 2))).symm
    exact Eq.subst
      (motive := fun value : ℝ =>
        ‖value‖ ≤ bound * Real.exp (-halfRate * t ^ 2))
      htargetFactorization.symm
      (Eq.subst
        (motive := fun left : ℝ =>
          left ≤ bound * Real.exp (-halfRate * t ^ 2))
        (Eq.trans
          (Real.norm_eq_abs
            (((1 + |t|) ^ degree *
              Real.exp (-halfRate * t ^ 2)) *
              Real.exp (-halfRate * t ^ 2)))
          (abs_of_nonneg
            (mul_nonneg
              (mul_nonneg
                (pow_nonneg
                  (add_nonneg zero_le_one (abs_nonneg t)) degree)
                hfactorNonnegative)
              hfactorNonnegative))).symm
        hfactorBound)
  exact MeasureTheory.Integrable.mono'
    hmajorantIntegrable
    htargetMeasurable
    (Filter.Eventually.of_forall hpointwise)

/-- Every iterated derivative of the real physical Gaussian has integrable
norm. -/
theorem integrable_norm_iteratedDeriv_realPhysicalGaussian
    (order : ℕ) :
    MeasureTheory.Integrable
      (fun t : ℝ =>
        ‖iteratedDeriv order realPhysicalGaussian t‖) := by
  let hermiteDegree : ℕ := (realHermitePolynomial order).natDegree
  let coefficientBound : ℝ :=
    realPolynomialCoefficientNormSum (realHermitePolynomial order)
  let scaleHeightBound : ℝ :=
    (1 + |Real.sqrt 2|) ^ hermiteDegree
  let derivativeBound : ℝ :=
    |(Real.sqrt 2) ^ order| * coefficientBound * scaleHeightBound
  have hcoefficientBoundNonnegative : 0 ≤ coefficientBound :=
    realPolynomialCoefficientNormSum_nonnegative
      (realHermitePolynomial order)
  have hscaleHeightBoundNonnegative : 0 ≤ scaleHeightBound :=
    pow_nonneg
      (add_nonneg zero_le_one (abs_nonneg (Real.sqrt 2)))
      hermiteDegree
  have hderivativeBoundNonnegative : 0 ≤ derivativeBound :=
    mul_nonneg
      (mul_nonneg
        (abs_nonneg ((Real.sqrt 2) ^ order))
        hcoefficientBoundNonnegative)
      hscaleHeightBoundNonnegative
  have hbaseIntegrable :
      MeasureTheory.Integrable
        (fun t : ℝ =>
          (1 + |t|) ^ hermiteDegree * Real.exp (-(1 : ℝ) * t ^ 2)) :=
    integrable_centeredHeight_pow_mul_realGaussian
      1 zero_lt_one hermiteDegree
  have hmajorantIntegrable :
      MeasureTheory.Integrable
        (fun t : ℝ =>
          derivativeBound *
            ((1 + |t|) ^ hermiteDegree *
              Real.exp (-(1 : ℝ) * t ^ 2))) :=
    hbaseIntegrable.const_mul derivativeBound
  have htargetMeasurable :
      MeasureTheory.AEStronglyMeasurable
        (fun t : ℝ =>
          ‖iteratedDeriv order realPhysicalGaussian t‖) :=
    ((realPhysicalGaussian_contDiff.continuous_iteratedDeriv order)
      (naturalOrder_le_contDiffInfinity order)).norm.aestronglyMeasurable
  have hpointwise :
      ∀ t : ℝ,
        ‖‖iteratedDeriv order realPhysicalGaussian t‖‖ ≤
          derivativeBound *
            ((1 + |t|) ^ hermiteDegree *
              Real.exp (-(1 : ℝ) * t ^ 2)) := by
    intro t
    have hhermite :=
      abs_aeval_hermite_le_coefficientNormSum_mul_height
        order
        (Real.sqrt 2 * t)
    have hscaledHeight :=
      one_add_abs_mul_pow_le_height_product_pow
        (Real.sqrt 2) t hermiteDegree
    have hheightProductNonnegative :
        0 ≤ coefficientBound * scaleHeightBound :=
      mul_nonneg hcoefficientBoundNonnegative hscaleHeightBoundNonnegative
    have hhermiteScaled :
        |Polynomial.aeval (Real.sqrt 2 * t)
            (Polynomial.hermite order)| ≤
          (coefficientBound * scaleHeightBound) *
            (1 + |t|) ^ hermiteDegree := by
      have hscaledByCoefficient :
          coefficientBound *
              (1 + |Real.sqrt 2 * t|) ^ hermiteDegree ≤
            coefficientBound *
              (scaleHeightBound *
                (1 + |t|) ^ hermiteDegree) :=
        mul_le_mul_of_nonneg_left
          hscaledHeight
          hcoefficientBoundNonnegative
      have hreassociate :
          coefficientBound *
              (scaleHeightBound *
                (1 + |t|) ^ hermiteDegree) =
            (coefficientBound * scaleHeightBound) *
              (1 + |t|) ^ hermiteDegree :=
        (mul_assoc
          coefficientBound
          scaleHeightBound
          ((1 + |t|) ^ hermiteDegree)).symm
      exact le_trans hhermite
        (Eq.mp
          (congrArg
            (fun right : ℝ =>
              coefficientBound *
                  (1 + |Real.sqrt 2 * t|) ^ hermiteDegree ≤ right)
            hreassociate)
          hscaledByCoefficient)
    have hgaussianPositive :
        0 < Real.exp (-(1 : ℝ) * t ^ 2) :=
      Real.exp_pos (-(1 : ℝ) * t ^ 2)
    have hgaussianNonnegative :
        0 ≤ Real.exp (-(1 : ℝ) * t ^ 2) :=
      le_of_lt hgaussianPositive
    have hhermiteWithGaussian :
        |Polynomial.aeval (Real.sqrt 2 * t)
            (Polynomial.hermite order)| *
            Real.exp (-(1 : ℝ) * t ^ 2) ≤
          ((coefficientBound * scaleHeightBound) *
              (1 + |t|) ^ hermiteDegree) *
            Real.exp (-(1 : ℝ) * t ^ 2) :=
      mul_le_mul_of_nonneg_right hhermiteScaled hgaussianNonnegative
    have hsqrtPowerNonnegative :
        0 ≤ |(Real.sqrt 2) ^ order| :=
      abs_nonneg ((Real.sqrt 2) ^ order)
    have hfullBound :
        |(Real.sqrt 2) ^ order| *
            (|Polynomial.aeval (Real.sqrt 2 * t)
                (Polynomial.hermite order)| *
              Real.exp (-(1 : ℝ) * t ^ 2)) ≤
          |(Real.sqrt 2) ^ order| *
            (((coefficientBound * scaleHeightBound) *
                (1 + |t|) ^ hermiteDegree) *
              Real.exp (-(1 : ℝ) * t ^ 2)) :=
      mul_le_mul_of_nonneg_left
        hhermiteWithGaussian
        hsqrtPowerNonnegative
    have hderivativeIdentity :=
      iteratedDeriv_realPhysicalGaussian_eq_hermite order t
    have hnegativePowerAbsolute : |(-1 : ℝ) ^ order| = 1 :=
      Eq.trans
        (abs_pow (-1 : ℝ) order)
        (Eq.trans
          (congrArg
            (fun value : ℝ => value ^ order)
            (Eq.trans (abs_neg (1 : ℝ)) (abs_of_nonneg zero_le_one)))
          (one_pow order))
    have hgaussianNormalization :
        Real.exp (-((Real.sqrt 2 * t) ^ 2 / 2)) =
          Real.exp (-(1 : ℝ) * t ^ 2) := by
      have hquadratic :=
        realPhysicalGaussian_eq_hermiteGaussian_scaled t
      exact Eq.trans hquadratic.symm
        (congrArg Real.exp
          (Eq.trans
            (congrArg Neg.neg (one_mul (t ^ 2)).symm)
            (neg_mul (1 : ℝ) (t ^ 2)).symm))
    have hnormDerivative :
        ‖iteratedDeriv order realPhysicalGaussian t‖ =
          |(Real.sqrt 2) ^ order| *
            (|Polynomial.aeval (Real.sqrt 2 * t)
                (Polynomial.hermite order)| *
              Real.exp (-(1 : ℝ) * t ^ 2)) := by
      exact Eq.trans
        (congrArg norm hderivativeIdentity)
        (Eq.trans
          (Real.norm_eq_abs
            ((Real.sqrt 2) ^ order *
              (((-1 : ℝ) ^ order *
                  Polynomial.aeval (Real.sqrt 2 * t)
                    (Polynomial.hermite order)) *
                Real.exp (-((Real.sqrt 2 * t) ^ 2 / 2)))))
          (Eq.trans
            (abs_mul
              ((Real.sqrt 2) ^ order)
              (((-1 : ℝ) ^ order *
                  Polynomial.aeval (Real.sqrt 2 * t)
                    (Polynomial.hermite order)) *
                Real.exp (-((Real.sqrt 2 * t) ^ 2 / 2))))
            (congrArg
              (fun value : ℝ => |(Real.sqrt 2) ^ order| * value)
              (Eq.trans
                (abs_mul
                  (((-1 : ℝ) ^ order *
                    Polynomial.aeval (Real.sqrt 2 * t)
                      (Polynomial.hermite order)))
                  (Real.exp (-((Real.sqrt 2 * t) ^ 2 / 2))))
                (Eq.trans
                  (congrArg₂ Mul.mul
                    (Eq.trans
                      (abs_mul
                        ((-1 : ℝ) ^ order)
                        (Polynomial.aeval (Real.sqrt 2 * t)
                          (Polynomial.hermite order)))
                      (Eq.trans
                        (congrArg
                          (fun value : ℝ => value *
                            |Polynomial.aeval (Real.sqrt 2 * t)
                              (Polynomial.hermite order)|)
                          hnegativePowerAbsolute)
                        (one_mul
                          |Polynomial.aeval (Real.sqrt 2 * t)
                            (Polynomial.hermite order)|)))
                    (Eq.trans
                      (abs_of_pos
                        (Real.exp_pos (-((Real.sqrt 2 * t) ^ 2 / 2))))
                      hgaussianNormalization))
                  (Eq.refl _))))))
    have hmajorantReassociate :
        |(Real.sqrt 2) ^ order| *
            (((coefficientBound * scaleHeightBound) *
                (1 + |t|) ^ hermiteDegree) *
              Real.exp (-(1 : ℝ) * t ^ 2)) =
          derivativeBound *
            ((1 + |t|) ^ hermiteDegree *
              Real.exp (-(1 : ℝ) * t ^ 2)) := by
      have hcoefficientIdentity :
          |(Real.sqrt 2) ^ order| *
              (coefficientBound * scaleHeightBound) =
            derivativeBound := by
        change
          |(Real.sqrt 2) ^ order| *
              (coefficientBound * scaleHeightBound) =
            (|(Real.sqrt 2) ^ order| * coefficientBound) * scaleHeightBound
        exact
          (mul_assoc
            |(Real.sqrt 2) ^ order|
            coefficientBound
            scaleHeightBound).symm
      exact Eq.trans
        (congrArg
          (fun value : ℝ => |(Real.sqrt 2) ^ order| * value)
          (mul_assoc
            (coefficientBound * scaleHeightBound)
            ((1 + |t|) ^ hermiteDegree)
            (Real.exp (-(1 : ℝ) * t ^ 2))))
        (Eq.trans
          (mul_assoc
            |(Real.sqrt 2) ^ order|
            (coefficientBound * scaleHeightBound)
            ((1 + |t|) ^ hermiteDegree *
              Real.exp (-(1 : ℝ) * t ^ 2))).symm
          (congrArg
            (fun value : ℝ => value *
              ((1 + |t|) ^ hermiteDegree *
                Real.exp (-(1 : ℝ) * t ^ 2)))
            hcoefficientIdentity))
    have hnormNorm :
        ‖‖iteratedDeriv order realPhysicalGaussian t‖‖ =
          ‖iteratedDeriv order realPhysicalGaussian t‖ :=
      Real.norm_of_nonneg
        (norm_nonneg (iteratedDeriv order realPhysicalGaussian t))
    exact Eq.subst
      (motive := fun left : ℝ =>
        left ≤
          derivativeBound *
            ((1 + |t|) ^ hermiteDegree *
              Real.exp (-(1 : ℝ) * t ^ 2)))
      hnormNorm.symm
      (Eq.subst
        (motive := fun left : ℝ =>
          left ≤
            derivativeBound *
              ((1 + |t|) ^ hermiteDegree *
                Real.exp (-(1 : ℝ) * t ^ 2)))
        hnormDerivative.symm
        (Eq.mp
          (congrArg
            (fun right : ℝ =>
              |(Real.sqrt 2) ^ order| *
                  (|Polynomial.aeval (Real.sqrt 2 * t)
                      (Polynomial.hermite order)| *
                    Real.exp (-(1 : ℝ) * t ^ 2)) ≤ right)
            hmajorantReassociate)
          hfullBound))
  exact MeasureTheory.Integrable.mono'
    hmajorantIntegrable
    htargetMeasurable
    (Filter.Eventually.of_forall hpointwise)

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
