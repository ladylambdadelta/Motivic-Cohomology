import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.KernelDensity.AtomicDistributionAffineFrequencyWeight

/-!
# Uniform Paley-Wiener decay for Gaussian cutoffs

This file owns the pure real-variable estimate behind compact Gaussian
completion.  The cutoff radius varies, while the horizontal strip, ordinate
scaling, and ordinate translation remain fixed.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

/-- The zero-th iterated oscillatory integral is the vertical-line kernel
integral. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_zero_eq_verticalLineKernelIntegral
    (f : ZetaAdmissibleFunction)
    (x frequency : ℝ) :
    zetaPaleyWienerIteratedDerivativeOscillatoryIntegral
        f 0 x frequency =
      ∫ t : ℝ,
        zetaPaleyWienerVerticalLineKernel f x frequency t := by
  have hkernel :
      (fun t : ℝ =>
        zetaPaleyWienerIteratedDerivativeOscillatoryKernel
          f 0 x frequency t) =
      (fun t : ℝ =>
        zetaPaleyWienerVerticalLineKernel f x frequency t) := by
    funext t
    exact congrArg
      (fun value : ℂ =>
        value * zetaPaleyWienerVerticalOscillation frequency t)
      (zetaPaleyWienerHorizontalTwistIteratedDerivative_zero f x t)
  exact congrArg
    (fun kernel : ℝ → ℂ => ∫ t : ℝ, kernel t)
    hkernel

/-- Vertical-line kernel integrals transport one real coordinate at a time. -/
theorem zetaPaleyWienerVerticalLineKernelIntegral_coordinates
    (f : ZetaAdmissibleFunction)
    (sourceReal sourceImaginary targetReal targetImaginary : ℝ)
    (hreal : sourceReal = targetReal)
    (himaginary : sourceImaginary = targetImaginary) :
    (∫ t : ℝ,
      zetaPaleyWienerVerticalLineKernel
        f sourceReal sourceImaginary t) =
      ∫ t : ℝ,
        zetaPaleyWienerVerticalLineKernel
          f targetReal targetImaginary t := by
  have hrealTransport :
      (∫ t : ℝ,
        zetaPaleyWienerVerticalLineKernel
          f sourceReal sourceImaginary t) =
        ∫ t : ℝ,
          zetaPaleyWienerVerticalLineKernel
            f targetReal sourceImaginary t :=
    congrArg
      (fun realCoordinate : ℝ =>
        ∫ t : ℝ,
          zetaPaleyWienerVerticalLineKernel
            f realCoordinate sourceImaginary t)
      hreal
  have himaginaryTransport :
      (∫ t : ℝ,
        zetaPaleyWienerVerticalLineKernel
          f targetReal sourceImaginary t) =
        ∫ t : ℝ,
          zetaPaleyWienerVerticalLineKernel
            f targetReal targetImaginary t :=
    congrArg
      (fun imaginaryCoordinate : ℝ =>
        ∫ t : ℝ,
          zetaPaleyWienerVerticalLineKernel
            f targetReal imaginaryCoordinate t)
      himaginary
  exact Eq.trans hrealTransport himaginaryTransport

/-- Spectral evaluation on an explicit vertical line is the zero-th iterated
oscillatory integral. -/
theorem zetaSpectralEval_verticalLine_eq_iteratedOscillatoryIntegral_zero
    (f : ZetaAdmissibleFunction)
    (x frequency : ℝ) :
    zetaSpectralEval f
        ((x : ℂ) + (frequency : ℂ) * Complex.I) =
      zetaPaleyWienerIteratedDerivativeOscillatoryIntegral
        f 0 x frequency := by
  let z : ℂ := (x : ℂ) + (frequency : ℂ) * Complex.I
  have hzReal : z.re = x :=
    paley_ofReal_add_mul_I_re x frequency
  have hzImaginary : z.im = frequency :=
    paley_ofReal_add_mul_I_im x frequency
  have hspectral :
      zetaSpectralEval f z =
        Boundary.zetaLaplaceTransform f.toZetaTestFunction' z :=
    zetaSpectralEval_eq_laplace f z
  have hlaplace :
      Boundary.zetaLaplaceTransform f.toZetaTestFunction' z =
        ∫ t : ℝ,
          zetaPaleyWienerVerticalLineKernel f z.re z.im t :=
    zetaLaplaceTransform_eq_verticalLineKernelIntegral f z
  have hcoordinates :
      (∫ t : ℝ,
        zetaPaleyWienerVerticalLineKernel f z.re z.im t) =
      ∫ t : ℝ,
        zetaPaleyWienerVerticalLineKernel f x frequency t := by
    exact zetaPaleyWienerVerticalLineKernelIntegral_coordinates
      f z.re z.im x frequency hzReal hzImaginary
  have hspectralToKernel :
      zetaSpectralEval f z =
        ∫ t : ℝ,
          zetaPaleyWienerVerticalLineKernel f z.re z.im t :=
    Eq.trans hspectral hlaplace
  have hspectralToCoordinates :
      zetaSpectralEval f z =
        ∫ t : ℝ,
          zetaPaleyWienerVerticalLineKernel f x frequency t :=
    Eq.trans hspectralToKernel hcoordinates
  exact Eq.trans hspectralToCoordinates
    (zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_zero_eq_verticalLineKernelIntegral
      f x frequency).symm

/-- A low affine frequency converts the canonical affine-height comparison
into a fixed factor-two height bound. -/
theorem one_add_abs_le_affineFrequencyHeightFactor_mul_two_of_norm_le_one
    (shift scale y : ℝ)
    (hscale : 0 < scale)
    (hfrequency : ‖scale * (y - shift)‖ ≤ 1) :
    1 + |y| ≤ affineFrequencyHeightFactor shift scale * 2 := by
  let frequency : ℝ := scale * (y - shift)
  let factor : ℝ := affineFrequencyHeightFactor shift scale
  have hfrequencyAbsolute : |frequency| ≤ 1 :=
    Eq.subst
      (motive := fun value : ℝ => value ≤ 1)
      (Real.norm_eq_abs frequency)
      hfrequency
  have hfrequencyHeight : 1 + |frequency| ≤ 2 :=
    Eq.subst
      (motive := fun right : ℝ => 1 + |frequency| ≤ right)
      one_add_one_eq_two
      (add_le_add_left hfrequencyAbsolute 1)
  have haffineHeight :
      1 + |y| ≤ factor * (1 + |frequency|) :=
    one_add_abs_le_affineFrequencyHeightFactor_mul
      shift scale y hscale
  have hfactorNonnegative : 0 ≤ factor :=
    le_of_lt (affineFrequencyHeightFactor_pos shift scale hscale)
  exact le_trans haffineHeight
    (mul_le_mul_of_nonneg_left hfrequencyHeight hfactorNonnegative)

/-- Low affine frequencies are controlled by the zero-th derivative `L1`
bound after enlarging the canonical-height constant. -/
theorem admissibleGaussianCutoffNat_uniformPaleyWiener_lowAffineFrequency
    (shift scale : ℝ)
    (hscale : 0 < scale)
    (degree : ℕ) :
    let lowBound : ℝ :=
      admissibleGaussianCutoffHorizontalTwistDerivativeL1Bound 0 scale *
        (affineFrequencyHeightFactor shift scale * 2) ^ degree
    ∀ n : ℕ,
      ∀ x y : ℝ,
        |x| ≤ scale →
          ‖scale * (y - shift)‖ ≤ 1 →
            ‖zetaSpectralEval
                (admissibleGaussianCutoffNat n)
                ((x : ℂ) +
                  ((scale * (y - shift) : ℝ) : ℂ) * Complex.I)‖ ≤
              lowBound * (1 + |y|) ^ (-(degree : ℤ)) := by
  change ∀ n : ℕ,
    ∀ x y : ℝ,
      |x| ≤ scale →
        ‖scale * (y - shift)‖ ≤ 1 →
          ‖zetaSpectralEval
              (admissibleGaussianCutoffNat n)
              ((x : ℂ) +
                ((scale * (y - shift) : ℝ) : ℂ) * Complex.I)‖ ≤
            (admissibleGaussianCutoffHorizontalTwistDerivativeL1Bound 0 scale *
                (affineFrequencyHeightFactor shift scale * 2) ^ degree) *
              (1 + |y|) ^ (-(degree : ℤ))
  intro n x y hx hfrequency
  let lowBound : ℝ :=
    admissibleGaussianCutoffHorizontalTwistDerivativeL1Bound 0 scale *
      (affineFrequencyHeightFactor shift scale * 2) ^ degree
  let frequency : ℝ := scale * (y - shift)
  let factor : ℝ := affineFrequencyHeightFactor shift scale
  let zeroBound : ℝ :=
    admissibleGaussianCutoffHorizontalTwistDerivativeL1Bound 0 scale
  have hspectral :=
    zetaSpectralEval_verticalLine_eq_iteratedOscillatoryIntegral_zero
      (admissibleGaussianCutoffNat n) x frequency
  have hzero :=
    zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_cutoff_uniformBound
      scale hscale 0 n x frequency hx
  have hheightBound :
      1 + |y| ≤ factor * 2 :=
    one_add_abs_le_affineFrequencyHeightFactor_mul_two_of_norm_le_one
      shift scale y hscale hfrequency
  have hfactorPositive : 0 < factor :=
    affineFrequencyHeightFactor_pos shift scale hscale
  have hfactorTwoPositive : 0 < factor * 2 :=
    mul_pos hfactorPositive zero_lt_two
  have habsorption :=
    one_le_factorPow_mul_negativePower_of_height_le
      (1 + |y|)
      (factor * 2)
      degree
      (add_pos_of_pos_of_nonneg zero_lt_one (abs_nonneg y))
      hfactorTwoPositive
      hheightBound
  have hzeroBoundNonnegative : 0 ≤ zeroBound :=
    le_of_lt
      (admissibleGaussianCutoffHorizontalTwistDerivativeL1Bound_pos
        0 scale)
  have hscaledAbsorption :
      zeroBound ≤
        zeroBound *
          ((factor * 2) ^ degree *
            (1 + |y|) ^ (-(degree : ℤ))) :=
    Eq.subst
      (motive := fun left : ℝ =>
        left ≤
          zeroBound *
            ((factor * 2) ^ degree *
              (1 + |y|) ^ (-(degree : ℤ))))
      (mul_one zeroBound)
      (mul_le_mul_of_nonneg_left habsorption hzeroBoundNonnegative)
  have hreassociate :
      zeroBound *
          ((factor * 2) ^ degree *
            (1 + |y|) ^ (-(degree : ℤ))) =
        lowBound * (1 + |y|) ^ (-(degree : ℤ)) :=
    (mul_assoc zeroBound ((factor * 2) ^ degree)
      ((1 + |y|) ^ (-(degree : ℤ)))).symm
  exact Eq.subst
    (motive := fun left : ℂ =>
      ‖left‖ ≤ lowBound * (1 + |y|) ^ (-(degree : ℤ)))
    hspectral.symm
    (le_trans hzero
      (le_trans hscaledAbsorption (le_of_eq hreassociate)))

/-- High affine frequencies inherit uniform oscillatory decay and then
transport it to the original canonical height. -/
theorem admissibleGaussianCutoffNat_uniformPaleyWiener_highAffineFrequency
    (shift scale : ℝ)
    (hscale : 0 < scale)
    (degree : ℕ) :
    ∃ highBound : ℝ,
      0 < highBound ∧
        ∀ n : ℕ,
          ∀ x y : ℝ,
            |x| ≤ scale →
              1 ≤ ‖scale * (y - shift)‖ →
                ‖zetaSpectralEval
                    (admissibleGaussianCutoffNat n)
                    ((x : ℂ) +
                      ((scale * (y - shift) : ℝ) : ℂ) * Complex.I)‖ ≤
                  highBound * (1 + |y|) ^ (-(degree : ℤ)) := by
  match
      admissibleGaussianCutoffNat_iteratedOscillatoryIntegral_uniform_highFrequency_decay
        scale hscale 0 degree with
  | ⟨frequencyBound, hfrequencyBoundPositive, hfrequencyBound⟩ =>
    let factor : ℝ := affineFrequencyHeightFactor shift scale
    let highBound : ℝ := frequencyBound * factor ^ degree
    have hfactorPowerPositive : 0 < factor ^ degree :=
      pow_pos (affineFrequencyHeightFactor_pos shift scale hscale) degree
    have hhighBoundPositive : 0 < highBound :=
      mul_pos hfrequencyBoundPositive hfactorPowerPositive
    have hdecay :
        ∀ n : ℕ,
          ∀ x y : ℝ,
            |x| ≤ scale →
              1 ≤ ‖scale * (y - shift)‖ →
                ‖zetaSpectralEval
                    (admissibleGaussianCutoffNat n)
                    ((x : ℂ) +
                      ((scale * (y - shift) : ℝ) : ℂ) * Complex.I)‖ ≤
                  highBound * (1 + |y|) ^ (-(degree : ℤ)) :=
      fun (n : ℕ) (x y : ℝ) hx hfrequency => by
      let frequency : ℝ := scale * (y - shift)
      have hspectral :=
        zetaSpectralEval_verticalLine_eq_iteratedOscillatoryIntegral_zero
          (admissibleGaussianCutoffNat n) x frequency
      have hoscillatory :=
        hfrequencyBound n x frequency hx hfrequency
      have hweightAbs :=
        affineFrequency_negativePower_le shift scale y hscale degree
      have hweightNorm :
          (1 + ‖frequency‖) ^ (-(degree : ℤ)) =
            (1 + |frequency|) ^ (-(degree : ℤ)) :=
        congrArg
          (fun value : ℝ => (1 + value) ^ (-(degree : ℤ)))
          (Real.norm_eq_abs frequency)
      have hweight :
          (1 + ‖frequency‖) ^ (-(degree : ℤ)) ≤
            factor ^ degree * (1 + |y|) ^ (-(degree : ℤ)) :=
        Eq.subst
          (motive := fun left : ℝ =>
            left ≤ factor ^ degree * (1 + |y|) ^ (-(degree : ℤ)))
          hweightNorm.symm
          hweightAbs
      have hfrequencyBoundNonnegative : 0 ≤ frequencyBound :=
        le_of_lt hfrequencyBoundPositive
      have hscaledWeight :
          frequencyBound * (1 + ‖frequency‖) ^ (-(degree : ℤ)) ≤
            frequencyBound *
              (factor ^ degree * (1 + |y|) ^ (-(degree : ℤ))) :=
        mul_le_mul_of_nonneg_left hweight hfrequencyBoundNonnegative
      have hreassociate :
          frequencyBound *
              (factor ^ degree * (1 + |y|) ^ (-(degree : ℤ))) =
            highBound * (1 + |y|) ^ (-(degree : ℤ)) :=
        (mul_assoc frequencyBound (factor ^ degree)
          ((1 + |y|) ^ (-(degree : ℤ)))).symm
      exact Eq.subst
        (motive := fun left : ℂ =>
          ‖left‖ ≤ highBound * (1 + |y|) ^ (-(degree : ℤ)))
        hspectral.symm
        (le_trans hoscillatory
          (le_trans hscaledWeight (le_of_eq hreassociate)))
    exact Exists.intro highBound (And.intro hhighBoundPositive hdecay)

/-- The maximum of the low- and high-frequency constants controls every
cutoff probe on the fixed horizontal strip. -/
theorem admissibleGaussianCutoffNat_uniformPaleyWiener_of_low_high
    (shift scale : ℝ)
    (hscale : 0 < scale)
    (degree : ℕ)
    (highBound : ℝ)
    (hhighBound :
      ∀ n : ℕ,
        ∀ x y : ℝ,
          |x| ≤ scale →
            1 ≤ ‖scale * (y - shift)‖ →
              ‖zetaSpectralEval
                  (admissibleGaussianCutoffNat n)
                  ((x : ℂ) +
                    ((scale * (y - shift) : ℝ) : ℂ) * Complex.I)‖ ≤
                highBound * (1 + |y|) ^ (-(degree : ℤ))) :
    let lowBound : ℝ :=
      admissibleGaussianCutoffHorizontalTwistDerivativeL1Bound 0 scale *
        (affineFrequencyHeightFactor shift scale * 2) ^ degree
    let bound : ℝ := max lowBound highBound + 1
    ∀ n : ℕ,
      ∀ x y : ℝ,
        |x| ≤ scale →
          ‖zetaSpectralEval
              (admissibleGaussianCutoffNat n)
              ((x : ℂ) +
                ((scale * (y - shift) : ℝ) : ℂ) * Complex.I)‖ ≤
            bound * (1 + |y|) ^ (-(degree : ℤ)) := by
  change ∀ n : ℕ,
    ∀ x y : ℝ,
      |x| ≤ scale →
        ‖zetaSpectralEval
            (admissibleGaussianCutoffNat n)
            ((x : ℂ) +
              ((scale * (y - shift) : ℝ) : ℂ) * Complex.I)‖ ≤
          (max
              (admissibleGaussianCutoffHorizontalTwistDerivativeL1Bound 0 scale *
                (affineFrequencyHeightFactor shift scale * 2) ^ degree)
              highBound + 1) *
            (1 + |y|) ^ (-(degree : ℤ))
  intro n x y hx
  let lowBound : ℝ :=
    admissibleGaussianCutoffHorizontalTwistDerivativeL1Bound 0 scale *
      (affineFrequencyHeightFactor shift scale * 2) ^ degree
  let bound : ℝ := max lowBound highBound + 1
  let frequency : ℝ := scale * (y - shift)
  have hweightNonnegative :
      0 ≤ (1 + |y|) ^ (-(degree : ℤ)) :=
    zpow_nonneg
      (add_nonneg zero_le_one (abs_nonneg y))
      (-(degree : ℤ))
  exact Or.elim (Classical.em (‖frequency‖ ≤ 1))
    (fun hlow =>
      have hraw :=
        admissibleGaussianCutoffNat_uniformPaleyWiener_lowAffineFrequency
          shift scale hscale degree n x y hx hlow
      have hconstant : lowBound ≤ bound :=
        le_trans
          (le_max_left lowBound highBound)
          (le_add_of_nonneg_right zero_le_one)
      have hscaledConstant :
          lowBound * (1 + |y|) ^ (-(degree : ℤ)) ≤
            bound * (1 + |y|) ^ (-(degree : ℤ)) :=
        mul_le_mul_of_nonneg_right hconstant hweightNonnegative
      le_trans hraw hscaledConstant)
    (fun hnotLow =>
      have hhigh : 1 ≤ ‖frequency‖ :=
        le_of_lt (lt_of_not_ge hnotLow)
      have hraw := hhighBound n x y hx hhigh
      have hconstant : highBound ≤ bound :=
        le_trans
          (le_max_right lowBound highBound)
          (le_add_of_nonneg_right zero_le_one)
      have hscaledConstant :
          highBound * (1 + |y|) ^ (-(degree : ℤ)) ≤
            bound * (1 + |y|) ^ (-(degree : ℤ)) :=
        mul_le_mul_of_nonneg_right hconstant hweightNonnegative
      le_trans hraw hscaledConstant)

/-- Natural Gaussian cutoffs have arbitrary vertical decay uniformly in the
cutoff radius on a fixed horizontal strip, after a fixed positive ordinate
scaling and translation. -/
theorem admissibleGaussianCutoffNat_uniformPaleyWiener_shiftedScale
    (shift scale : ℝ)
    (hscale : 0 < scale)
    (degree : ℕ) :
    ∃ bound : ℝ,
      0 < bound ∧
        ∀ n : ℕ,
          ∀ x y : ℝ,
            |x| ≤ scale →
              ‖zetaSpectralEval
                  (admissibleGaussianCutoffNat n)
                  ((x : ℂ) +
                    ((scale * (y - shift) : ℝ) : ℂ) * Complex.I)‖ ≤
                bound * (1 + |y|) ^ (-(degree : ℤ)) := by
  obtain ⟨highBound, hhighBoundPositive, hhighBound⟩ :=
    admissibleGaussianCutoffNat_uniformPaleyWiener_highAffineFrequency
      shift scale hscale degree
  let lowBound : ℝ :=
    admissibleGaussianCutoffHorizontalTwistDerivativeL1Bound 0 scale *
      (affineFrequencyHeightFactor shift scale * 2) ^ degree
  have hlowBoundPositive : 0 < lowBound :=
    mul_pos
      (admissibleGaussianCutoffHorizontalTwistDerivativeL1Bound_pos
        0 scale)
      (pow_pos
        (mul_pos
          (affineFrequencyHeightFactor_pos shift scale hscale)
          zero_lt_two)
        degree)
  let bound : ℝ := max lowBound highBound + 1
  have hmaxNonnegative : 0 ≤ max lowBound highBound :=
    le_trans
      (le_of_lt hlowBoundPositive)
      (le_max_left lowBound highBound)
  have hboundPositive : 0 < bound :=
    add_pos_of_nonneg_of_pos hmaxNonnegative zero_lt_one
  have huniform :=
    admissibleGaussianCutoffNat_uniformPaleyWiener_of_low_high
      shift scale hscale degree highBound hhighBound
  exact Exists.intro bound (And.intro hboundPositive huniform)

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
