import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.ZetaTransformCalculusBase.Owner
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Integral.SetIntegral

/-!
# Fixed-line Cauchy projection for logarithmic Laplace transforms

This file owns the Fourier-Cauchy multiplier theorem used by the one-pole
vertical channel.  The parent transform-calculus owner supplies only the
zeta-specific naming wrapper.
-/

namespace Boundary

open scoped Filter FourierTransform
open Filter Real Complex Set MeasureTheory

noncomputable section

section FixedLineCauchyProjection

/-- The right one-pole Cauchy/Laplace projection value attached to a compactly
supported logarithmic test function. -/
noncomputable def zetaLaplaceTransform_rightOnePoleCauchyProjectionValue
    (φ : LFunctions.ZetaTestFunction) (_c : ℝ) : ℂ :=
  ∫ x in Set.Iic (0 : ℝ),
    (-2 * (Real.pi : ℂ)) *
      φ x *
        Complex.exp ((1 / 2 : ℂ) * (x : ℂ))

/-- The time-side kernel whose Fourier transform is the fixed right vertical
Laplace slice after the `s = 1` Cauchy multiplier is separated. -/
noncomputable def zetaLaplaceTransform_rightOnePoleProjectionKernel
    (φ : LFunctions.ZetaTestFunction) : ℝ → ℂ :=
  fun x : ℝ =>
    φ x *
      Complex.exp ((1 / 2 : ℂ) * (x : ℂ))

/-- Fixed-line Fourier-Cauchy projection theorem for compactly supported
logarithmic test functions.

This is the transform-calculus owner theorem: the symmetric truncations of the
right half-plane Cauchy multiplier on the fixed line converge to the one-sided
time projection with inverse-quadratic tail. -/
theorem zetaLaplaceTransform_fixedLine_rightOnePoleCauchyProjection_eventual_inverseQuadratic_to_value
    (φ : LFunctions.ZetaTestFunction) (c : ℝ) (hc : 1 < c)
    (height : ℝ → ℝ) (hcofinal : Tendsto height atTop atTop) :
    ∃ MR : ℝ,
      0 < MR ∧
        ∀ᶠ u in atTop,
          ‖(∫ t in Set.Icc (-(height u)) (height u),
              (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                zetaLaplaceTransform φ
                  (((c : ℂ) + t * Complex.I) - 1 / 2)) -
            zetaLaplaceTransform_rightOnePoleCauchyProjectionValue φ c‖
            ≤ MR * (1 + ‖height u‖) ^ (-(2 : ℤ)) := by
  sorry

end FixedLineCauchyProjection

end
end Boundary
