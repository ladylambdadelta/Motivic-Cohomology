import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.LogDerivativeFixedVertical
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.L2_AbelPlanaDecomposition

/-!
# Gamma logarithmic derivative from the finite Abel-Plana formula
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

/-- The endpoint-restored finite-height contour calculation supplies the exact
finite Abel-Plana formula throughout the open right half-plane. -/
theorem Complex.binetAbelPlanaFiniteFormula_openRightHalfPlane :
    ∀ z : ℂ,
      0 < z.re →
        ∀ N : ℕ,
          Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
            Complex.binetAbelPlanaFiniteMainTerm N z +
              Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                Complex.binetAbelPlanaFiniteContourRemainder N z := by
  exact
    Complex.binetSecondFormula_finiteAbelPlana_logGammaFiniteApproximation_eq_main_boundary_contourRemainder_owner

/-- A global finite Abel-Plana formula restricts to every neighborhood in the
open right half-plane. -/
theorem Complex.binetAbelPlanaFiniteFormula_eventually_rightHalfPlane
    (finiteFormula :
      ∀ z : ℂ,
        0 < z.re →
          ∀ N : ℕ,
            Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
              Complex.binetAbelPlanaFiniteMainTerm N z +
                Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                  Complex.binetAbelPlanaFiniteContourRemainder N z)
    {w : ℂ}
    (realPartPositive : 0 < w.re) :
    ∀ᶠ z : ℂ in 𝓝 w,
      ∀ N : ℕ,
        Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
          Complex.binetAbelPlanaFiniteMainTerm N z +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
              Complex.binetAbelPlanaFiniteContourRemainder N z := by
  have eventuallyPositive : ∀ᶠ z : ℂ in 𝓝 w, 0 < z.re :=
    Complex.continuous_re.continuousAt.eventually
      (IsOpen.mem_nhds isOpen_Ioi realPartPositive)
  exact eventuallyPositive.mono
    (fun z positive => finiteFormula z positive)

/-- The Gamma logarithmic derivative on a positive fixed-real-part line follows
from the finite Abel-Plana formula, without a global principal-log condition on
the range of Gamma. -/
theorem Complex.Gamma_logDerivative_fixedRealPartLine_eq_binet_of_finiteFormula
    (finiteFormula :
      ∀ z : ℂ,
        0 < z.re →
          ∀ N : ℕ,
            Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
              Complex.binetAbelPlanaFiniteMainTerm N z +
                Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                  Complex.binetAbelPlanaFiniteContourRemainder N z)
    {sigma : ℝ}
    (sigmaPositive : 0 < sigma)
    (t : ℝ) :
    deriv Complex.Gamma (sigma + t * Complex.I) /
        Complex.Gamma (sigma + t * Complex.I) =
      (Complex.log (sigma + t * Complex.I) -
          (1 / (2 * (sigma + t * Complex.I)))) +
        2 * ∫ u : ℝ in Set.Ioi (0 : ℝ),
          (-(u : ℂ) /
              ((sigma + t * Complex.I) ^ 2 + (u : ℂ) ^ 2)) /
            (Complex.exp (((2 : ℝ) * Real.pi * u : ℝ) : ℂ) - 1) := by
  let w : ℂ := sigma + t * Complex.I
  have realPart : w.re = sigma := by
    exact Complex.fixedRealPartLine_re sigma t
  have realPartPositive : 0 < w.re :=
    Eq.subst
      (motive := fun value : ℝ => 0 < value)
      realPart.symm
      sigmaPositive
  have pointFormula :
      ∀ N : ℕ,
        Complex.binetAbelPlanaLogGammaFiniteApproximation N w =
          Complex.binetAbelPlanaFiniteMainTerm N w +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N w +
              Complex.binetAbelPlanaFiniteContourRemainder N w :=
    finiteFormula w realPartPositive
  have neighborhoodFormula :
      ∀ᶠ z : ℂ in 𝓝 w,
        ∀ N : ℕ,
          Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
            Complex.binetAbelPlanaFiniteMainTerm N z +
              Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                Complex.binetAbelPlanaFiniteContourRemainder N z :=
    Complex.binetAbelPlanaFiniteFormula_eventually_rightHalfPlane
      finiteFormula realPartPositive
  exact
    Complex.Gamma_logDerivative_eq_binet_explicit_derivative_add_integral
      realPartPositive pointFormula neighborhoodFormula

/-- Named main-plus-remainder form of the fixed-line logarithmic derivative
under the finite Abel-Plana formula. -/
theorem Complex.Gamma_logDerivative_fixedRealPartLine_eq_main_add_remainder_of_finiteFormula
    (finiteFormula :
      ∀ z : ℂ,
        0 < z.re →
          ∀ N : ℕ,
            Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
              Complex.binetAbelPlanaFiniteMainTerm N z +
                Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                  Complex.binetAbelPlanaFiniteContourRemainder N z)
    {sigma : ℝ}
    (sigmaPositive : 0 < sigma)
    (t : ℝ) :
    deriv Complex.Gamma (sigma + t * Complex.I) /
        Complex.Gamma (sigma + t * Complex.I) =
      Complex.GammaLogDerivativeFixedVerticalMain sigma t +
        Complex.GammaLogDerivativeFixedVerticalRemainder sigma t := by
  exact
    Complex.Gamma_logDerivative_fixedRealPartLine_eq_binet_of_finiteFormula
      finiteFormula sigmaPositive t

/-- Unconditional fixed-line Binet logarithmic-derivative identity from the
endpoint-restored finite Abel-Plana owner. -/
theorem Complex.Gamma_logDerivative_fixedRealPartLine_eq_binet_direct
    {sigma : ℝ}
    (sigmaPositive : 0 < sigma)
    (t : ℝ) :
    deriv Complex.Gamma (sigma + t * Complex.I) /
        Complex.Gamma (sigma + t * Complex.I) =
      (Complex.log (sigma + t * Complex.I) -
          (1 / (2 * (sigma + t * Complex.I)))) +
        2 * ∫ u : ℝ in Set.Ioi (0 : ℝ),
          (-(u : ℂ) /
              ((sigma + t * Complex.I) ^ 2 + (u : ℂ) ^ 2)) /
            (Complex.exp (((2 : ℝ) * Real.pi * u : ℝ) : ℂ) - 1) := by
  exact
    Complex.Gamma_logDerivative_fixedRealPartLine_eq_binet_of_finiteFormula
      Complex.binetAbelPlanaFiniteFormula_openRightHalfPlane sigmaPositive t

/-- Unconditional named main-plus-remainder decomposition of the fixed-line
Gamma logarithmic derivative. -/
theorem Complex.Gamma_logDerivative_fixedRealPartLine_eq_main_add_remainder_direct
    {sigma : ℝ}
    (sigmaPositive : 0 < sigma)
    (t : ℝ) :
    deriv Complex.Gamma (sigma + t * Complex.I) /
        Complex.Gamma (sigma + t * Complex.I) =
      Complex.GammaLogDerivativeFixedVerticalMain sigma t +
        Complex.GammaLogDerivativeFixedVerticalRemainder sigma t := by
  exact
    Complex.Gamma_logDerivative_fixedRealPartLine_eq_main_add_remainder_of_finiteFormula
      Complex.binetAbelPlanaFiniteFormula_openRightHalfPlane sigmaPositive t

/-- Unconditional finite-shift decomposition obtained by iterating the Gamma
recurrence from the direct positive-line finite-formula identity. -/
theorem Complex.Gamma_logDerivative_fixedRealPartLine_eq_shiftNat_main_add_remainder_direct
    {sigma : ℝ}
    (N : ℕ)
    (shiftedRealPartPositive : 0 < sigma + (N : ℝ))
    (avoidsPoles :
      ∀ t : ℝ, ∀ n : ℕ,
        (sigma + t * Complex.I : ℂ) ≠ -n)
    (t : ℝ) :
    deriv Complex.Gamma (sigma + t * Complex.I) /
        Complex.Gamma (sigma + t * Complex.I) =
      Complex.GammaLogDerivativeFixedVerticalShiftNatMain sigma N t +
        Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder sigma N t := by
  exact
    _root_.Boundary.LFunctions.Complex.Gamma_logDerivative_fixedRealPartLine_eq_shiftNat_main_add_remainder_of_base
      (fun realPartPositive height =>
        Complex.Gamma_logDerivative_fixedRealPartLine_eq_main_add_remainder_direct
          realPartPositive height)
      N shiftedRealPartPositive avoidsPoles t

/-- Direct positive-line linear bound obtained from finite Abel--Plana. -/
theorem Complex.Gamma_logDerivative_fixedRealPartLine_linear_bound_direct
    {sigma : ℝ}
    (sigmaPositive : 0 < sigma) :
    ∀ t : ℝ,
      ‖deriv Complex.Gamma (sigma + t * Complex.I) /
          Complex.Gamma (sigma + t * Complex.I)‖ ≤
        Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant sigma *
          (1 + ‖t‖) := by
  exact
    _root_.Boundary.LFunctions.Complex.Gamma_logDerivative_fixedRealPartLine_linear_bound_of_decomposition
      sigmaPositive
      (fun t : ℝ =>
        Complex.Gamma_logDerivative_fixedRealPartLine_eq_main_add_remainder_direct
          sigmaPositive t)

/-- Direct shifted-line linear bound obtained from finite Abel--Plana and the
Gamma recurrence. -/
theorem Complex.Gamma_logDerivative_fixedRealPartLine_linear_bound_of_shift_nat_direct
    {sigma : ℝ}
    (N : ℕ)
    (shiftedRealPartPositive : 0 < sigma + (N : ℝ))
    (avoidsPoles :
      ∀ t : ℝ, ∀ n : ℕ,
        (sigma + t * Complex.I : ℂ) ≠ -n) :
    ∀ t : ℝ,
      ‖deriv Complex.Gamma (sigma + t * Complex.I) /
          Complex.Gamma (sigma + t * Complex.I)‖ ≤
        Complex.GammaLogDerivativeFixedVerticalShiftConstant sigma N *
          (1 + ‖t‖) := by
  induction N generalizing sigma with
  | zero =>
      intro t
      have hzero : sigma + ((0 : ℕ) : ℝ) = sigma :=
        (congrArg (fun x : ℝ => sigma + x) Nat.cast_zero).trans
          (add_zero sigma)
      have sigmaPositive : 0 < sigma :=
        Eq.subst
          (motive := fun x : ℝ => 0 < x)
          hzero
          shiftedRealPartPositive
      exact
        Complex.Gamma_logDerivative_fixedRealPartLine_linear_bound_direct
          sigmaPositive t
  | succ N inductionHypothesis =>
      intro t
      have hrewrite :
          sigma + ((N + 1 : ℕ) : ℝ) = (sigma + 1) + (N : ℝ) :=
        Complex.real_add_one_add_nat_eq_add_succ sigma N
      have tailPositive : 0 < (sigma + 1) + (N : ℝ) :=
        Eq.subst
          (motive := fun x : ℝ => 0 < x)
          hrewrite
          shiftedRealPartPositive
      have tailAvoidsPoles :
          ∀ height : ℝ, ∀ n : ℕ,
            ((sigma + 1 : ℝ) + height * Complex.I : ℂ) ≠ -n :=
        Complex.fixedRealPartLine_shift_one_ne_Gamma_zero_locus avoidsPoles
      have tailBound :
          ∀ height : ℝ,
            ‖deriv Complex.Gamma
                ((sigma + 1 : ℝ) + height * Complex.I) /
                Complex.Gamma ((sigma + 1 : ℝ) + height * Complex.I)‖ ≤
              Complex.GammaLogDerivativeFixedVerticalShiftConstant
                  (sigma + 1) N *
                (1 + ‖height‖) :=
        inductionHypothesis tailPositive tailAvoidsPoles
      have sigmaNonzero : sigma ≠ 0 :=
        Complex.fixedRealPartLine_realPart_ne_zero_of_ne_Gamma_zero_locus
          avoidsPoles
      exact
        Complex.Gamma_logDerivative_fixedRealPartLine_linear_bound_of_shift_one_bound
          sigmaNonzero avoidsPoles tailBound t

end

end LFunctions
end Boundary
