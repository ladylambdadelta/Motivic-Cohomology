import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaFiniteEndpoint
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaFiniteMajorants
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaFiniteUpperTail
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaFiniteLowerTail

/-!
# Finite Abel-Plana contour assembly owners

This file assembles lower-tail and upper-tail estimates into finite contour-remainder convergence.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology
open MeasureTheory

/-- Exact finite Abel-Plana summation formula for the logarithmic summand. -/
theorem Complex.binetAbelPlana_logGammaFiniteApproximation_eq_finiteMain_add_boundary_add_contourRemainder_owner
    {w : ℂ}
    (hfinite :
      ∀ N : ℕ,
        Complex.binetAbelPlanaLogGammaFiniteApproximation N w =
          Complex.binetAbelPlanaFiniteMainTerm N w +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N w +
              Complex.binetAbelPlanaFiniteContourRemainder N w) :
    ∀ N : ℕ,
      Complex.binetAbelPlanaLogGammaFiniteApproximation N w =
        Complex.binetAbelPlanaFiniteMainTerm N w +
          Complex.binetAbelPlanaFiniteBoundaryCorrection N w +
            Complex.binetAbelPlanaFiniteContourRemainder N w := by
  exact hfinite

/-- Exact finite Abel-Plana residual identity for the logarithmic summand.

This is the finite contour theorem: after separating the finite main term and
the lower Abel-Plana boundary correction, the remaining error is exactly the
total contour remainder: lower truncation tail plus upper vertical residual. -/
theorem Complex.binetAbelPlanaFiniteRemainderError_eq_contourRemainder_owner
    {w : ℂ}
    (hfinite :
      ∀ N : ℕ,
        Complex.binetAbelPlanaLogGammaFiniteApproximation N w =
          Complex.binetAbelPlanaFiniteMainTerm N w +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N w +
              Complex.binetAbelPlanaFiniteContourRemainder N w) :
    ∀ N : ℕ,
      Complex.binetAbelPlanaFiniteRemainderError N w =
        Complex.binetAbelPlanaFiniteContourRemainder N w := by
  exact fun N => by
    have hfinite :
        Complex.binetAbelPlanaLogGammaFiniteApproximation N w =
          Complex.binetAbelPlanaFiniteMainTerm N w +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N w +
              Complex.binetAbelPlanaFiniteContourRemainder N w :=
      Complex.binetAbelPlana_logGammaFiniteApproximation_eq_finiteMain_add_boundary_add_contourRemainder_owner
        hfinite N
    have herror_unfold :
        Complex.binetAbelPlanaFiniteRemainderError N w =
          Complex.binetAbelPlanaLogGammaFiniteApproximation N w -
            (Complex.binetAbelPlanaFiniteMainTerm N w +
              Complex.binetAbelPlanaFiniteBoundaryCorrection N w) := rfl
    calc
      Complex.binetAbelPlanaFiniteRemainderError N w =
          Complex.binetAbelPlanaLogGammaFiniteApproximation N w -
            (Complex.binetAbelPlanaFiniteMainTerm N w +
              Complex.binetAbelPlanaFiniteBoundaryCorrection N w) :=
            herror_unfold
      _ =
          (Complex.binetAbelPlanaFiniteMainTerm N w +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N w +
              Complex.binetAbelPlanaFiniteContourRemainder N w) -
            (Complex.binetAbelPlanaFiniteMainTerm N w +
              Complex.binetAbelPlanaFiniteBoundaryCorrection N w) := by
            exact congrArg
              (fun z : ℂ =>
                z - (Complex.binetAbelPlanaFiniteMainTerm N w +
                  Complex.binetAbelPlanaFiniteBoundaryCorrection N w))
              hfinite
      _ = Complex.binetAbelPlanaFiniteContourRemainder N w := by
            exact Complex.add_add_sub_add_eq_right
              (Complex.binetAbelPlanaFiniteMainTerm N w)
              (Complex.binetAbelPlanaFiniteBoundaryCorrection N w)
              (Complex.binetAbelPlanaFiniteContourRemainder N w)

/-- Owner estimate for the honest total finite Abel-Plana contour remainder.

The total remainder is the sum of the lower truncation tail and the upper
endpoint residual.  This theorem is the analytic tail estimate replacing the
old false upper-only remainder bridge. -/
theorem Complex.exists_norm_binetAbelPlanaFiniteContourRemainder_le_kernelTail_add_upperMajorant_owner
    {w : ℂ}
    (hw : 0 < w.re) :
      ∃ C : ℝ,
        0 ≤ C ∧
          ∀ᶠ N : ℕ in Filter.atTop,
            ‖Complex.binetAbelPlanaFiniteContourRemainder N w‖ ≤
              (C * ∫ t : ℝ in Set.Ioi (N : ℝ),
                  Complex.binetAbelPlanaVerticalKernelMajorant t) +
                Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N := by
  exact
    match
      Complex.exists_norm_binetAbelPlanaFiniteLowerContourTail_le_kernelTail_owner
        hw with
    | ⟨C, hC_nonneg, hlower⟩ =>
      Exists.intro C
        (And.intro hC_nonneg
          (by
            have hupper :
                ∀ᶠ N : ℕ in Filter.atTop,
                  ‖Complex.binetAbelPlanaFiniteUpperContourResidual N w‖ ≤
                    Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N :=
              Complex.norm_binetAbelPlanaFiniteUpperContourResidual_le_majorant_owner hw
            exact
              (hlower.and hupper).mono
                (fun N hN_pair =>
                  by
                    have hN_lower :
                        ‖Complex.binetAbelPlanaFiniteLowerContourTail N w‖ ≤
                          C * ∫ t : ℝ in Set.Ioi (N : ℝ),
                            Complex.binetAbelPlanaVerticalKernelMajorant t :=
                      hN_pair.1
                    have hN_upper :
                        ‖Complex.binetAbelPlanaFiniteUpperContourResidual N w‖ ≤
                          Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N :=
                      hN_pair.2
                    calc
                        ‖Complex.binetAbelPlanaFiniteContourRemainder N w‖
                            =
                            ‖Complex.binetAbelPlanaFiniteLowerContourTail N w +
                              Complex.binetAbelPlanaFiniteUpperContourResidual N w‖ := by
                          exact congrArg norm
                            (Complex.binetAbelPlanaFiniteContourRemainder_core_unfold N w)
                      _ ≤
                            ‖Complex.binetAbelPlanaFiniteLowerContourTail N w‖ +
                              ‖Complex.binetAbelPlanaFiniteUpperContourResidual N w‖ := by
                        exact norm_add_le
                          (Complex.binetAbelPlanaFiniteLowerContourTail N w)
                          (Complex.binetAbelPlanaFiniteUpperContourResidual N w)
                      _ ≤
                          (C * ∫ t : ℝ in Set.Ioi (N : ℝ),
                              Complex.binetAbelPlanaVerticalKernelMajorant t) +
                            Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N := by
                        exact add_le_add hN_lower hN_upper)))

/-- Owner finite-contour remainder estimate in majorant form. -/
theorem Complex.exists_norm_binetAbelPlanaFiniteRemainderError_le_kernelTail_add_upperMajorant_owner
    {w : ℂ}
    (hw : 0 < w.re)
    (hfinite :
      ∀ N : ℕ,
        Complex.binetAbelPlanaLogGammaFiniteApproximation N w =
          Complex.binetAbelPlanaFiniteMainTerm N w +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N w +
              Complex.binetAbelPlanaFiniteContourRemainder N w) :
    ∃ C : ℝ,
      0 ≤ C ∧
          ∀ᶠ N : ℕ in Filter.atTop,
            ‖Complex.binetAbelPlanaFiniteRemainderError N w‖ ≤
              (C * ∫ t : ℝ in Set.Ioi (N : ℝ),
                  Complex.binetAbelPlanaVerticalKernelMajorant t) +
                Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N := by
  have hidentity :
      ∀ N : ℕ,
        Complex.binetAbelPlanaFiniteRemainderError N w =
          Complex.binetAbelPlanaFiniteContourRemainder N w :=
    Complex.binetAbelPlanaFiniteRemainderError_eq_contourRemainder_owner
      hfinite
  exact
    match
      Complex.exists_norm_binetAbelPlanaFiniteContourRemainder_le_kernelTail_add_upperMajorant_owner
        hw with
    | ⟨C, hC_nonneg, hbound⟩ =>
      Exists.intro C
        (And.intro hC_nonneg
          (hbound.mono
            (fun N hN => hidentity N ▸ hN)))

/-- Norm convergence from a fixed-ray lower kernel-tail estimate and the
upper-endpoint majorant estimate. -/
theorem Complex.binetAbelPlanaFiniteRemainderError_norm_tendsto_zero_of_kernelTail_add_upperMajorant
    {w : ℂ}
    {C : ℝ}
    (_hC_nonneg : 0 ≤ C)
    (hbound :
        ∀ᶠ N : ℕ in Filter.atTop,
          ‖Complex.binetAbelPlanaFiniteRemainderError N w‖ ≤
            (C * ∫ t : ℝ in Set.Ioi (N : ℝ),
                Complex.binetAbelPlanaVerticalKernelMajorant t) +
              Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N) :
    Filter.Tendsto
      (fun N : ℕ =>
        ‖Complex.binetAbelPlanaFiniteRemainderError N w‖)
      Filter.atTop
      (𝓝 (0 : ℝ)) := by
  have hlower_tail :
      Filter.Tendsto
        (fun N : ℕ =>
          ∫ t : ℝ in Set.Ioi (N : ℝ),
            Complex.binetAbelPlanaVerticalKernelMajorant t)
        Filter.atTop
        (𝓝 (0 : ℝ)) := by
    have hmajorant :
        Filter.Tendsto
          (fun N : ℕ =>
            Complex.binetAbelPlanaFiniteLowerContourTailMajorant w N)
          Filter.atTop
          (𝓝 (0 : ℝ)) :=
      Complex.binetAbelPlanaFiniteLowerContourTailMajorant_tendsto_zero w
    have hscale :
        Filter.Tendsto
          (fun N : ℕ =>
            (2 : ℝ) * ∫ t : ℝ in Set.Ioi (N : ℝ),
              Complex.binetAbelPlanaVerticalKernelMajorant t)
          Filter.atTop
          (𝓝 (0 : ℝ)) := by
      have hevent :
          (fun N : ℕ =>
            Complex.binetAbelPlanaFiniteLowerContourTailMajorant w N) =ᶠ[Filter.atTop]
          (fun N : ℕ =>
            (2 : ℝ) * ∫ t : ℝ in Set.Ioi (N : ℝ),
              Complex.binetAbelPlanaVerticalKernelMajorant t) :=
        Filter.Eventually.of_forall
          (fun _N => rfl)
      exact hmajorant.congr' hevent
    have hinv :
        Filter.Tendsto
          (fun N : ℕ =>
            (1 / 2 : ℝ) *
              ((2 : ℝ) * ∫ t : ℝ in Set.Ioi (N : ℝ),
                Complex.binetAbelPlanaVerticalKernelMajorant t))
          Filter.atTop
          (𝓝 ((1 / 2 : ℝ) * 0)) :=
      tendsto_const_nhds.mul hscale
    have hevent_tail :
        (fun N : ℕ =>
          (1 / 2 : ℝ) *
            ((2 : ℝ) * ∫ t : ℝ in Set.Ioi (N : ℝ),
              Complex.binetAbelPlanaVerticalKernelMajorant t)) =ᶠ[Filter.atTop]
        (fun N : ℕ =>
          ∫ t : ℝ in Set.Ioi (N : ℝ),
            Complex.binetAbelPlanaVerticalKernelMajorant t) :=
      Filter.Eventually.of_forall
        (fun N =>
          Real.half_mul_two_mul
            (∫ t : ℝ in Set.Ioi (N : ℝ),
              Complex.binetAbelPlanaVerticalKernelMajorant t))
    exact (mul_zero (1 / 2 : ℝ)).symm ▸ (hinv.congr' hevent_tail)
  have hlower_scaled :
      Filter.Tendsto
        (fun N : ℕ =>
          C * ∫ t : ℝ in Set.Ioi (N : ℝ),
            Complex.binetAbelPlanaVerticalKernelMajorant t)
        Filter.atTop
        (𝓝 (C * 0)) :=
    tendsto_const_nhds.mul hlower_tail
  have hupper :
      Filter.Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N)
        Filter.atTop
        (𝓝 (0 : ℝ)) :=
    Complex.binetAbelPlanaFiniteUpperContourResidualMajorant_tendsto_zero w
  have hsum :
      Filter.Tendsto
        (fun N : ℕ =>
          (C * ∫ t : ℝ in Set.Ioi (N : ℝ),
              Complex.binetAbelPlanaVerticalKernelMajorant t) +
            Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N)
        Filter.atTop
        (𝓝 (C * 0 + 0)) :=
    hlower_scaled.add hupper
  exact
    squeeze_zero'
      (Filter.Eventually.of_forall
        (fun N : ℕ =>
          norm_nonneg
            (Complex.binetAbelPlanaFiniteRemainderError N w)))
      hbound
      ((Real.mul_zero_add_zero C) ▸ hsum)

/-- Norm decay of the finite Abel-Plana contour remainder.

This is the finite-contour estimate for the logarithmic summand.  It is stated
as norm convergence because the classical proof bounds the top and vertical
finite-contour residuals before passing to the complex limit. -/
theorem Complex.binetAbelPlanaFiniteRemainderError_norm_tendsto_zero_owner
    {w : ℂ}
    (hw : 0 < w.re)
    (hfinite :
      ∀ N : ℕ,
        Complex.binetAbelPlanaLogGammaFiniteApproximation N w =
          Complex.binetAbelPlanaFiniteMainTerm N w +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N w +
              Complex.binetAbelPlanaFiniteContourRemainder N w) :
    Filter.Tendsto
      (fun N : ℕ =>
        ‖Complex.binetAbelPlanaFiniteRemainderError N w‖)
      Filter.atTop
      (𝓝 (0 : ℝ)) := by
  have hnorm_bound :
      ∃ C : ℝ,
        0 ≤ C ∧
            ∀ᶠ N : ℕ in Filter.atTop,
              ‖Complex.binetAbelPlanaFiniteRemainderError N w‖ ≤
                (C * ∫ t : ℝ in Set.Ioi (N : ℝ),
                    Complex.binetAbelPlanaVerticalKernelMajorant t) +
                  Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N :=
    Complex.exists_norm_binetAbelPlanaFiniteRemainderError_le_kernelTail_add_upperMajorant_owner
      hw hfinite
  exact
    match hnorm_bound with
    | ⟨_C, hC_nonneg, hbound⟩ =>
      Complex.binetAbelPlanaFiniteRemainderError_norm_tendsto_zero_of_kernelTail_add_upperMajorant
        hC_nonneg
        hbound

/-- Algebraic/topological assembly of complex convergence from norm decay of
the finite Abel-Plana contour remainder. -/
theorem Complex.binetAbelPlanaFiniteRemainderError_tendsto_zero_of_norm_tendsto_zero
    {w : ℂ}
    (hnorm :
      Filter.Tendsto
        (fun N : ℕ =>
          ‖Complex.binetAbelPlanaFiniteRemainderError N w‖)
        Filter.atTop
        (𝓝 (0 : ℝ))) :
    Filter.Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteRemainderError N w)
      Filter.atTop
      (𝓝 (0 : ℂ)) := by
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

/-- Finite Abel-Plana contour-remainder decay in complex form. -/
theorem Complex.binetAbelPlanaFiniteRemainderError_tendsto_zero_from_contourNorm_owner
    {w : ℂ}
    (hw : 0 < w.re)
    (hfinite :
      ∀ N : ℕ,
        Complex.binetAbelPlanaLogGammaFiniteApproximation N w =
          Complex.binetAbelPlanaFiniteMainTerm N w +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N w +
              Complex.binetAbelPlanaFiniteContourRemainder N w) :
    Filter.Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteRemainderError N w)
      Filter.atTop
      (𝓝 (0 : ℂ)) := by
  exact
    Complex.binetAbelPlanaFiniteRemainderError_tendsto_zero_of_norm_tendsto_zero
      (Complex.binetAbelPlanaFiniteRemainderError_norm_tendsto_zero_owner hw hfinite)

end

end LFunctions
end Boundary
