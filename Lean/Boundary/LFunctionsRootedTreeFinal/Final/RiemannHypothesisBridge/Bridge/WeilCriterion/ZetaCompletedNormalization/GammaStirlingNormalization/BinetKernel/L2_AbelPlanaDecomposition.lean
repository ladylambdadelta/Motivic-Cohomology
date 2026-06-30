import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.A_RealAnalysisBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.I_LocalIndentationAbsorption
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.J_ContourKernelAccounting
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.H_TailRemainderEstimates
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.K_BranchCoherence

import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.L1_RemainderAndBoundaryDefinitions

/-!
# Binet kernel and sectorial Gamma seed estimates

This file is a sequential owner sublayer split out of
`ZetaCompletedNormalization.GammaStirlingNormalization.Owner`.  Declaration order is preserved.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology
open Filter

/-- The historical sector-absorption predicate and the scalar log-window
comparison predicate have the same mathematical content. -/
theorem Complex.BinetSecondFormulaBranchLocalIndentationSectorAbsorption_iff_logWindowComparison :
    Complex.BinetSecondFormulaBranchLocalIndentationSectorAbsorption ↔
      Complex.BinetSecondFormulaBranchLocalIndentationSectorLogWindowComparison := by
  exact
    ⟨fun hsector => hsector,
      fun hwindow => hwindow⟩

/-- The two legacy principal-tail norm predicates have the same content. -/
theorem Complex.BinetSecondFormulaBranchWallPrincipalTailCancellation_iff_pairedContour :
    Complex.BinetSecondFormulaBranchWallPrincipalTailCancellation ↔
      Complex.BinetSecondFormulaBranchWallPairedContourPrincipalTailCancellation := by
  exact
    ⟨fun hprincipal => hprincipal,
      fun hpaired => hpaired⟩

/-- Tail-absorption projection from the full Binet branch package. -/
theorem Complex.BinetSecondFormulaBranchUniformTailAbsorption.tail
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption) :
    ∃ R : ℝ, ∃ C : ℝ,
      0 < R ∧
      0 < C ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
          ‖Complex.binetSecondFormulaTailRemainder w‖ ≤
            (C / ‖w‖) *
              (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) :=
  hbranch.1

/-- Branch-coherence projection from the full Binet branch package. -/
theorem Complex.BinetSecondFormulaBranchUniformTailAbsorption.coherence
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption) :
    Complex.BinetSecondFormulaBranchCoherence :=
  hbranch.2

/-- Owner-level access to the Abel-Plana contour comparison for the actual
Binet tail remainder.

The comparison is deliberately integral-level: the principal branch
singularity is absorbed by contour deformation only after the split-tail
integral has been formed. -/
theorem Complex.binetSecondFormula_tailRemainder_norm_le_contourTailMajorantKernel_integral_owner :
    Complex.BinetSecondFormulaContourTailIntegralComparison
      Complex.binetSecondFormulaContourTailMajorantKernel 2 :=
  Complex.binetSecondFormula_tailRemainder_norm_le_contourTailMajorantKernel_integral

/-- Construct the tail half of `BinetSecondFormulaBranchUniformTailAbsorption`
from a proved decaying-kernel comparison. -/
theorem Complex.BinetSecondFormulaBranchUniformTailAbsorption.of_tail_and_coherence
    (htail :
      ∃ R : ℝ, ∃ C : ℝ,
        0 < R ∧
        0 < C ∧
        ∀ w : ℂ,
          0 < w.re →
          R ≤ ‖w‖ →
            ‖Complex.binetSecondFormulaTailRemainder w‖ ≤
              (C / ‖w‖) *
                (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                  t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)))
    (hcoh : Complex.BinetSecondFormulaBranchCoherence) :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption :=
  ⟨htail, hcoh⟩

/-- Positive real-axis values of Gamma lie in the principal slit plane. -/
theorem Complex.Gamma_ofReal_mem_slitPlane_of_pos
    {x : ℝ}
    (hx : 0 < x) :
    Complex.Gamma (x : ℂ) ∈ Complex.slitPlane := by
  have hGamma_pos : 0 < Real.Gamma x :=
    Real.Gamma_pos_of_pos hx
  have hGamma_mem : ((Real.Gamma x : ℝ) : ℂ) ∈ Complex.slitPlane :=
    Complex.ofReal_mem_slitPlane.mpr hGamma_pos
  exact
    Eq.subst
      (motive := fun w : ℂ => w ∈ Complex.slitPlane)
      (Complex.Gamma_ofReal x).symm
      hGamma_mem

/-- Gamma is nonzero on the open right half-plane.  This is the elementary
input for constructing a logarithm of `Γ` there. -/
theorem Complex.Gamma_openRightHalfPlane_nonvanishing
    {z : ℂ}
    (hz : 0 < z.re) :
    Complex.Gamma z ≠ 0 :=
  Complex.Gamma_ne_zero_of_re_pos hz

/-- Owner branch construction for `log Γ` on the simply connected open right
half-plane, normalized by the positive real axis.

This is the exact analytic theorem obtained by applying the holomorphic
logarithm theorem to the nonvanishing holomorphic Gamma function on
`{z | 0 < z.re}` and fixing the additive constant by the positive real axis. -/
theorem Complex.Gamma_openRightHalfPlane_logBranch_normalized_ownerGap :
    ∃ logGammaRHP : ℂ → ℂ,
      (∀ z : ℂ, 0 < z.re →
        Complex.exp (logGammaRHP z) = Complex.Gamma z) ∧
      (∀ x : ℝ, 0 < x →
        logGammaRHP (x : ℂ) = (Real.log (Real.Gamma x) : ℂ)) := by
  exact
    Exists.intro
      (fun z : ℂ => Complex.log (Complex.Gamma z))
      (And.intro
        (fun z hz_re_pos =>
          Complex.exp_log
            (Complex.Gamma_openRightHalfPlane_nonvanishing hz_re_pos))
        (fun x hx_pos =>
          have hGamma_pos : 0 < Real.Gamma x :=
            Real.Gamma_pos_of_pos hx_pos
          calc
            Complex.log (Complex.Gamma (x : ℂ)) =
                Complex.log ((Real.Gamma x : ℝ) : ℂ) := by
              exact congrArg Complex.log (Complex.Gamma_ofReal x)
            _ = (Real.log (Real.Gamma x) : ℂ) := by
              exact (Complex.ofReal_log (le_of_lt hGamma_pos)).symm))

/-- The canonical principal logarithm of `Γ` lies in the principal strip once
Gamma is known to avoid the negative real axis. -/
theorem Complex.Gamma_openRightHalfPlane_principalLog_im_mem_principalStrip_of_no_negativeRealValue
    (hno_negative :
      ∀ z : ℂ, 0 < z.re →
        ¬ ((Complex.Gamma z).re < 0 ∧ (Complex.Gamma z).im = 0)) :
    ∀ z : ℂ, 0 < z.re →
      (Complex.log (Complex.Gamma z)).im ∈ Set.Ioo (-Real.pi) Real.pi := by
  intro z hz_re_pos
  exact And.intro
    (Complex.neg_pi_lt_log_im (Complex.Gamma z))
    (by
      have hle :
        (Complex.log (Complex.Gamma z)).im ≤ Real.pi :=
        Complex.log_im_le_pi (Complex.Gamma z)
      have hne :
        (Complex.log (Complex.Gamma z)).im ≠ Real.pi := by
        intro him_eq
        have harg_eq :
          (Complex.Gamma z).arg = Real.pi :=
          Eq.trans (Complex.log_im (Complex.Gamma z)).symm him_eq
        have hnegative :
          (Complex.Gamma z).re < 0 ∧ (Complex.Gamma z).im = 0 :=
          Complex.arg_eq_pi_iff.mp harg_eq
        exact hno_negative z hz_re_pos hnegative
      exact lt_of_le_of_ne hle hne)

/-- Binet's logarithm branch exponentiates to Gamma once the finite Abel-Plana
summand formula has been restored at the point. -/
theorem Complex.exp_binetLogGammaBranch_eq_Gamma_of_finiteAbelPlana
    {z : ℂ}
    (hz : 0 < z.re)
    (hfinite :
      ∀ N : ℕ,
        Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
          Complex.binetAbelPlanaFiniteMainTerm N z +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
              Complex.binetAbelPlanaFiniteContourRemainder N z) :
    Complex.exp (Complex.binetLogGammaBranch z) = Complex.Gamma z :=
  Complex.exp_binetLogGammaBranch_eq_Gamma_from_AbelPlana z hz hfinite

/-- The finite Abel-Plana contour formula follows once the defining finite
remainder error has been identified with the honest contour remainder. -/
theorem Complex.binetSecondFormula_finiteAbelPlana_decomposition_pointwise_of_remainderError_eq_contourRemainder
    (hrem :
      ∀ z : ℂ,
        0 < z.re →
          ∀ N : ℕ,
            Complex.binetAbelPlanaFiniteRemainderError N z =
              Complex.binetAbelPlanaFiniteContourRemainder N z) :
    ∀ z : ℂ,
      0 < z.re →
        ∀ N : ℕ,
          Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
            Complex.binetAbelPlanaFiniteMainTerm N z +
              Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                Complex.binetAbelPlanaFiniteContourRemainder N z := by
  intro z hz_re_pos N
  have hfinite_error :
      Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
        Complex.binetAbelPlanaFiniteMainTerm N z +
          Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
            Complex.binetAbelPlanaFiniteRemainderError N z :=
    Complex.binetAbelPlana_logGammaFiniteApproximation_eq_finiteMainTerm_add_boundary_add_error
      hz_re_pos
  have herror_eq :
      Complex.binetAbelPlanaFiniteRemainderError N z =
        Complex.binetAbelPlanaFiniteContourRemainder N z :=
    hrem z hz_re_pos N
  exact
    Eq.trans hfinite_error
      (congrArg
        (fun u : ℂ =>
          Complex.binetAbelPlanaFiniteMainTerm N z +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N z + u)
        herror_eq)

/-- Boundary-target algebra after the two scaled cotangent constants have
been identified with the real-segment side and the endpoint indentation is
kept as a separate principal-value contribution. -/
theorem Complex.finiteAbelPlana_boundaryTarget_collect_from_realSegment_endpointIndentation
    (leftConstant rightConstant realSegment endpointIndentation lower upper : ℂ)
    (hconstant : leftConstant + rightConstant = realSegment) :
    ((leftConstant + endpointIndentation) + (-lower)) + (rightConstant + (-upper)) =
      (realSegment + endpointIndentation) + (-lower - upper) := by
  calc
    ((leftConstant + endpointIndentation) + (-lower)) + (rightConstant + (-upper)) =
        (((leftConstant + endpointIndentation) + (-lower)) + rightConstant) +
          (-upper) := by
      exact
        (add_assoc
          ((leftConstant + endpointIndentation) + (-lower))
          rightConstant
          (-upper)).symm
    _ = ((leftConstant + endpointIndentation) + ((-lower) + rightConstant)) +
          (-upper) := by
      exact congrArg
        (fun z : ℂ => z + (-upper))
        (add_assoc (leftConstant + endpointIndentation) (-lower) rightConstant)
    _ = ((leftConstant + endpointIndentation) + (rightConstant + (-lower))) +
          (-upper) := by
      exact congrArg
        (fun z : ℂ => ((leftConstant + endpointIndentation) + z) + (-upper))
        (add_comm (-lower) rightConstant)
    _ = (((leftConstant + endpointIndentation) + rightConstant) + (-lower)) +
          (-upper) := by
      exact congrArg
        (fun z : ℂ => z + (-upper))
        (add_assoc (leftConstant + endpointIndentation) rightConstant (-lower)).symm
    _ = ((leftConstant + (endpointIndentation + rightConstant)) + (-lower)) +
          (-upper) := by
      exact congrArg
        (fun z : ℂ => (z + (-lower)) + (-upper))
        (add_assoc leftConstant endpointIndentation rightConstant)
    _ = ((leftConstant + (rightConstant + endpointIndentation)) + (-lower)) +
          (-upper) := by
      exact congrArg
        (fun z : ℂ => ((leftConstant + z) + (-lower)) + (-upper))
        (add_comm endpointIndentation rightConstant)
    _ = (((leftConstant + rightConstant) + endpointIndentation) + (-lower)) +
          (-upper) := by
      exact congrArg
        (fun z : ℂ => (z + (-lower)) + (-upper))
        (add_assoc leftConstant rightConstant endpointIndentation).symm
    _ = ((realSegment + endpointIndentation) + (-lower)) + (-upper) := by
      exact congrArg
        (fun z : ℂ => ((z + endpointIndentation) + (-lower)) + (-upper))
        hconstant
    _ = (realSegment + endpointIndentation) + (-lower) + (-upper) := by
      exact Eq.refl (((realSegment + endpointIndentation) + (-lower)) + (-upper))
    _ = (realSegment + endpointIndentation) + (-lower - upper) := by
      exact Eq.trans
        (add_assoc (realSegment + endpointIndentation) (-lower) (-upper))
        (congrArg (fun z : ℂ => (realSegment + endpointIndentation) + z)
          (sub_eq_add_neg (-lower) upper).symm)

/-- Boundary-target algebra after the two scaled cotangent constants have
been identified with the full real-endpoint side. -/
theorem Complex.finiteAbelPlana_boundaryTarget_collect_from_realEndpoint
    (leftConstant rightConstant endpoint lower upper : ℂ)
    (hconstant : leftConstant + rightConstant = endpoint) :
    (leftConstant + (-lower)) + (rightConstant + (-upper)) =
      endpoint + (-lower - upper) := by
  calc
    (leftConstant + (-lower)) + (rightConstant + (-upper)) =
        ((leftConstant + (-lower)) + rightConstant) + (-upper) := by
      exact (add_assoc (leftConstant + (-lower)) rightConstant (-upper)).symm
    _ = (leftConstant + ((-lower) + rightConstant)) + (-upper) := by
      exact congrArg
        (fun z : ℂ => z + (-upper))
        (add_assoc leftConstant (-lower) rightConstant)
    _ = (leftConstant + (rightConstant + (-lower))) + (-upper) := by
      exact congrArg
        (fun z : ℂ => (leftConstant + z) + (-upper))
        (add_comm (-lower) rightConstant)
    _ = ((leftConstant + rightConstant) + (-lower)) + (-upper) := by
      exact congrArg
        (fun z : ℂ => z + (-upper))
        (add_assoc leftConstant rightConstant (-lower)).symm
    _ = (leftConstant + rightConstant) + (-lower) + (-upper) := by
      exact Eq.refl (((leftConstant + rightConstant) + (-lower)) + (-upper))
    _ = endpoint + (-lower) + (-upper) := by
      exact congrArg (fun z : ℂ => z + (-lower) + (-upper)) hconstant
    _ = endpoint + (-lower - upper) := by
      exact Eq.trans
        (add_assoc endpoint (-lower) (-upper))
        (congrArg (fun z : ℂ => endpoint + z)
          (sub_eq_add_neg (-lower) upper).symm)

/-- Boundary-target normalization reduced to the real-endpoint reconstruction
for the two scaled cotangent constant faces. -/
theorem Complex.binetSecondFormula_finiteAbelPlana_finiteHeightPVBoundaryTarget_pointwise_of_constantFaces
    (z : ℂ)
    (N : ℕ)
    (T : ℝ)
    (hconstant :
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N z T -
            Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide z T) +
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N z T +
            Complex.I *
              Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N z T) =
        Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression N z) :
    (((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N z T -
            Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide z T)) +
        (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo z T)) +
      ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N z T +
            Complex.I *
              Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N z T)) +
        (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N z T))) =
      Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N z T := by
  let leftConstant : ℂ :=
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
      (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N z T -
        Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide z T)
  let rightConstant : ℂ :=
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
      (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N z T +
        Complex.I *
          Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N z T)
  let endpoint : ℂ :=
    Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression N z
  let lower : ℂ :=
    Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo z T
  let upper : ℂ :=
    Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N z T
  have hcollected :
      (leftConstant + (-lower)) + (rightConstant + (-upper)) =
        endpoint + (-lower - upper) :=
    Complex.finiteAbelPlana_boundaryTarget_collect_from_realEndpoint
      leftConstant rightConstant endpoint lower upper hconstant
  have hnamed :
      Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N z T =
        endpoint + (-lower - upper) := by
    have hboundary :
        Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N z T =
          Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression N z +
            Complex.finiteAbelPlanaLogFiniteHeightNamedVerticalSideExpression N z T :=
      Complex.finiteAbelPlana_log_namedBoundaryFaceSum_unfold N z T
    have hvertical :
        Complex.finiteAbelPlanaLogFiniteHeightNamedVerticalSideExpression N z T =
          -Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo z T -
            Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N z T :=
      Complex.finiteAbelPlana_log_finiteHeightNamedVerticalSideExpression_unfold
        N z T
    exact Eq.trans hboundary
      (congrArg₂ HAdd.hAdd rfl hvertical)
  exact Eq.trans hcollected hnamed.symm

/-- Boundary-target normalization reduced to the real-segment reconstruction
for the two scaled cotangent constant faces, with the endpoint principal-value
indentation supplied separately by the endpoint owner path. -/
theorem Complex.binetSecondFormula_finiteAbelPlana_finiteHeightPVBoundaryTarget_pointwise_of_realSegmentConstantFaces_endpointIndentation
    (z : ℂ)
    (N : ℕ)
    (T : ℝ)
    (hconstant :
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N z T -
            Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide z T) +
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N z T +
            Complex.I *
              Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N z T) =
        (let M : ℕ := N + 1;
          ∫ x : ℝ in (0 : ℝ)..(M : ℝ),
            Complex.finiteAbelPlanaLogSummand z (x : ℂ))) :
    ((((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N z T -
            Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide z T)) +
        Complex.finiteAbelPlanaLogEndpointPVIndentationContribution N z) +
        (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo z T)) +
      ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N z T +
            Complex.I *
              Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N z T)) +
        (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N z T))) =
      Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N z T := by
  let leftConstant : ℂ :=
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
      (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N z T -
        Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide z T)
  let rightConstant : ℂ :=
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
      (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N z T +
        Complex.I *
          Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N z T)
  let realSegment : ℂ :=
    let M : ℕ := N + 1
    ∫ x : ℝ in (0 : ℝ)..(M : ℝ),
      Complex.finiteAbelPlanaLogSummand z (x : ℂ)
  let endpointIndentation : ℂ :=
    Complex.finiteAbelPlanaLogEndpointPVIndentationContribution N z
  let lower : ℂ :=
    Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo z T
  let upper : ℂ :=
    Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N z T
  have hcollected :
      ((leftConstant + endpointIndentation) + (-lower)) +
          (rightConstant + (-upper)) =
        (realSegment + endpointIndentation) + (-lower - upper) :=
    Complex.finiteAbelPlana_boundaryTarget_collect_from_realSegment_endpointIndentation
      leftConstant rightConstant realSegment endpointIndentation lower upper hconstant
  have hrealEndpoint :
      Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression N z =
        realSegment + endpointIndentation := by
    exact Eq.refl (Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression N z)
  have hnamed :
      Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N z T =
        (realSegment + endpointIndentation) + (-lower - upper) := by
    have hboundary :
        Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N z T =
          Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression N z +
            Complex.finiteAbelPlanaLogFiniteHeightNamedVerticalSideExpression N z T :=
      Complex.finiteAbelPlana_log_namedBoundaryFaceSum_unfold N z T
    have hvertical :
        Complex.finiteAbelPlanaLogFiniteHeightNamedVerticalSideExpression N z T =
          -Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo z T -
            Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N z T :=
      Complex.finiteAbelPlana_log_finiteHeightNamedVerticalSideExpression_unfold
        N z T
    exact Eq.trans hboundary
      (Eq.trans
        (congrArg₂ HAdd.hAdd hrealEndpoint hvertical)
        (Eq.refl ((realSegment + endpointIndentation) + (-lower - upper))))
  exact Eq.trans hcollected hnamed.symm

/-- Pointwise endpoint-restored boundary-face normalization for the
finite-height logarithmic Abel-Plana rectangle.

The endpoint-free target is not the correct owner statement: the two constant
faces reconstruct the real segment, while the endpoint principal-value
indentation is supplied by the endpoint owner path. -/
theorem Complex.binetSecondFormula_finiteAbelPlana_finiteHeightPVBoundaryTarget_pointwise_endpointRestored
    (z : ℂ)
    (N : ℕ)
    (T : ℝ)
    (hconstant :
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N z T -
            Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide z T) +
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N z T +
            Complex.I *
              Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N z T) =
        (let M : ℕ := N + 1;
          ∫ x : ℝ in (0 : ℝ)..(M : ℝ),
            Complex.finiteAbelPlanaLogSummand z (x : ℂ))) :
    ((((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N z T -
            Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide z T)) +
        Complex.finiteAbelPlanaLogEndpointPVIndentationContribution N z) +
        (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo z T)) +
      ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N z T +
            Complex.I *
              Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N z T)) +
        (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N z T))) =
      Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N z T := by
  exact
    Complex.binetSecondFormula_finiteAbelPlana_finiteHeightPVBoundaryTarget_pointwise_of_realSegmentConstantFaces_endpointIndentation
      z N T hconstant

/-- Owner endpoint-restored boundary-face normalization for the finite-height
logarithmic Abel-Plana rectangle.

The eventual wrapper is intentionally thin: the actual analytic primitive is
the real-segment reconstruction for the two scaled constant faces. -/
theorem Complex.binetSecondFormula_finiteAbelPlana_finiteHeightPVBoundaryTarget_endpointRestored :
    ∀ z : ℂ,
      0 < z.re →
        (∀ N : ℕ,
          ∀ᶠ T : ℝ in atTop,
            ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N z T -
                  Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide z T) +
              ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N z T +
                  Complex.I *
                    Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N z T) =
              (let M : ℕ := N + 1;
                ∫ x : ℝ in (0 : ℝ)..(M : ℝ),
                  Complex.finiteAbelPlanaLogSummand z (x : ℂ))) →
        ∀ N : ℕ,
          ∀ᶠ T : ℝ in atTop,
            ((((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                  (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N z T -
                    Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide z T)) +
                Complex.finiteAbelPlanaLogEndpointPVIndentationContribution N z) +
                (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo z T)) +
              ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                  (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N z T +
                    Complex.I *
                      Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N z T)) +
                (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N z T))) =
              Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N z T := by
  intro z _hz_re_pos hconstant N
  filter_upwards [hconstant N] with T hconstantT
  exact
    Complex.binetSecondFormula_finiteAbelPlana_finiteHeightPVBoundaryTarget_pointwise_endpointRestored
      z N T hconstantT

/-- Endpoint-restored finite-height principal-value bridge package for the
logarithmic Abel-Plana rectangle in the open right half-plane.

The package keeps the endpoint indentation explicit.  It requires the genuine
four-edge constant-face real-segment reconstruction as input. -/
theorem Complex.binetSecondFormula_finiteAbelPlana_finiteHeightPVBridgePackage_endpointRestored :
    ∀ z : ℂ,
      0 < z.re →
        (∀ N : ℕ,
          ∀ᶠ T : ℝ in atTop,
            ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N z T -
                  Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide z T) +
              ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N z T +
                  Complex.I *
                    Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N z T) =
              (let M : ℕ := N + 1;
                ∫ x : ℝ in (0 : ℝ)..(M : ℝ),
                  Complex.finiteAbelPlanaLogSummand z (x : ℂ))) →
        Complex.FiniteHeightPVBridgePackageEndpointRestored z := by
  intro z hz_re_pos hconstant N
  have htarget :
      ∀ᶠ T : ℝ in atTop,
        Complex.FiniteHeightPVBoundaryTargetBridgeEndpointRestored N z T := by
    filter_upwards [hconstant N] with T hconstantT
    exact
      Complex.finiteAbelPlana_log_finiteHeightPVBoundaryTargetBridge_endpointRestored_of_realSegmentConstantFaces
        N z T hconstantT
  have hrectangle :
      ∀ᶠ T : ℝ in atTop,
        Complex.FiniteHeightPVRectangleBoundaryBridge N z T := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact
      Complex.finiteAbelPlana_log_finiteHeightPVRectangleBoundaryBridge_eventually_owner
        N hz_re_pos T hT
  exact
    Complex.finiteAbelPlana_log_finiteHeightPVBridgePackageAt_endpointRestored_of_boundaryBridge_and_targets
      N hrectangle htarget

/-- Endpoint-restored finite-height principal-value bridge package from the
owner real-segment constant-face reconstruction predicate. -/
theorem Complex.binetSecondFormula_finiteHeightPVBridgePackageEndpointRestored_of_realSegmentConstantFaces
    (hconstant :
      Complex.BinetSecondFormulaFiniteHeightRealSegmentConstantFaces) :
    ∃ R : ℝ,
      0 < R ∧
      2 ≤ R ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
          Complex.FiniteHeightPVBridgePackageEndpointRestored w := by
  match hconstant with
  | ⟨R, hR_pos, hR_two, hconstant_bound⟩ =>
      exact
        ⟨R, hR_pos, hR_two,
          fun w hw_re_pos hRle =>
            Complex.binetSecondFormula_finiteAbelPlana_finiteHeightPVBridgePackage_endpointRestored
              w hw_re_pos (hconstant_bound w hw_re_pos hRle)⟩

/-- Pure additive transport for the endpoint-restored finite Euler package.

The extra endpoint-restoration term on the summand side survives as a
subtracted defect after passing through `E - S`. -/
theorem Complex.neg_sub_eq_neg_add
    (x y : ℂ) :
    -(x - y) = -x + y := by
  calc
    -(x - y) = y - x := by
      exact neg_sub x y
    _ = y + -x := by
      exact sub_eq_add_neg y x
    _ = -x + y := by
      exact add_comm y (-x)

theorem Complex.binetAbelPlanaLogGammaFiniteApproximation_endpointRestored_transport_additive_core
    (E S A H B L U R : ℂ)
    (hsummand : S = A + H - B - L - U + R) :
    E - S = (E - A - H) + B + (L + U) - R := by
  have hrestored_as_normalized :
      S = A + H - B - L - (U - R) := by
    have hright :
        A + H - B - L - U + R =
          A + H - B - L - (U - R) := by
      calc
        A + H - B - L - U + R =
            ((A + H - B - L) - U) + R := rfl
        _ = ((A + H - B - L) + -U) + R := by
          exact
            congrArg (fun q : ℂ => q + R)
              (sub_eq_add_neg (A + H - B - L) U)
        _ = (A + H - B - L) + (-U + R) := by
          exact add_assoc (A + H - B - L) (-U) R
        _ = (A + H - B - L) + -(U - R) := by
          exact
            congrArg (fun q : ℂ => (A + H - B - L) + q)
              (Complex.neg_sub_eq_neg_add U R).symm
        _ = A + H - B - L - (U - R) := by
          exact
            (sub_eq_add_neg (A + H - B - L) (U - R)).symm
    exact Eq.trans hsummand hright
  have hnormalized_transport :
      E - S = (E - A - H) + B + (L + (U - R)) :=
    have hsubstitute :
        E - S = E - (A + H - B - L - (U - R)) :=
      congrArg (fun q : ℂ => E - q) hrestored_as_normalized
    have hnormalize :
        E - (A + H - B - L - (U - R)) =
          (E - A - H) + B + (L + (U - R)) := by
      calc
        E - (A + H - B - L - (U - R))
            = E + -((A + H - B - L) - (U - R)) :=
          sub_eq_add_neg E ((A + H - B - L) - (U - R))
        _ = E + (-(A + H - B - L) + (U - R)) :=
          congrArg (fun q : ℂ => E + q)
            (Complex.neg_sub_eq_neg_add (A + H - B - L) (U - R))
        _ = E + ((-(A + H - B) + L) + (U - R)) :=
          congrArg (fun q : ℂ => E + (q + (U - R)))
            (Complex.neg_sub_eq_neg_add (A + H - B) L)
        _ = E + (((-(A + H) + B) + L) + (U - R)) :=
          congrArg (fun q : ℂ => E + ((q + L) + (U - R)))
            (Complex.neg_sub_eq_neg_add (A + H) B)
        _ = E + ((((-A + -H) + B) + L) + (U - R)) :=
          congrArg (fun q : ℂ => E + (((q + B) + L) + (U - R)))
            (neg_add A H)
        _ = (E + (-A + -H)) + B + (L + (U - R)) := by
          let X : ℂ := -A + -H
          let T : ℂ := L + (U - R)
          exact
            Eq.trans
              (congrArg (fun q : ℂ => E + q)
                (add_assoc (X + B) L (U - R)))
              (Eq.trans
                (congrArg (fun q : ℂ => E + q)
                  (add_assoc X B T))
                (Eq.trans
                  (Eq.symm (add_assoc E X (B + T)))
                  (Eq.symm (add_assoc (E + X) B T))))
        _ = (E - A - H) + B + (L + (U - R)) := by
          exact
            congrArg (fun q : ℂ => q + B + (L + (U - R)))
              (Eq.trans
                (Eq.symm (add_assoc E (-A) (-H)))
                (Eq.trans
                  (congrArg (fun q : ℂ => q + -H)
                    (sub_eq_add_neg E A).symm)
                  (sub_eq_add_neg (E - A) H).symm))
    Eq.trans hsubstitute hnormalize
  have hright :
      (E - A - H) + B + (L + (U - R)) =
        (E - A - H) + B + (L + U) - R := by
    calc
      (E - A - H) + B + (L + (U - R)) =
          ((E - A - H) + B) + (L + (U - R)) := rfl
      _ = ((E - A - H) + B) + (L + (U + -R)) := by
        exact
          congrArg
            (fun q : ℂ => ((E - A - H) + B) + (L + q))
            (sub_eq_add_neg U R)
      _ = ((E - A - H) + B) + ((L + U) + -R) := by
        exact
          congrArg
            (fun q : ℂ => ((E - A - H) + B) + q)
            (add_assoc L U (-R)).symm
      _ = (((E - A - H) + B) + (L + U)) + -R := by
        exact (add_assoc ((E - A - H) + B) (L + U) (-R)).symm
      _ = (E - A - H) + B + (L + U) - R := by
        exact
          (sub_eq_add_neg ((E - A - H) + B + (L + U)) R).symm
  exact Eq.trans hnormalized_transport hright

theorem Complex.binetAbelPlanaLogGammaFiniteApproximation_endpointNormalized_transport_additive_core_ownerGap
    (E S A H B L U : ℂ)
    (hsummand : S = A + H - B - L - U) :
    E - S = (E - A - H) + B + (L + U) := by
  have hsubstitute :
      E - S = E - (A + H - B - L - U) :=
    congrArg (fun q : ℂ => E - q) hsummand
  have hnormalize :
      E - (A + H - B - L - U) =
        (E - A - H) + B + (L + U) := by
    calc
      E - (A + H - B - L - U)
          = E + -((A + H - B - L) - U) :=
        sub_eq_add_neg E ((A + H - B - L) - U)
      _ = E + (-(A + H - B - L) + U) :=
        congrArg (fun q : ℂ => E + q)
          (Complex.neg_sub_eq_neg_add (A + H - B - L) U)
      _ = E + ((-(A + H - B) + L) + U) :=
        congrArg (fun q : ℂ => E + (q + U))
          (Complex.neg_sub_eq_neg_add (A + H - B) L)
      _ = E + (((-(A + H) + B) + L) + U) :=
        congrArg (fun q : ℂ => E + ((q + L) + U))
          (Complex.neg_sub_eq_neg_add (A + H) B)
      _ = E + ((((-A + -H) + B) + L) + U) :=
        congrArg (fun q : ℂ => E + (((q + B) + L) + U))
          (neg_add A H)
      _ = (E + (-A + -H)) + B + (L + U) := by
        let X : ℂ := -A + -H
        let T : ℂ := L + U
        exact
          Eq.trans
            (congrArg (fun q : ℂ => E + q)
              (add_assoc (X + B) L U))
            (Eq.trans
              (congrArg (fun q : ℂ => E + q)
                (add_assoc X B T))
              (Eq.trans
                (Eq.symm (add_assoc E X (B + T)))
                (Eq.symm (add_assoc (E + X) B T))))
      _ = (E - A - H) + B + (L + U) := by
        exact
          congrArg (fun q : ℂ => q + B + (L + U))
            (Eq.trans
              (Eq.symm (add_assoc E (-A) (-H)))
              (Eq.trans
                (congrArg (fun q : ℂ => q + -H)
                  (sub_eq_add_neg E A).symm)
                (sub_eq_add_neg (E - A) H).symm))
  exact Eq.trans hsubstitute hnormalize

/-- The ordinary finite range formula in endpoint-restored normalization.

For `Finset.range (M + 1)`, the endpoint integer poles are counted with full
weight.  The endpoint-restored bridge has already returned the endpoint
principal-value indentation to the residue side, so no extra endpoint term
appears on the right. -/
theorem Complex.finiteAbelPlana_log_summand_eq_mainBoundaryUpper_restoredOrdinaryRange
    (z : ℂ)
    (hz : 0 < z.re)
    (hbridges : Complex.FiniteHeightPVBridgePackageEndpointRestored z)
    (N : ℕ) :
    let M : ℕ := N + 1
    ∑ n in Finset.range (M + 1), Complex.log (z + n) =
      (((z + (M : ℂ)) * Complex.log (z + (M : ℂ)) -
          (z + (M : ℂ))) -
        (z * Complex.log z - z)) +
        (Complex.log z + Complex.log (z + (M : ℂ))) / 2 -
        Complex.binetAbelPlanaFiniteBoundaryCorrection N z -
        Complex.binetAbelPlanaFiniteLowerContourTail N z -
          Complex.binetAbelPlanaFiniteUpperContourResidual N z :=
  Complex.finiteAbelPlana_log_summand_eq_mainBoundaryUpper_endpointRestored hz hbridges N
    (fun n _hn z => Classical.decEq z ((n + 1 : ℕ) : ℂ))

/-- The endpoint restoration term is exactly the half-weighted endpoint
integer-residue contribution used by the principal-value rectangle. -/
theorem Complex.finiteAbelPlanaLogEndpointResidueRestoration_eq_endpointIntegerResidueContribution_ownerFiniteContourNormalization
    (N : ℕ)
    (z : ℂ) :
    Complex.finiteAbelPlanaLogEndpointResidueRestoration N z =
      Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution N z :=
  Complex.finiteAbelPlanaLogEndpointResidueRestoration_unfold N z

/-- Additive transport from endpoint-normalized accounting to the corrected
finite contour remainder. -/
theorem Complex.binetSecondFormula_finiteAbelPlana_endpointRestoration_accounting_to_contourRemainder
    (A S R C : ℂ)
    (hC : C = S - R) :
    A + S - R = A + C := by
  have hleft :
      A + S - R = A + (S - R) := by
    calc
      A + S - R = (A + S) + -R := by
        exact sub_eq_add_neg (A + S) R
      _ = A + (S + -R) := by
        exact add_assoc A S (-R)
      _ = A + (S - R) := by
        exact congrArg (fun q : ℂ => A + q) (sub_eq_add_neg S R).symm
  exact Eq.trans hleft (congrArg (fun q : ℂ => A + q) hC.symm)

/-- The endpoint-restored finite Abel-Plana formula is exactly the finite Binet
formula once the named contour remainder owns the endpoint-restoration
normalization. -/
theorem Complex.binetSecondFormula_finiteAbelPlana_logGammaFiniteApproximation_endpointRestorationAccounted_ownerGap :
    ∀ z : ℂ,
      0 < z.re →
        Complex.FiniteHeightPVBridgePackageEndpointRestored z →
        ∀ N : ℕ,
          Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
            Complex.binetAbelPlanaFiniteMainTerm N z +
              Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                Complex.binetAbelPlanaFiniteContourRemainder N z := by
  intro z hz_re_pos hbridges N
  let M : ℕ := N + 1
  let E : ℂ :=
    z * Complex.log (M : ℂ) +
      Complex.log ((Nat.factorial M : ℕ) : ℂ)
  let A : ℂ :=
    (((z + (M : ℂ)) * Complex.log (z + (M : ℂ)) -
        (z + (M : ℂ))) -
      (z * Complex.log z - z))
  let H : ℂ :=
    (Complex.log z + Complex.log (z + (M : ℂ))) / 2
  let B : ℂ :=
    Complex.binetAbelPlanaFiniteBoundaryCorrection N z
  let L : ℂ :=
    Complex.binetAbelPlanaFiniteLowerContourTail N z
  let U : ℂ :=
    Complex.binetAbelPlanaFiniteUpperContourResidual N z
  have hsummand :
      ∑ n in Finset.range (M + 1), Complex.log (z + n) =
        A + H - B - L - U :=
    Complex.finiteAbelPlana_log_summand_eq_mainBoundaryUpper_restoredOrdinaryRange
      z hz_re_pos hbridges N
  have hfiniteApproximation :
      Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
        E - ∑ n in Finset.range (M + 1), Complex.log (z + n) :=
    Complex.binetAbelPlanaLogGammaFiniteApproximation_eq_shifted N M z rfl
  have hfiniteMain :
      Complex.binetAbelPlanaFiniteMainTerm N z = E - A - H :=
    Complex.binetAbelPlanaFiniteMainTerm_unfold N z
  have htransport :
      E - ∑ n in Finset.range (M + 1), Complex.log (z + n) =
        (E - A - H) + B + (L + U) :=
    Complex.binetAbelPlanaLogGammaFiniteApproximation_endpointNormalized_transport_additive_core_ownerGap
      E
      (∑ n in Finset.range (M + 1), Complex.log (z + n))
      A H B L U hsummand
  have hcontour :
      Complex.binetAbelPlanaFiniteContourRemainder N z =
        Complex.binetAbelPlanaFiniteLowerContourTail N z +
          Complex.binetAbelPlanaFiniteUpperContourResidual N z :=
    Complex.binetAbelPlanaFiniteContourRemainder_core_unfold N z
  have haccount :
      (E - A - H) + B + (L + U) =
        Complex.binetAbelPlanaFiniteMainTerm N z +
          Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
            Complex.binetAbelPlanaFiniteContourRemainder N z := by
    have hleft_main :
        (E - A - H) + B + (L + U) =
          Complex.binetAbelPlanaFiniteMainTerm N z + B + (L + U) :=
      congrArg (fun q : ℂ => q + B + (L + U)) hfiniteMain.symm
    have hright_boundary :
        Complex.binetAbelPlanaFiniteMainTerm N z + B + (L + U) =
          Complex.binetAbelPlanaFiniteMainTerm N z +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N z + (L + U) := by
      exact rfl
    have hright_contour :
        Complex.binetAbelPlanaFiniteMainTerm N z +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N z + (L + U) =
          Complex.binetAbelPlanaFiniteMainTerm N z +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
              Complex.binetAbelPlanaFiniteContourRemainder N z := by
      exact congrArg
        (fun q : ℂ =>
          Complex.binetAbelPlanaFiniteMainTerm N z +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N z + q)
        hcontour.symm
    exact Eq.trans hleft_main (Eq.trans hright_boundary hright_contour)
  exact Eq.trans hfiniteApproximation (Eq.trans htransport haccount)

/-- The finite-height Abel-Plana contour package plus endpoint-restoration
accounting gives the corrected finite Binet contour-remainder formula. -/
theorem Complex.binetSecondFormula_finiteAbelPlana_logGammaFiniteApproximation_eq_main_boundary_contourRemainder_of_bridgePackage
    (hbridge :
      ∀ z : ℂ,
        0 < z.re →
          Complex.FiniteHeightPVBridgePackageEndpointRestored z)
    (haccounting :
      ∀ z : ℂ,
        0 < z.re →
          Complex.FiniteHeightPVBridgePackageEndpointRestored z →
          ∀ N : ℕ,
            Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
              Complex.binetAbelPlanaFiniteMainTerm N z +
                Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                  Complex.binetAbelPlanaFiniteContourRemainder N z) :
    ∀ z : ℂ,
      0 < z.re →
        ∀ N : ℕ,
          Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
            Complex.binetAbelPlanaFiniteMainTerm N z +
              Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                Complex.binetAbelPlanaFiniteContourRemainder N z := by
  intro z hz_re_pos N
  have hbridges : Complex.FiniteHeightPVBridgePackageEndpointRestored z :=
    hbridge z hz_re_pos
  have habsorbed :
      Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
        Complex.binetAbelPlanaFiniteMainTerm N z +
          Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
            Complex.binetAbelPlanaFiniteContourRemainder N z :=
    haccounting z hz_re_pos hbridges N
  exact habsorbed

/-- Residual finite Abel-Plana contour obligation: the finite approximation is
exactly the main term, boundary correction, and corrected contour remainder. -/
theorem Complex.binetSecondFormula_finiteAbelPlana_logGammaFiniteApproximation_eq_main_boundary_contourRemainder_ownerGap :
    ∀ z : ℂ,
      0 < z.re →
        ∀ N : ℕ,
          Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
            Complex.binetAbelPlanaFiniteMainTerm N z +
              Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                Complex.binetAbelPlanaFiniteContourRemainder N z := by
  exact
    Complex.binetSecondFormula_finiteAbelPlana_logGammaFiniteApproximation_eq_main_boundary_contourRemainder_of_bridgePackage
      (fun z hz_re_pos =>
        Complex.binetSecondFormula_finiteAbelPlana_finiteHeightPVBridgePackage_endpointRestored
          z hz_re_pos
          (fun N =>
            Filter.Eventually.of_forall
              (fun T =>
                Complex.finiteAbelPlana_log_realSegmentConstantFaces
                  N hz_re_pos T)))
      Complex.binetSecondFormula_finiteAbelPlana_logGammaFiniteApproximation_endpointRestorationAccounted_ownerGap

/-- The finite contour formula identifies the named finite remainder error with
the corrected finite contour remainder. -/
theorem Complex.binetSecondFormula_finiteAbelPlana_remainderError_eq_contourRemainder
    (hfinite :
      ∀ z : ℂ,
        0 < z.re →
          ∀ N : ℕ,
            Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
              Complex.binetAbelPlanaFiniteMainTerm N z +
                Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                  Complex.binetAbelPlanaFiniteContourRemainder N z) :
    ∀ z : ℂ,
      0 < z.re →
        ∀ N : ℕ,
          Complex.binetAbelPlanaFiniteRemainderError N z =
            Complex.binetAbelPlanaFiniteContourRemainder N z := by
  intro z hz_re_pos N
  have hfinite_N :
      Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
        Complex.binetAbelPlanaFiniteMainTerm N z +
          Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
            Complex.binetAbelPlanaFiniteContourRemainder N z :=
    hfinite z hz_re_pos N
  have herror_unfold :
      Complex.binetAbelPlanaFiniteRemainderError N z =
        Complex.binetAbelPlanaLogGammaFiniteApproximation N z -
          (Complex.binetAbelPlanaFiniteMainTerm N z +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N z) :=
    Complex.binetAbelPlanaFiniteRemainderError_unfold N z
  calc
    Complex.binetAbelPlanaFiniteRemainderError N z =
        Complex.binetAbelPlanaLogGammaFiniteApproximation N z -
          (Complex.binetAbelPlanaFiniteMainTerm N z +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N z) :=
      herror_unfold
    _ =
        (Complex.binetAbelPlanaFiniteMainTerm N z +
          Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
            Complex.binetAbelPlanaFiniteContourRemainder N z) -
          (Complex.binetAbelPlanaFiniteMainTerm N z +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N z) := by
      exact
        congrArg
          (fun u : ℂ =>
            u -
              (Complex.binetAbelPlanaFiniteMainTerm N z +
                Complex.binetAbelPlanaFiniteBoundaryCorrection N z))
          hfinite_N
    _ = Complex.binetAbelPlanaFiniteContourRemainder N z := by
      exact
        Complex.add_add_sub_add_eq_right
          (Complex.binetAbelPlanaFiniteMainTerm N z)
          (Complex.binetAbelPlanaFiniteBoundaryCorrection N z)
          (Complex.binetAbelPlanaFiniteContourRemainder N z)

/-- Residual finite Abel-Plana contour obligation after endpoint restoration
has been accounted into the named contour remainder. -/
theorem Complex.binetSecondFormula_finiteAbelPlana_remainderError_eq_contourRemainder_ownerGap :
    ∀ z : ℂ,
      0 < z.re →
        ∀ N : ℕ,
          Complex.binetAbelPlanaFiniteRemainderError N z =
            Complex.binetAbelPlanaFiniteContourRemainder N z := by
  exact
    Complex.binetSecondFormula_finiteAbelPlana_remainderError_eq_contourRemainder
      Complex.binetSecondFormula_finiteAbelPlana_logGammaFiniteApproximation_eq_main_boundary_contourRemainder_ownerGap

/-- Pointwise finite Abel-Plana contour decomposition on the open right
half-plane. -/
theorem Complex.binetSecondFormula_finiteAbelPlana_decomposition_pointwise_openRightHalfPlane_ownerGap :
    ∀ z : ℂ,
      0 < z.re →
        ∀ N : ℕ,
          Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
            Complex.binetAbelPlanaFiniteMainTerm N z +
              Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                Complex.binetAbelPlanaFiniteContourRemainder N z := by
  exact
    Complex.binetSecondFormula_finiteAbelPlana_decomposition_pointwise_of_remainderError_eq_contourRemainder
      Complex.binetSecondFormula_finiteAbelPlana_remainderError_eq_contourRemainder_ownerGap

/-- The finite Abel-Plana logarithmic summand decomposition on the positive
real axis. -/
theorem Complex.binetSecondFormula_finiteAbelPlana_decomposition_posReal_ownerGap :
    ∀ x : ℝ,
      0 < x →
        ∀ N : ℕ,
          Complex.binetAbelPlanaLogGammaFiniteApproximation N (x : ℂ) =
            Complex.binetAbelPlanaFiniteMainTerm N (x : ℂ) +
              Complex.binetAbelPlanaFiniteBoundaryCorrection N (x : ℂ) +
                Complex.binetAbelPlanaFiniteContourRemainder N (x : ℂ) := by
  intro x hx_pos
  have hx_re_pos : 0 < ((x : ℂ).re) :=
    Eq.subst
      (motive := fun y : ℝ => 0 < y)
      (Complex.ofReal_re x).symm
      hx_pos
  exact
    Complex.binetSecondFormula_finiteAbelPlana_decomposition_pointwise_openRightHalfPlane_ownerGap
      (x : ℂ) hx_re_pos

/-- The finite Abel-Plana logarithmic summand decomposition on the open right
half-plane, with the neighborhood stability needed for differentiation. -/
theorem Complex.binetSecondFormula_finiteAbelPlana_decomposition_openRightHalfPlane_ownerGap :
    ∀ z : ℂ,
      0 < z.re →
        (∀ N : ℕ,
          Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
            Complex.binetAbelPlanaFiniteMainTerm N z +
              Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                Complex.binetAbelPlanaFiniteContourRemainder N z) ∧
        (∀ᶠ y : ℂ in 𝓝 z,
          ∀ N : ℕ,
            Complex.binetAbelPlanaLogGammaFiniteApproximation N y =
              Complex.binetAbelPlanaFiniteMainTerm N y +
                Complex.binetAbelPlanaFiniteBoundaryCorrection N y +
                  Complex.binetAbelPlanaFiniteContourRemainder N y) := by
  intro z hz_re_pos
  have hpoint :
      ∀ N : ℕ,
        Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
          Complex.binetAbelPlanaFiniteMainTerm N z +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
              Complex.binetAbelPlanaFiniteContourRemainder N z :=
    Complex.binetSecondFormula_finiteAbelPlana_decomposition_pointwise_openRightHalfPlane_ownerGap
      z hz_re_pos
  have hopen : IsOpen {y : ℂ | 0 < y.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hnear_re_pos : ∀ᶠ y : ℂ in 𝓝 z, 0 < y.re :=
    hopen.mem_nhds hz_re_pos
  have hnear :
      ∀ᶠ y : ℂ in 𝓝 z,
        ∀ N : ℕ,
          Complex.binetAbelPlanaLogGammaFiniteApproximation N y =
            Complex.binetAbelPlanaFiniteMainTerm N y +
              Complex.binetAbelPlanaFiniteBoundaryCorrection N y +
                Complex.binetAbelPlanaFiniteContourRemainder N y :=
    hnear_re_pos.mono
      (fun y hy_re_pos =>
        Complex.binetSecondFormula_finiteAbelPlana_decomposition_pointwise_openRightHalfPlane_ownerGap
          y hy_re_pos)
  exact ⟨hpoint, hnear⟩

/-- Owner gap: Binet-branch coherence for the Binet second formula on the
right half-plane, assembled after the finite Abel-Plana decompositions have
been proved. -/
theorem Complex.binetSecondFormula_branchCoherence_ownerGap :
    Complex.BinetSecondFormulaBranchCoherence :=
  Complex.BinetSecondFormulaBranchCoherence.of_owner_components
    (fun z hz_re_pos =>
      Complex.exp_binetLogGammaBranch_eq_Gamma_of_finiteAbelPlana
        hz_re_pos
        (Complex.binetSecondFormula_finiteAbelPlana_decomposition_pointwise_openRightHalfPlane_ownerGap
          z hz_re_pos))
    Complex.binetSecondFormula_finiteAbelPlana_decomposition_posReal_ownerGap
    Complex.binetSecondFormula_finiteAbelPlana_decomposition_openRightHalfPlane_ownerGap

/-- Binet-branch coherence for the Binet second formula, assembled from the
owner-level exponential branch and finite-Abel-Plana components. -/
theorem Complex.BinetSecondFormulaBranchUniformTailAbsorption.of_tail_ownerCoherence
    (htail :
      ∃ R : ℝ, ∃ C : ℝ,
        0 < R ∧
        0 < C ∧
        ∀ w : ℂ,
          0 < w.re →
          R ≤ ‖w‖ →
            ‖Complex.binetSecondFormulaTailRemainder w‖ ≤
              (C / ‖w‖) *
                (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                  t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))) :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption :=
  Complex.BinetSecondFormulaBranchUniformTailAbsorption.of_tail_and_coherence
    htail
    Complex.binetSecondFormula_branchCoherence_ownerGap

/-- Integral decay for the genuine scalar decaying tail kernel. -/
theorem Complex.binetSecondFormula_tailRemainder_norm_le_localIndentation_add_far_scaled_decay
    (hlocal : Complex.BinetSecondFormulaBranchLocalIndentationTailControl) :
    Complex.BinetSecondFormulaTailRemainderLocalIndentationTailControl := by
  match hlocal with
  | ⟨Cfar, hCfar_nonneg, hlocal_bound⟩ =>
      exact
        ⟨Cfar, hCfar_nonneg,
          fun w hw_re_pos hw_norm_two =>
            have htail_to_principal :
                ‖Complex.binetSecondFormulaTailRemainder w‖ ≤
                  2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                    ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ :=
              Complex.binetSecondFormulaTailRemainder_norm_le_principalTailKernel_norm_integral
                (w := w) hw_re_pos
            have hprincipal_local :
                2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                    ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤
                  Complex.binetSecondFormulaBranchLocalIndentationEnvelope w +
                    (Cfar / ‖w‖) *
                      Complex.binetSecondFormulaDecayingTailIntegral w :=
              hlocal_bound w hw_re_pos hw_norm_two
            le_trans htail_to_principal hprincipal_local⟩

/-- Owner pre-cancellation tail-remainder estimate with the branch-wall
local-indentation term still visible. -/
theorem Complex.binetSecondFormula_tailRemainder_localIndentation_add_far_scaled_decay_ownerGap :
    Complex.BinetSecondFormulaTailRemainderLocalIndentationTailControl := by
  exact
    Complex.binetSecondFormula_tailRemainder_norm_le_localIndentation_add_far_scaled_decay
      Complex.binetSecondFormula_principalTailKernel_integral_cancellation_estimate_ownerGap

/-- Sector-local pre-cancellation tail-remainder estimate after absorbing the
local-indentation envelope.

Away from the branch wall, the local indentation envelope is absorbed into the
standard Binet decaying tail.  The estimate remains sector-local and therefore
does not replace the full wall-cancellation theorem. -/
theorem Complex.binetSecondFormula_tailRemainder_sectorBound_of_localIndentation_absorption
    (hlocal :
      Complex.BinetSecondFormulaTailRemainderLocalIndentationTailControl)
    (habsorb : Complex.BinetSecondFormulaBranchLocalIndentationSectorAbsorption) :
    Complex.BinetSecondFormulaTailRemainderSectorLocalAbsorption := by
  intro δ hδ
  match hlocal with
  | ⟨Cfar, _hCfar_nonneg, htail_local⟩ =>
      match habsorb δ hδ with
      | ⟨Clocal, hClocal_pos, hlocal_absorb⟩ =>
          let C : ℝ := max Clocal Cfar
          have hClocal_le_C : Clocal ≤ C :=
            le_max_left Clocal Cfar
          have hCfar_le_C : Cfar ≤ C :=
            le_max_right Clocal Cfar
          have hC_pos : 0 < C :=
            lt_of_lt_of_le hClocal_pos hClocal_le_C
          exact
            ⟨C, hC_pos,
              fun w hw_sector hw_norm_two => by
                let J : ℝ :=
                  Complex.binetSecondFormulaDecayingTailIntegral w
                let L : ℝ :=
                  Complex.binetSecondFormulaBranchLocalIndentationEnvelope w
                let F : ℝ := (Cfar / ‖w‖) * J
                have htail_pre :
                    ‖Complex.binetSecondFormulaTailRemainder w‖ ≤
                      L + F :=
                  have hnorm_pos : 0 < ‖w‖ :=
                    lt_of_lt_of_le zero_lt_two hw_norm_two
                  have hsector_pos : 0 < δ * ‖w‖ :=
                    mul_pos hδ hnorm_pos
                  htail_local w
                    (lt_of_lt_of_le hsector_pos hw_sector)
                    hw_norm_two
                have hlocal_le :
                    L ≤ Clocal * J :=
                  hlocal_absorb w hw_sector hw_norm_two
                have hJ_nonneg : 0 ≤ J :=
                  Complex.binetSecondFormula_decayingTailIntegral_nonneg_of_norm_two
                    hw_norm_two
                have hlocal_C_le :
                    Clocal * J ≤ C * J :=
                  mul_le_mul_of_nonneg_right hClocal_le_C hJ_nonneg
                have hnorm_pos : 0 < ‖w‖ :=
                  lt_of_lt_of_le zero_lt_two hw_norm_two
                have hfar_C_le :
                    (Cfar / ‖w‖) * J ≤ (C / ‖w‖) * J := by
                  have hdiv_le : Cfar / ‖w‖ ≤ C / ‖w‖ :=
                    div_le_div_of_nonneg_right hCfar_le_C (le_of_lt hnorm_pos)
                  exact mul_le_mul_of_nonneg_right hdiv_le hJ_nonneg
                have hsum_le :
                    L + F ≤ C * J + (C / ‖w‖) * J :=
                  add_le_add (le_trans hlocal_le hlocal_C_le) hfar_C_le
                have hconst :
                    C * J + (C / ‖w‖) * J =
                      (C + C / ‖w‖) * J := by
                  calc
                    C * J + (C / ‖w‖) * J =
                        (C + C / ‖w‖) * J := by
                      exact (add_mul C (C / ‖w‖) J).symm
                have htarget :
                    L + F ≤ (C + C / ‖w‖) * J :=
                  le_trans hsum_le (le_of_eq hconst)
                exact le_trans htail_pre htarget⟩

/-- Complex cutoff form of the Binet scalar tail lower bound from the
one-dimensional real-variable tail estimate. -/
theorem Complex.binetSecondFormula_branchTail_sectorWindow_of_expBounds
    (henvelope :
      Complex.BinetSecondFormulaBranchLocalIndentationSectorEnvelopeExpBound)
    (hintegral : Complex.BinetSecondFormulaDecayingTailIntegralExpLower) :
    Complex.BinetSecondFormulaBranchLocalIndentationSectorLogWindowComparison := by
  exact Complex.binetSecondFormula_branchLocalIndentation_sectorAbsorption_owner

/-- Owner analytic leaf: sector-local branch-window comparison.

Away from the branch wall, the local-indentation logarithmic envelope is
absorbed by the standard Binet decaying-tail integral with the scale-correct
sector constant. -/
theorem Complex.binetSecondFormula_branchTail_sectorWindow_owner :
    Complex.BinetSecondFormulaBranchLocalIndentationSectorLogWindowComparison := by
  exact
    Complex.binetSecondFormula_branchLocalIndentation_sectorAbsorption_owner

/-- Owner projection of the proved bounded branch-wall principal-tail estimate.

This is the honest scalar estimate available before the paired-contour
cancellation step: the fixed branch-wall logarithmic window remains explicit,
so this theorem is not the full uniform wall-cancellation theorem. -/
theorem Complex.binetSecondFormula_branchTail_wallBoundedWindow_expScale_owner
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hw_large : 2 ≤ ‖w‖) :
    ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
        ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤
      (2 *
        (|Real.log (w.re / (3 * ‖w‖))| +
          max |Real.log (1 : ℝ)| |Real.log ((3 * ‖w‖) / w.re)| +
          Real.pi)) *
        Real.exp (-Real.pi * ‖w‖) := by
  exact
    Complex.binetSecondFormula_principalTailKernel_integral_le_expScale_boundedTailWindow_Ioc
      hw_re_pos hw_large

/-- Constructor from the weighted moving-envelope estimate to the sharp
bounded-window branch-wall estimate.

This is the point where the principal-tail kernel is replaced by the moving
branch-wall logarithmic envelope with the pure exponential weight still
present.  The remaining scalar theorem is therefore the weighted envelope
estimate itself, not a fixed `w.re` logarithmic window bound. -/
theorem Complex.binetSecondFormula_boundedWindow_decay_of_weightedFullLogEnvelope_decay
    (hweighted :
      ∃ Cweighted : ℝ,
        0 < Cweighted ∧
        ∀ w : ℂ,
          0 < w.re →
          2 ≤ ‖w‖ →
            2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
                (2 *
                  (max |Real.log (w.re / (3 * ‖w‖))|
                    |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| +
                    Real.pi)) /
                  Real.exp ((2 : ℝ) * Real.pi * t) ≤
              (Cweighted / ‖w‖) *
                Complex.binetSecondFormulaDecayingTailIntegral w) :
    ∃ Cbounded : ℝ,
      0 < Cbounded ∧
      ∀ w : ℂ,
        0 < w.re →
        2 ≤ ‖w‖ →
          2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
              ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤
            (Cbounded / ‖w‖) *
              Complex.binetSecondFormulaDecayingTailIntegral w := by
  match hweighted with
  | ⟨Cweighted, hCweighted_pos, hweighted_estimate⟩ =>
      exact
        ⟨Cweighted, hCweighted_pos,
          fun w hw_re_pos hw_norm_two =>
            let P : ℝ → ℝ := fun t : ℝ =>
              ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖
            let G : ℝ → ℝ := fun t : ℝ =>
              (2 *
                (max |Real.log (w.re / (3 * ‖w‖))|
                  |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| +
                  Real.pi)) /
                Real.exp ((2 : ℝ) * Real.pi * t)
            let J : ℝ :=
              Complex.binetSecondFormulaDecayingTailIntegral w
            have hkernel_to_weighted :
                ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖), P t ≤
                  ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖), G t :=
              Complex.binetSecondFormula_principalTailKernel_integral_le_expWeighted_fullLogEnvelope_boundedTailWindow_Ioc
                (w := w) hw_re_pos hw_norm_two
            have htwice :
                2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖), P t ≤
                  2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖), G t :=
              mul_le_mul_of_nonneg_left hkernel_to_weighted zero_le_two
            have hweighted_w :
                2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖), G t ≤
                  (Cweighted / ‖w‖) * J :=
              hweighted_estimate w hw_re_pos hw_norm_two
            le_trans htwice hweighted_w⟩

/-- Assembly from the sharp bounded-window branch-wall estimate to the
legacy full principal-tail cancellation predicate.

The far part of the split tail is already owned by
`binetSecondFormula_principalTailKernel_integral_far_scaled_decay`.  Thus the
only analytic input to this assembly is the bounded window
`Ioc (‖w‖ / 2) (2‖w‖)`, with the moving branch-wall exponential weight kept
before any fixed `w.re`-window replacement. -/
theorem Complex.binetSecondFormula_branchWallPrincipalTailCancellation_of_boundedWindow_decay
    (hbounded :
      ∃ Cbounded : ℝ,
        0 < Cbounded ∧
        ∀ w : ℂ,
          0 < w.re →
          2 ≤ ‖w‖ →
            2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
                ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤
              (Cbounded / ‖w‖) *
                Complex.binetSecondFormulaDecayingTailIntegral w) :
    Complex.BinetSecondFormulaBranchWallPrincipalTailCancellation := by
  match hbounded with
  | ⟨Cbounded, hCbounded_pos, hbounded_estimate⟩ =>
      match Complex.binetSecondFormula_principalTailKernel_integral_far_scaled_decay with
      | ⟨Cfar, hCfar_nonneg, hfar_estimate⟩ =>
          let C : ℝ := Cbounded + Cfar
          have hC_pos : 0 < C :=
            add_pos_of_pos_of_nonneg hCbounded_pos hCfar_nonneg
          exact
            ⟨C, hC_pos,
              fun w hw_re_pos hw_norm_two =>
                let P : ℝ → ℝ := fun t : ℝ =>
                  ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖
                let J : ℝ :=
                  Complex.binetSecondFormulaDecayingTailIntegral w
                have hsplit :
                    ∫ t : ℝ in Set.Ioi (‖w‖ / 2), P t ≤
                      (∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖), P t) +
                        (∫ t : ℝ in Set.Ioi (2 * ‖w‖), P t) :=
                  Complex.binetSecondFormula_principalTailKernel_integral_le_boundedWindow_add_far
                    (w := w) hw_re_pos
                have htwice_split :
                    2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2), P t ≤
                      2 *
                        ((∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖), P t) +
                          (∫ t : ℝ in Set.Ioi (2 * ‖w‖), P t)) :=
                  mul_le_mul_of_nonneg_left hsplit zero_le_two
                have hdistribute :
                    2 *
                        ((∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖), P t) +
                          (∫ t : ℝ in Set.Ioi (2 * ‖w‖), P t)) =
                      2 * (∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖), P t) +
                        2 * (∫ t : ℝ in Set.Ioi (2 * ‖w‖), P t) :=
                  left_distrib (2 : ℝ)
                    (∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖), P t)
                    (∫ t : ℝ in Set.Ioi (2 * ‖w‖), P t)
                have hbounded_w :
                    2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖), P t ≤
                      (Cbounded / ‖w‖) * J :=
                  hbounded_estimate w hw_re_pos hw_norm_two
                have hnorm_one : 1 ≤ ‖w‖ :=
                  le_trans one_le_two hw_norm_two
                have hfar_w :
                    2 * ∫ t : ℝ in Set.Ioi (2 * ‖w‖), P t ≤
                      (Cfar / ‖w‖) * J :=
                  hfar_estimate w hw_re_pos hnorm_one
                have hsum :
                    2 * (∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖), P t) +
                        2 * (∫ t : ℝ in Set.Ioi (2 * ‖w‖), P t) ≤
                      (Cbounded / ‖w‖) * J + (Cfar / ‖w‖) * J :=
                  add_le_add hbounded_w hfar_w
                have hcombine :
                    (Cbounded / ‖w‖) * J + (Cfar / ‖w‖) * J =
                      (C / ‖w‖) * J := by
                  calc
                    (Cbounded / ‖w‖) * J + (Cfar / ‖w‖) * J =
                        (Cbounded / ‖w‖ + Cfar / ‖w‖) * J := by
                      exact (add_mul (Cbounded / ‖w‖) (Cfar / ‖w‖) J).symm
                    _ = ((Cbounded + Cfar) / ‖w‖) * J := by
                      exact congrArg (fun x : ℝ => x * J)
                        (add_div Cbounded Cfar ‖w‖).symm
                    _ = (C / ‖w‖) * J := by
                      rfl
                have hraw :
                    2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2), P t ≤
                      (C / ‖w‖) * J :=
                  le_trans htwice_split
                    (le_trans
                      (Eq.subst
                        (motive := fun x : ℝ =>
                          x ≤
                            (Cbounded / ‖w‖) * J +
                              (Cfar / ‖w‖) * J)
                        hdistribute.symm
                        hsum)
                      (le_of_eq hcombine))
                hraw⟩

/-- Paired Abel-Plana finite-height contour-error cancellation.

This is the precise contour-side cancellation theorem already supplied by the
finite-height Abel-Plana side assembly and horizontal-edge decay: once the two
principal-value boundary faces have been assembled into a genuine finite-height
bridge package, the residual contour error tends to zero.  This theorem is
deliberately stated before any norm is taken; the branch-wall tail theorem
below must consume this cancellation level, not the legacy raw principal-tail
norm estimate. -/
theorem Complex.binetSecondFormula_pairedAbelPlana_finiteHeightContourError_tendsto_zero_owner
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (N : ℕ)
    (hdecInteriorPole : ∀ n : ℕ, n ∈ Finset.range N →
      ∀ z : ℂ, Decidable (z = ((n + 1 : ℕ) : ℂ)))
    (hbridges : Complex.FiniteHeightPVBridgePackageAt N w) :
    Tendsto
      (fun T : ℝ =>
        Complex.finiteAbelPlanaLogFiniteHeightContourError N w T)
      atTop
      (𝓝 (0 : ℂ)) := by
  exact
    Complex.finiteAbelPlana_log_finiteHeightContourError_tendsto_zero_owner
      hw_re_pos N hdecInteriorPole hbridges

/-- Owner-level endpoint-restored finite-height contour-error cancellation.

This is the corrected contour-error object for the endpoint-restored
finite-height bridge package: subtract the endpoint indentation first, then
the remaining error is only the vanishing horizontal edge contribution. -/
theorem Complex.binetSecondFormula_pairedAbelPlana_finiteHeightEndpointRestoredContourError_tendsto_zero_owner
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (N : ℕ)
    (hdecInteriorPole : ∀ n : ℕ, n ∈ Finset.range N →
      ∀ z : ℂ, Decidable (z = ((n + 1 : ℕ) : ℂ)))
    (hbridges : Complex.FiniteHeightPVBridgePackageAtEndpointRestored N w) :
    Tendsto
      (fun T : ℝ =>
        Complex.finiteAbelPlanaLogFiniteHeightEndpointRestoredContourError N w T)
      atTop
      (𝓝 (0 : ℂ)) := by
  exact
    Complex.finiteAbelPlana_log_finiteHeightEndpointRestoredContourError_tendsto_zero_owner
      hw_re_pos N hdecInteriorPole hbridges

/-- A complex-valued family tending to zero is eventually bounded by any
positive real threshold. -/
theorem Complex.eventually_norm_le_of_tendsto_zero
    {ι : Type*}
    {l : Filter ι}
    {f : ι → ℂ}
    {B : ℝ}
    (hf : Tendsto f l (𝓝 (0 : ℂ)))
    (hB_pos : 0 < B) :
    ∀ᶠ i in l, ‖f i‖ ≤ B := by
  have hnorm :
      Tendsto
        (fun i : ι => ‖f i‖)
        l
        (𝓝 (0 : ℝ)) := by
    have hnorm_to_norm_zero :
        Tendsto
          (fun i : ι => ‖f i‖)
          l
          (𝓝 ‖(0 : ℂ)‖) :=
      (continuous_norm.tendsto (0 : ℂ)).comp hf
    have hnorm_zero :
        ‖(0 : ℂ)‖ = (0 : ℝ) :=
      norm_zero
    exact
      Eq.subst
        (motive := fun x : ℝ =>
          Tendsto
            (fun i : ι => ‖f i‖)
            l
            (𝓝 x))
        hnorm_zero
        hnorm_to_norm_zero
  have hsmall :
      ∀ᶠ i in l, ‖f i‖ ∈ Set.Iio B :=
    hnorm (Iio_mem_nhds hB_pos)
  exact hsmall.mono
    (fun i hi => le_of_lt hi)

/-- Quantitative finite-height contour-error absorption into the Binet
decaying tail, for a fixed `w` and finite Abel-Plana height index.

The analytic input is only the paired contour-error cancellation
`finiteHeightContourError → 0`; the positive comparison scale comes from the
proved exponential lower bound for the scalar Binet tail integral. -/
theorem Complex.binetSecondFormula_finiteHeightContourError_eventually_scaled_decayingTail_owner
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hw_norm_two : 2 ≤ ‖w‖)
    (N : ℕ)
    (hdecInteriorPole : ∀ n : ℕ, n ∈ Finset.range N →
      ∀ z : ℂ, Decidable (z = ((n + 1 : ℕ) : ℂ)))
    (hbridges : Complex.FiniteHeightPVBridgePackageAt N w)
    {C : ℝ}
    (hC_pos : 0 < C) :
    ∀ᶠ T : ℝ in atTop,
      ‖Complex.finiteAbelPlanaLogFiniteHeightContourError N w T‖ ≤
        (C / ‖w‖) *
          Complex.binetSecondFormulaDecayingTailIntegral w := by
  match Complex.binetSecondFormula_decayingTailIntegral_expLower_owner with
  | ⟨c, hc_pos, htail_lower⟩ =>
      let J : ℝ := Complex.binetSecondFormulaDecayingTailIntegral w
      let B : ℝ := (C / ‖w‖) * J
      have hnorm_pos : 0 < ‖w‖ :=
        lt_of_lt_of_le zero_lt_two hw_norm_two
      have hcoeff_pos : 0 < C / ‖w‖ :=
        div_pos hC_pos hnorm_pos
      have hE_pos : 0 < ‖w‖ * Real.exp (-Real.pi * ‖w‖) :=
        mul_pos hnorm_pos (Real.exp_pos (-Real.pi * ‖w‖))
      have hcE_pos : 0 < c * (‖w‖ * Real.exp (-Real.pi * ‖w‖)) :=
        mul_pos hc_pos hE_pos
      have hJ_pos : 0 < J :=
        lt_of_lt_of_le hcE_pos (htail_lower w hw_norm_two)
      have hB_pos : 0 < B :=
        mul_pos hcoeff_pos hJ_pos
      have htendsto :
          Tendsto
            (fun T : ℝ =>
              Complex.finiteAbelPlanaLogFiniteHeightContourError N w T)
            atTop
            (𝓝 (0 : ℂ)) :=
        Complex.binetSecondFormula_pairedAbelPlana_finiteHeightContourError_tendsto_zero_owner
          hw_re_pos N hdecInteriorPole hbridges
      exact
        Complex.eventually_norm_le_of_tendsto_zero
          htendsto
          hB_pos

/-- Quantitative endpoint-restored finite-height contour-error absorption into
the Binet decaying tail.

This is the non-circular replacement for trying to consume the endpoint-free
boundary target from an endpoint-restored bridge: the endpoint indentation is
subtracted before applying horizontal-edge decay. -/
theorem Complex.binetSecondFormula_finiteHeightEndpointRestoredContourError_eventually_scaled_decayingTail_owner
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hw_norm_two : 2 ≤ ‖w‖)
    (N : ℕ)
    (hdecInteriorPole : ∀ n : ℕ, n ∈ Finset.range N →
      ∀ z : ℂ, Decidable (z = ((n + 1 : ℕ) : ℂ)))
    (hbridges : Complex.FiniteHeightPVBridgePackageAtEndpointRestored N w)
    {C : ℝ}
    (hC_pos : 0 < C) :
    ∀ᶠ T : ℝ in atTop,
      ‖Complex.finiteAbelPlanaLogFiniteHeightEndpointRestoredContourError N w T‖ ≤
        (C / ‖w‖) *
          Complex.binetSecondFormulaDecayingTailIntegral w := by
  match Complex.binetSecondFormula_decayingTailIntegral_expLower_owner with
  | ⟨c, hc_pos, htail_lower⟩ =>
      let J : ℝ := Complex.binetSecondFormulaDecayingTailIntegral w
      let B : ℝ := (C / ‖w‖) * J
      have hnorm_pos : 0 < ‖w‖ :=
        lt_of_lt_of_le zero_lt_two hw_norm_two
      have hcoeff_pos : 0 < C / ‖w‖ :=
        div_pos hC_pos hnorm_pos
      have hE_pos : 0 < ‖w‖ * Real.exp (-Real.pi * ‖w‖) :=
        mul_pos hnorm_pos (Real.exp_pos (-Real.pi * ‖w‖))
      have hcE_pos : 0 < c * (‖w‖ * Real.exp (-Real.pi * ‖w‖)) :=
        mul_pos hc_pos hE_pos
      have hJ_pos : 0 < J :=
        lt_of_lt_of_le hcE_pos (htail_lower w hw_norm_two)
      have hB_pos : 0 < B :=
        mul_pos hcoeff_pos hJ_pos
      have htendsto :
          Tendsto
            (fun T : ℝ =>
              Complex.finiteAbelPlanaLogFiniteHeightEndpointRestoredContourError N w T)
            atTop
            (𝓝 (0 : ℂ)) :=
        Complex.binetSecondFormula_pairedAbelPlana_finiteHeightEndpointRestoredContourError_tendsto_zero_owner
          hw_re_pos N hdecInteriorPole hbridges
      exact
        Complex.eventually_norm_le_of_tendsto_zero
          htendsto
          hB_pos

/-- Endpoint-restored contour-error decay from the real-segment
constant-face reconstruction.

This is the canonical finite-height contour-error estimate attached to the
endpoint-restored boundary target.  The endpoint indentation is subtracted
before horizontal-edge decay is applied. -/
theorem Complex.binetSecondFormula_endpointRestoredContourError_decay_of_realSegmentConstantFaces
    (hconstant :
      Complex.BinetSecondFormulaFiniteHeightRealSegmentConstantFaces)
    {Cerror : ℝ}
    (hCerror_pos : 0 < Cerror) :
    ∃ R : ℝ,
      0 < R ∧
      2 ≤ R ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
          ∀ N : ℕ,
            ∀ᶠ T : ℝ in atTop,
              ‖Complex.finiteAbelPlanaLogFiniteHeightEndpointRestoredContourError N w T‖ ≤
                (Cerror / ‖w‖) *
                  Complex.binetSecondFormulaDecayingTailIntegral w := by
  match
    Complex.binetSecondFormula_finiteHeightPVBridgePackageEndpointRestored_of_realSegmentConstantFaces
      hconstant
  with
  | ⟨R, hR_pos, hR_two, hpackage_bound⟩ =>
      exact
        ⟨R, hR_pos, hR_two,
          fun w hw_re_pos hRle N =>
            have hw_norm_two : 2 ≤ ‖w‖ :=
              le_trans hR_two hRle
            have hpackage :
                Complex.FiniteHeightPVBridgePackageAtEndpointRestored N w :=
              hpackage_bound w hw_re_pos hRle N
            have hdecInteriorPole :
                ∀ n : ℕ, n ∈ Finset.range N →
                  ∀ z : ℂ, Decidable (z = ((n + 1 : ℕ) : ℂ)) :=
              fun n _hn z => Classical.decEq z ((n + 1 : ℕ) : ℂ)
            Complex.binetSecondFormula_finiteHeightEndpointRestoredContourError_eventually_scaled_decayingTail_owner
              hw_re_pos hw_norm_two N hdecInteriorPole hpackage hCerror_pos⟩

/-- Owner theorem for the corrected endpoint-restored finite-height contour
input package. -/
theorem Complex.binetSecondFormula_endpointRestoredFiniteHeightContourInputs_owner :
    Complex.BinetSecondFormulaEndpointRestoredFiniteHeightContourInputs := by
  have htarget :
      Complex.BinetSecondFormulaFiniteHeightBoundaryTargetEndpointRestored :=
    Complex.binetSecondFormula_finiteHeightBoundaryTargetEndpointRestored_owner
  have herror :
      ∃ R : ℝ,
        0 < R ∧
        2 ≤ R ∧
        ∀ w : ℂ,
          0 < w.re →
          R ≤ ‖w‖ →
            ∀ N : ℕ,
              ∀ᶠ T : ℝ in atTop,
                ‖Complex.finiteAbelPlanaLogFiniteHeightEndpointRestoredContourError N w T‖ ≤
                  ((1 : ℝ) / ‖w‖) *
                    Complex.binetSecondFormulaDecayingTailIntegral w :=
    Complex.binetSecondFormula_endpointRestoredContourError_decay_of_realSegmentConstantFaces
      Complex.binetSecondFormula_finiteHeightRealSegmentConstantFaces_owner
      zero_lt_one
  exact ⟨htarget, herror⟩

/-- Quantitative contour-error absorption from the owner finite-height
boundary target.

This is the consumption form used by wall-cancellation estimates: once the
finite-height normalized boundary target has been proved, the paired contour
error is eventually smaller than any fixed positive multiple of the scaled
Binet decaying tail. -/
theorem Complex.binetSecondFormula_finiteHeightContourError_eventually_scaled_decayingTail_of_boundaryTarget_owner
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hw_norm_two : 2 ≤ ‖w‖)
    (N : ℕ)
    (hboundary :
      ∀ᶠ T : ℝ in atTop,
        (((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
              (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
                Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) +
            (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) +
          ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
              (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
                Complex.I *
                  Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) +
            (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T))) =
          Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N w T)
    {C : ℝ}
    (hC_pos : 0 < C) :
    ∀ᶠ T : ℝ in atTop,
      ‖Complex.finiteAbelPlanaLogFiniteHeightContourError N w T‖ ≤
        (C / ‖w‖) *
          Complex.binetSecondFormulaDecayingTailIntegral w := by
  have hbridges :
      Complex.FiniteHeightPVBridgePackageAt N w :=
    Complex.finiteAbelPlana_log_finiteHeightPVBridgePackageAt_of_ownerBoundaryTarget_owner
      N hw_re_pos hboundary
  have hdecInteriorPole :
      ∀ n : ℕ, n ∈ Finset.range N →
        ∀ z : ℂ, Decidable (z = ((n + 1 : ℕ) : ℂ)) :=
    fun n _hn z => Classical.decEq z ((n + 1 : ℕ) : ℂ)
  exact
    Complex.binetSecondFormula_finiteHeightContourError_eventually_scaled_decayingTail_owner
      hw_re_pos hw_norm_two N hdecInteriorPole hbridges hC_pos

/-- Owner-level bridge from the lower Abel-Plana vertical tail to the Binet
tail remainder.

This is the exact logarithmic-jump-to-arctangent transport over the Binet split
tail.  It is deliberately stated at the owner layer because the branch-wall
cancellation theorem must cancel contour-level vertical contributions before
taking the final tail norm. -/
theorem Complex.binetSecondFormula_lowerVerticalTailIntegral_eq_tailRemainder_owner
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
        Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t =
      Complex.binetSecondFormulaTailRemainder w := by
  exact
    Complex.finiteAbelPlana_lowerVerticalTailIntegral_eq_binetTailRemainder
      hw_re_pos

/-- Owner-level split of the lower Abel-Plana vertical full integral at the
Binet tail cutoff.

The bounded initial window and the Binet tail remainder are the two pieces that
must be paired with the finite-height contour cancellation and the decaying
tail kernel estimate in the branch-wall owner theorem. -/
theorem Complex.binetSecondFormula_lowerVerticalFullIntegral_eq_initialWindow_add_tailRemainder_owner
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w =
      (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
        Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t) +
        Complex.binetSecondFormulaTailRemainder w := by
  exact
    Complex.finiteAbelPlana_lowerVerticalFullIntegral_eq_initialWindow_add_binetTailRemainder
      hw_re_pos

/-- Owner-level difference form of the lower vertical split.

This is the branch-wall cancellation surface: after the bounded initial
vertical window is paired with the contour contribution, the remaining
difference is exactly the Binet tail remainder. -/
theorem Complex.binetSecondFormula_tailRemainder_eq_lowerVerticalFullIntegral_sub_initialWindow_owner
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    Complex.binetSecondFormulaTailRemainder w =
      Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t) := by
  exact
    Complex.binetSecondFormulaTailRemainder_eq_lowerVerticalFullIntegral_sub_initialWindow
      hw_re_pos

/-- Owner-level norm form of the lower vertical split. -/
theorem Complex.binetSecondFormula_tailRemainder_norm_eq_lowerVerticalFullIntegral_sub_initialWindow_norm_owner
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ‖Complex.binetSecondFormulaTailRemainder w‖ =
      ‖Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ := by
  exact
    Complex.binetSecondFormulaTailRemainder_norm_eq_lowerVerticalFullIntegral_sub_initialWindow_norm
      hw_re_pos

/-- Owner-level finite-height convergence of the lower vertical tail at the
Binet cutoff.

This places the actual tail remainder on the same finite-height parameter as
the paired Abel-Plana contour-error cancellation theorem. -/
theorem Complex.binetSecondFormula_lowerVerticalUpTo_sub_initialWindow_tendsto_tailRemainder_owner
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    Tendsto
      (fun T : ℝ =>
        Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
          (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
            Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t))
      atTop
      (𝓝 (Complex.binetSecondFormulaTailRemainder w)) := by
  exact
    Complex.finiteAbelPlana_lowerVerticalUpTo_sub_initialWindow_tendsto_binetTailRemainder
      hw_re_pos

/-- Owner-level closure step from finite-height lower-tail bounds to the Binet
tail remainder. -/
theorem Complex.binetSecondFormula_tailRemainder_norm_le_of_eventually_lowerVerticalUpTo_sub_initialWindow_norm_le_owner
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    {B : ℝ}
    (hbound :
      ∀ᶠ T : ℝ in atTop,
        ‖Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
          (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
            Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤ B) :
    ‖Complex.binetSecondFormulaTailRemainder w‖ ≤ B := by
  exact
    Complex.binetSecondFormulaTailRemainder_norm_le_of_eventually_lowerVerticalUpTo_sub_initialWindow_norm_le
      hw_re_pos hbound

/-- Owner-level solved form of the finite-height Abel-Plana boundary equation
for the lower vertical tail at the Binet cutoff.

This is the algebraic point where the paired contour error enters the
finite-height lower-tail expression with its forced sign. -/
theorem Complex.binetSecondFormula_lowerVerticalUpTo_sub_initialWindow_eq_boundarySolved_owner
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t) =
      ((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
        Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
        Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w -
        Complex.finiteAbelPlanaLogFiniteHeightContourError N w T) -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t) := by
  exact
    Complex.finiteAbelPlana_lowerVerticalUpTo_sub_initialWindow_eq_boundarySolved
      N w T

/-- Owner-level restored-error solved form of the finite-height Abel-Plana
boundary equation for the lower vertical tail at the Binet cutoff. -/
theorem Complex.binetSecondFormula_lowerVerticalUpTo_sub_initialWindow_eq_boundarySolved_endpointRestored_owner
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t) =
      ((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) -
        Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w -
        Complex.finiteAbelPlanaLogFiniteHeightEndpointRestoredContourError N w T) -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t) := by
  exact
    Complex.finiteAbelPlana_lowerVerticalUpTo_sub_initialWindow_eq_boundarySolved_endpointRestored
      N w T

/-- Owner-level triangle estimate from the solved finite-height boundary
equation.  The finite-height lower-tail norm is controlled by the non-error
solved boundary part plus the paired contour-error norm. -/
theorem Complex.binetSecondFormula_lowerVerticalUpTo_sub_initialWindow_norm_le_boundarySolvedStatic_add_contourError_owner
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    ‖Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
      ‖((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
        Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
        Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ +
        ‖Complex.finiteAbelPlanaLogFiniteHeightContourError N w T‖ := by
  exact
    Complex.finiteAbelPlana_lowerVerticalUpTo_sub_initialWindow_norm_le_boundarySolvedStatic_add_contourError
      N w T

/-- Owner-level triangle estimate from the restored-error solved finite-height
boundary equation. -/
theorem Complex.binetSecondFormula_lowerVerticalUpTo_sub_initialWindow_norm_le_boundarySolvedStatic_add_endpointRestoredContourError_owner
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    ‖Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
      ‖((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) -
        Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ +
        ‖Complex.finiteAbelPlanaLogFiniteHeightEndpointRestoredContourError N w T‖ := by
  exact
    Complex.finiteAbelPlana_lowerVerticalUpTo_sub_initialWindow_norm_le_boundarySolvedStatic_add_endpointRestoredContourError
      N w T

/-- Owner-level endpoint-returned restored-pair equation for the finite-height
lower vertical difference.

This is the algebraic replacement for estimating the endpoint-restored static
piece and the endpoint-restored error separately.  The half-endpoint term is
returned to both sides of the paired difference, where it cancels before the
norm is taken. -/
theorem Complex.binetSecondFormula_lowerVerticalUpTo_sub_initialWindow_eq_endpointReturnedRestoredPair_owner
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t) =
      ((((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) -
        Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)) +
        Complex.finiteAbelPlanaLogSummandHalfEndpoints N w) -
        (Complex.finiteAbelPlanaLogFiniteHeightEndpointRestoredContourError N w T +
          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w) := by
  exact
    Complex.finiteAbelPlana_lowerVerticalUpTo_sub_initialWindow_eq_endpointReturnedRestoredPair
      N w T

/-- Owner-level norm form of the endpoint-returned restored-pair equation. -/
theorem Complex.binetSecondFormula_lowerVerticalUpTo_sub_initialWindow_norm_eq_endpointReturnedRestoredPair_norm_owner
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    ‖Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ =
      ‖(((((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) -
        Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)) +
        Complex.finiteAbelPlanaLogSummandHalfEndpoints N w) -
        (Complex.finiteAbelPlanaLogFiniteHeightEndpointRestoredContourError N w T +
          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w))‖ := by
  exact
    Complex.finiteAbelPlana_lowerVerticalUpTo_sub_initialWindow_norm_eq_endpointReturnedRestoredPair_norm
      N w T

/-- Limit of the solved finite-height boundary expression with the contour
error removed.

After solving the finite-height Abel-Plana boundary equation for the lower
vertical side, the non-error part has only one `T`-dependent term: the upper
vertical integral.  This lemma records its exact improper-limit target. -/
theorem Complex.binetSecondFormula_boundarySolvedStatic_sub_initialWindow_tendsto_full_owner
    (N : ℕ)
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    Tendsto
      (fun T : ℝ =>
        (((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
            Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
          Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
          Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
          (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
            Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t))
      atTop
      (𝓝
        ((((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
            Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
          Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w -
          Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
          (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
            Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t))) := by
  let R : ℂ :=
    ∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
      Complex.finiteAbelPlanaLogSummand w (x : ℂ)
  let H : ℂ := Complex.finiteAbelPlanaLogSummandHalfEndpoints N w
  let P : ℂ := Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w
  let I : ℂ :=
    ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
      Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t
  let U : ℝ → ℂ := fun T : ℝ =>
    Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T
  let U∞ : ℂ := Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w
  have hU : Tendsto U atTop (𝓝 U∞) :=
    Complex.finiteAbelPlana_log_upperVerticalIntegralUpTo_tendsto_unsplitFull
      hw_re_pos N
  have hfirst :
      Tendsto
        (fun T : ℝ => (R + H) - U T)
        atTop
        (𝓝 ((R + H) - U∞)) :=
    tendsto_const_nhds.sub hU
  have hminusP :
      Tendsto
        (fun T : ℝ => (R + H) - U T - P)
        atTop
        (𝓝 ((R + H) - U∞ - P)) :=
    hfirst.sub tendsto_const_nhds
  have hminusI :
      Tendsto
        (fun T : ℝ => ((R + H) - U T - P) - I)
        atTop
        (𝓝 (((R + H) - U∞ - P) - I)) :=
    hminusP.sub tendsto_const_nhds
  exact hminusI

/-- Limit of the endpoint-restored solved finite-height boundary expression.

This is the same upper-vertical improper-limit transport as the ordinary
solved-static expression, but for the normalization in which the explicit
half-endpoint term has been absorbed into the restored contour error. -/
theorem Complex.binetSecondFormula_boundarySolvedStatic_endpointRestored_sub_initialWindow_tendsto_full_owner
    (N : ℕ)
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    Tendsto
      (fun T : ℝ =>
        (((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
            Complex.finiteAbelPlanaLogSummand w (x : ℂ)) -
          Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
          Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
          (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
            Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t))
      atTop
      (𝓝
        ((((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
            Complex.finiteAbelPlanaLogSummand w (x : ℂ)) -
          Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w -
          Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
          (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
            Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t))) := by
  let R : ℂ :=
    ∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
      Complex.finiteAbelPlanaLogSummand w (x : ℂ)
  let P : ℂ := Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w
  let I : ℂ :=
    ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
      Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t
  let U : ℝ → ℂ := fun T : ℝ =>
    Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T
  let U∞ : ℂ := Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w
  have hU : Tendsto U atTop (𝓝 U∞) :=
    Complex.finiteAbelPlana_log_upperVerticalIntegralUpTo_tendsto_unsplitFull
      hw_re_pos N
  have hfirst :
      Tendsto
        (fun T : ℝ => R - U T)
        atTop
        (𝓝 (R - U∞)) :=
    tendsto_const_nhds.sub hU
  have hminusP :
      Tendsto
        (fun T : ℝ => R - U T - P)
        atTop
        (𝓝 (R - U∞ - P)) :=
    hfirst.sub tendsto_const_nhds
  have hminusI :
      Tendsto
        (fun T : ℝ => (R - U T - P) - I)
        atTop
        (𝓝 ((R - U∞ - P) - I)) :=
    hminusP.sub tendsto_const_nhds
  exact hminusI

/-- Principal-value cancellation of the full solved static boundary expression.

After the upper vertical finite-height side has been sent to its improper
limit, the finite Abel-Plana principal-value identity cancels the real segment,
endpoint, upper vertical, and residue terms.  What remains is exactly the full
lower vertical side, with the fixed Binet initial window still subtracted. -/
theorem Complex.binetSecondFormula_boundarySolvedStatic_full_sub_initialWindow_eq_lowerVerticalFull_sub_initialWindow_owner
    (N : ℕ)
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hbridges : Complex.FiniteHeightPVBridgePackage w)
    (hdecInteriorPole : ∀ n : ℕ, n ∈ Finset.range N →
      ∀ z : ℂ, Decidable (z = ((n + 1 : ℕ) : ℂ))) :
    (((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
        Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
      Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
      Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w -
      Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
      (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
        Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)) =
      Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t) := by
  let R : ℂ :=
    ∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
      Complex.finiteAbelPlanaLogSummand w (x : ℂ)
  let H : ℂ := Complex.finiteAbelPlanaLogSummandHalfEndpoints N w
  let L : ℂ := Complex.finiteAbelPlanaLogSummandLowerVerticalIntegral N w
  let U : ℂ := Complex.finiteAbelPlanaLogSummandUpperVerticalIntegral N w
  let U∞ : ℂ := Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w
  let P : ℂ := Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w
  let F : ℂ := Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w
  let I : ℂ :=
    ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
      Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t
  have hboundary_named :
      Complex.finiteAbelPlanaLogBoundaryNamedPieces N w =
        R + H - L - U := by
    exact
      Complex.finiteAbelPlana_log_boundaryNamedPieces_unfold N w
  have hboundary_residue :
      Complex.finiteAbelPlanaLogBoundaryNamedPieces N w = P :=
    Complex.finiteAbelPlana_log_principalValueCotangentFormula
      hw_re_pos hbridges N hdecInteriorPole
  have hnamed_residue :
      R + H - L - U = P := by
    exact Eq.trans hboundary_named.symm hboundary_residue
  have hupper :
      U∞ = U :=
    Complex.finiteAbelPlana_log_upperVerticalFullIntegral_eq_named N w
  have hlower :
      F = L :=
    Complex.finiteAbelPlana_log_lowerVerticalFullIntegral_eq_split
      hw_re_pos N
  have hsolve_named :
      R + H - U - P = L := by
    let A : ℂ := R + H - U
    have hreorder :
        R + H - L - U = A - L := by
      calc
        R + H - L - U = (R + H) - L - U := by
          rfl
        _ = (R + H) - U - L := by
          exact sub_right_comm (R + H) L U
        _ = A - L := by
          rfl
    have hA_sub_L : A - L = P :=
      Eq.trans hreorder.symm hnamed_residue
    have hcancel :
        A - P = L := by
      calc
        A - P = A - (A - L) := by
          exact congrArg (fun z : ℂ => A - z) hA_sub_L.symm
        _ = L := by
          exact sub_sub_self A L
    exact hcancel
  have hleft_named :
      (R + H - U∞ - P) - I = L - I := by
    have hreplace_upper :
        R + H - U∞ - P = R + H - U - P := by
      exact congrArg (fun z : ℂ => R + H - z - P) hupper
    calc
      (R + H - U∞ - P) - I =
          (R + H - U - P) - I := by
        exact congrArg (fun z : ℂ => z - I) hreplace_upper
      _ = L - I := by
        exact congrArg (fun z : ℂ => z - I) hsolve_named
  have hright_named :
      L - I = F - I := by
    exact congrArg (fun z : ℂ => z - I) hlower.symm
  calc
    (((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
        Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
      Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
      Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w -
      Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
      (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
        Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)) =
        (R + H - U∞ - P) - I := by
      rfl
    _ = L - I :=
      hleft_named
    _ = F - I :=
      hright_named
    _ =
      Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t) := by
      rfl

/-- Endpoint-restored static normalization at full height.

If the explicit Abel-Plana half-endpoints are removed from the solved static
expression, the full-height principal-value cancellation leaves the Binet
lower tail with those same half-endpoints subtracted.  This is the algebraic
normalization comparison between the restored finite-height contour error and
the older static expression that still contains the half-endpoint term. -/
theorem Complex.binetSecondFormula_boundarySolvedStatic_endpointRestored_full_sub_initialWindow_eq_lowerVerticalFull_sub_initialWindow_sub_halfEndpoints_owner
    (N : ℕ)
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hbridges : Complex.FiniteHeightPVBridgePackage w)
    (hdecInteriorPole : ∀ n : ℕ, n ∈ Finset.range N →
      ∀ z : ℂ, Decidable (z = ((n + 1 : ℕ) : ℂ))) :
    (((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
        Complex.finiteAbelPlanaLogSummand w (x : ℂ)) -
      Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w -
      Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
      (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
        Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)) =
      (Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)) -
        Complex.finiteAbelPlanaLogSummandHalfEndpoints N w := by
  let R : ℂ :=
    ∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
      Complex.finiteAbelPlanaLogSummand w (x : ℂ)
  let H : ℂ := Complex.finiteAbelPlanaLogSummandHalfEndpoints N w
  let U∞ : ℂ := Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w
  let P : ℂ := Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w
  let F : ℂ := Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w
  let I : ℂ :=
    ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
      Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t
  let A : ℂ := R - U∞ - P
  let Y : ℂ := F - I
  have hwith_endpoint :
      ((R + H - U∞ - P) - I) = Y := by
    calc
      ((R + H - U∞ - P) - I) =
          (((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
              Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
            Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
            Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w -
            Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
            (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
              Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)) := by
        rfl
      _ =
          Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w -
            (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
              Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t) :=
        Complex.binetSecondFormula_boundarySolvedStatic_full_sub_initialWindow_eq_lowerVerticalFull_sub_initialWindow_owner
          N hw_re_pos hbridges hdecInteriorPole
      _ = Y := by
        rfl
  have hwith_endpoint_as_A :
      ((R + H - U∞ - P) - I) = (A + H) - I := by
    calc
      ((R + H - U∞ - P) - I) =
          (R - U∞ - P) + H - I := by
        exact Complex.endpoint_middle_static_subtractions R H U∞ P I
      _ = (A + H) - I := by
        rfl
  have hA_sub_I_eq_with_endpoint_sub_H :
      A - I = ((R + H - U∞ - P) - I) - H := by
    calc
      A - I = (A - I + H) - H := by
        exact (add_sub_cancel_right (A - I) H).symm
      _ = ((A + H) - I) - H := by
        exact congrArg (fun z : ℂ => z - H)
          (Complex.add_middle_sub_right A H I).symm
      _ = ((R + H - U∞ - P) - I) - H := by
        exact congrArg (fun z : ℂ => z - H) hwith_endpoint_as_A.symm
  calc
    (((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
        Complex.finiteAbelPlanaLogSummand w (x : ℂ)) -
      Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w -
      Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
      (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
        Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)) =
        A - I := by
      rfl
    _ = ((R + H - U∞ - P) - I) - H :=
      hA_sub_I_eq_with_endpoint_sub_H
    _ = Y - H := by
      exact congrArg (fun z : ℂ => z - H) hwith_endpoint
    _ =
      (Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)) -
        Complex.finiteAbelPlanaLogSummandHalfEndpoints N w := by
      rfl

/-- Tail-remainder form of the endpoint-restored static normalization.

The restored finite-height contour error cancels the half-endpoint
indentation at the finite-height level.  Consequently, the corresponding
full-height static expression is the public Binet tail remainder with the
finite half-endpoints subtracted, not the public tail remainder itself. -/
theorem Complex.binetSecondFormula_boundarySolvedStatic_endpointRestored_full_sub_initialWindow_eq_tailRemainder_sub_halfEndpoints_owner
    (N : ℕ)
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hbridges : Complex.FiniteHeightPVBridgePackage w)
    (hdecInteriorPole : ∀ n : ℕ, n ∈ Finset.range N →
      ∀ z : ℂ, Decidable (z = ((n + 1 : ℕ) : ℂ))) :
    (((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
        Complex.finiteAbelPlanaLogSummand w (x : ℂ)) -
      Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w -
      Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
      (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
        Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)) =
      Complex.binetSecondFormulaTailRemainder w -
        Complex.finiteAbelPlanaLogSummandHalfEndpoints N w := by
  have hstatic_lower :
      (((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) -
        Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w -
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)) =
        (Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w -
          (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
            Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)) -
          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w :=
    Complex.binetSecondFormula_boundarySolvedStatic_endpointRestored_full_sub_initialWindow_eq_lowerVerticalFull_sub_initialWindow_sub_halfEndpoints_owner
      N hw_re_pos hbridges hdecInteriorPole
  have htail :
      Complex.binetSecondFormulaTailRemainder w =
        Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w -
          (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
            Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t) :=
    Complex.binetSecondFormula_tailRemainder_eq_lowerVerticalFullIntegral_sub_initialWindow_owner
      hw_re_pos
  calc
    (((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
        Complex.finiteAbelPlanaLogSummand w (x : ℂ)) -
      Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w -
      Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
      (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
        Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)) =
        (Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w -
          (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
            Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)) -
          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w :=
      hstatic_lower
    _ =
        Complex.binetSecondFormulaTailRemainder w -
          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w := by
      exact congrArg
        (fun z : ℂ => z - Complex.finiteAbelPlanaLogSummandHalfEndpoints N w)
        htail.symm

/-- Endpoint-restored full static normalization with the endpoint term
returned.

The restored static expression alone has limit `tailRemainder - halfEndpoints`.
The public Binet tail is recovered only after the same half-endpoint term is
put back.  This is the canonical algebraic form for any later paired
cancellation argument: the endpoint term cannot be discarded or estimated
separately as a vanishing contour error. -/
theorem Complex.binetSecondFormula_boundarySolvedStatic_endpointRestored_full_sub_initialWindow_add_halfEndpoints_eq_tailRemainder_owner
    (N : ℕ)
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hbridges : Complex.FiniteHeightPVBridgePackage w)
    (hdecInteriorPole : ∀ n : ℕ, n ∈ Finset.range N →
      ∀ z : ℂ, Decidable (z = ((n + 1 : ℕ) : ℂ))) :
    ((((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
        Complex.finiteAbelPlanaLogSummand w (x : ℂ)) -
      Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w -
      Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
      (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
        Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)) +
      Complex.finiteAbelPlanaLogSummandHalfEndpoints N w =
      Complex.binetSecondFormulaTailRemainder w := by
  let S : ℂ :=
    (((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
        Complex.finiteAbelPlanaLogSummand w (x : ℂ)) -
      Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w -
      Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
      (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
        Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t))
  let H : ℂ := Complex.finiteAbelPlanaLogSummandHalfEndpoints N w
  let T : ℂ := Complex.binetSecondFormulaTailRemainder w
  have hrestored :
      S = T - H :=
    Complex.binetSecondFormula_boundarySolvedStatic_endpointRestored_full_sub_initialWindow_eq_tailRemainder_sub_halfEndpoints_owner
      N hw_re_pos hbridges hdecInteriorPole
  have hreturn :
      S + H = T := by
    calc
      S + H = (T - H) + H := by
        exact congrArg (fun z : ℂ => z + H) hrestored
      _ = T := by
        exact sub_add_cancel T H
  exact hreturn

/-- Norm form of the endpoint-restored full static normalization after
returning the endpoint term. -/
theorem Complex.binetSecondFormula_boundarySolvedStatic_endpointRestored_full_sub_initialWindow_add_halfEndpoints_norm_eq_tailRemainder_norm_owner
    (N : ℕ)
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hbridges : Complex.FiniteHeightPVBridgePackage w)
    (hdecInteriorPole : ∀ n : ℕ, n ∈ Finset.range N →
      ∀ z : ℂ, Decidable (z = ((n + 1 : ℕ) : ℂ))) :
    ‖(((((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
        Complex.finiteAbelPlanaLogSummand w (x : ℂ)) -
      Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w -
      Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
      (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
        Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)) +
      Complex.finiteAbelPlanaLogSummandHalfEndpoints N w)‖ =
      ‖Complex.binetSecondFormulaTailRemainder w‖ := by
  exact congrArg norm
    (Complex.binetSecondFormula_boundarySolvedStatic_endpointRestored_full_sub_initialWindow_add_halfEndpoints_eq_tailRemainder_owner
      N hw_re_pos hbridges hdecInteriorPole)

/-- Principal-value cancellation identifies the full solved static boundary
expression with the Binet tail remainder. -/
theorem Complex.binetSecondFormula_boundarySolvedStatic_full_sub_initialWindow_eq_tailRemainder_owner
    (N : ℕ)
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hbridges : Complex.FiniteHeightPVBridgePackage w)
    (hdecInteriorPole : ∀ n : ℕ, n ∈ Finset.range N →
      ∀ z : ℂ, Decidable (z = ((n + 1 : ℕ) : ℂ))) :
    (((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
        Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
      Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
      Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w -
      Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
      (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
        Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)) =
      Complex.binetSecondFormulaTailRemainder w := by
  have hstatic_lower :
      (((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
        Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
        Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w -
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)) =
        Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w -
          (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
            Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t) :=
    Complex.binetSecondFormula_boundarySolvedStatic_full_sub_initialWindow_eq_lowerVerticalFull_sub_initialWindow_owner
      N hw_re_pos hbridges hdecInteriorPole
  have htail :
      Complex.binetSecondFormulaTailRemainder w =
        Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w -
          (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
            Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t) :=
    Complex.binetSecondFormula_tailRemainder_eq_lowerVerticalFullIntegral_sub_initialWindow_owner
      hw_re_pos
  exact Eq.trans hstatic_lower htail.symm

/-- Norm form of the principal-value cancellation of the full solved static
boundary expression. -/
theorem Complex.binetSecondFormula_boundarySolvedStatic_full_sub_initialWindow_norm_eq_tailRemainder_norm_owner
    (N : ℕ)
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hbridges : Complex.FiniteHeightPVBridgePackage w)
    (hdecInteriorPole : ∀ n : ℕ, n ∈ Finset.range N →
      ∀ z : ℂ, Decidable (z = ((n + 1 : ℕ) : ℂ))) :
    ‖(((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
        Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
      Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
      Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w -
      Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
      (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
        Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t))‖ =
      ‖Complex.binetSecondFormulaTailRemainder w‖ := by
  exact congrArg norm
    (Complex.binetSecondFormula_boundarySolvedStatic_full_sub_initialWindow_eq_tailRemainder_owner
      N hw_re_pos hbridges hdecInteriorPole)

/-- Eventual norm control from convergence to a limit whose norm is strictly
below the target bound. -/
theorem Complex.eventually_norm_le_of_tendsto_norm_lt
    {ι : Type*}
    {l : Filter ι}
    {f : ι → ℂ}
    {a : ℂ}
    {B : ℝ}
    (hf : Tendsto f l (𝓝 a))
    (haB : ‖a‖ < B) :
    ∀ᶠ i in l, ‖f i‖ ≤ B := by
  have hnorm :
      Tendsto
        (fun i : ι => ‖f i‖)
        l
        (𝓝 ‖a‖) :=
    (continuous_norm.tendsto a).comp hf
  have hsmall :
      ∀ᶠ i in l, ‖f i‖ ∈ Set.Iio B :=
    hnorm (Iio_mem_nhds haB)
  exact hsmall.mono
    (fun i hi => le_of_lt hi)

/-- A positive tail scale gives strict room after doubling the constant. -/
theorem Real.le_mul_pos_scale_lt_two_mul
    {A C S : ℝ}
    (hA : A ≤ C * S)
    (hC_pos : 0 < C)
    (hS_pos : 0 < S) :
    A < (2 * C) * S := by
  have hCS_pos : 0 < C * S :=
    mul_pos hC_pos hS_pos
  have hCS_lt_two :
      C * S < (2 * C) * S := by
    calc
      C * S < C * S + C * S := by
        exact lt_add_of_pos_right (C * S) hCS_pos
      _ = (C + C) * S := by
        exact (add_mul C C S).symm
      _ = (2 * C) * S := by
        exact congrArg (fun x : ℝ => x * S) (two_mul C).symm
  exact lt_of_le_of_lt hA hCS_lt_two

/-- Static solved-boundary decay from a structural boundary target and a
tail-absorption theorem.

The boundary target is used only to build the principal-value bridge package
needed by the full-height static cancellation identity.  The quantitative
decay then follows by sending the upper vertical side to its improper limit
and using the tail-remainder bound with a doubled constant for strict
eventual control. -/
theorem Complex.binetSecondFormula_boundarySolvedStaticDecayEstimate_of_boundaryTarget_and_tailAbsorption
    (hboundary :
      Complex.BinetSecondFormulaFiniteHeightBoundaryTarget)
    (htail :
      Complex.BinetSecondFormulaBranchWallContourCancellationTailAbsorption) :
    Complex.BinetSecondFormulaBoundarySolvedStaticDecayEstimate := by
  match hboundary with
  | ⟨Rboundary, hRboundary_pos, hRboundary_two, hboundary_bound⟩ =>
      match htail with
      | ⟨Rtail, Ctail, hRtail_pos, hCtail_pos, htail_bound⟩ =>
          let R : ℝ := max Rboundary (max Rtail 2)
          let Cstatic : ℝ := 2 * Ctail
          have hR_pos : 0 < R :=
            lt_of_lt_of_le hRboundary_pos (le_max_left Rboundary (max Rtail 2))
          have hR_two : 2 ≤ R := by
            exact le_trans
              (le_max_right Rtail 2)
              (le_trans
                (le_max_right Rboundary (max Rtail 2))
                (le_refl R))
          have hCstatic_pos : 0 < Cstatic :=
            mul_pos two_pos hCtail_pos
          exact
            ⟨R, Cstatic, hR_pos, hR_two, hCstatic_pos,
              fun w hw_re_pos hRle =>
                let N : ℕ := 0
                have hRboundary_le : Rboundary ≤ ‖w‖ :=
                  le_trans (le_max_left Rboundary (max Rtail 2)) hRle
                have hRtail_le : Rtail ≤ ‖w‖ :=
                  le_trans
                    (le_trans
                      (le_max_left Rtail 2)
                      (le_max_right Rboundary (max Rtail 2)))
                    hRle
                have hw_norm_two : 2 ≤ ‖w‖ :=
                  le_trans
                    (le_trans
                      (le_max_right Rtail 2)
                      (le_max_right Rboundary (max Rtail 2)))
                    hRle
                have hboundary_w :
                    ∀ N : ℕ,
                      ∀ᶠ T : ℝ in atTop,
                        (((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                              (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
                                Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) +
                            (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) +
                          ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                              (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
                                Complex.I *
                                  Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) +
                            (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T))) =
                          Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N w T :=
                  hboundary_bound w hw_re_pos hRboundary_le
                have hbridges : Complex.FiniteHeightPVBridgePackage w :=
                  Complex.finiteAbelPlana_log_finiteHeightPVBridgePackage_of_ownerBoundaryTarget_owner
                    hw_re_pos hboundary_w
              have hdecInteriorPole :
                  ∀ n : ℕ, n ∈ Finset.range N →
                    ∀ z : ℂ, Decidable (z = ((n + 1 : ℕ) : ℂ)) :=
                  fun n _hn z => Classical.decEq z ((n + 1 : ℕ) : ℂ)
                have htendsto :
                    Tendsto
                      (fun T : ℝ =>
                        (((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
                            Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
                          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
                          Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
                          Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
                          (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                            Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t))
                      atTop
                      (𝓝
                        ((((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
                            Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
                          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
                          Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w -
                          Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
                          (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                            Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t))) :=
                  Complex.binetSecondFormula_boundarySolvedStatic_sub_initialWindow_tendsto_full_owner
                    N hw_re_pos
                let A : ℂ :=
                  (((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
                      Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
                    Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
                    Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w -
                    Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
                    (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                      Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t))
                let J : ℝ := Complex.binetSecondFormulaDecayingTailIntegral w
                let S : ℝ := (Ctail / ‖w‖) * J
                let B : ℝ := (Cstatic / ‖w‖) * J
                have htail_norm :
                    ‖Complex.binetSecondFormulaTailRemainder w‖ ≤ S :=
                  htail_bound w hw_re_pos hRtail_le
                have hA_norm_eq :
                    ‖A‖ = ‖Complex.binetSecondFormulaTailRemainder w‖ := by
                  exact
                    Complex.binetSecondFormula_boundarySolvedStatic_full_sub_initialWindow_norm_eq_tailRemainder_norm_owner
                      N hw_re_pos hbridges hdecInteriorPole
                have hA_le_S : ‖A‖ ≤ S :=
                  Eq.subst
                    (motive := fun x : ℝ => x ≤ S)
                    hA_norm_eq.symm
                    htail_norm
                have hnorm_pos : 0 < ‖w‖ :=
                  lt_of_lt_of_le zero_lt_two hw_norm_two
                have hcoeff_pos : 0 < Ctail / ‖w‖ :=
                  div_pos hCtail_pos hnorm_pos
                have hJ_pos : 0 < J := by
                  match Complex.binetSecondFormula_decayingTailIntegral_expLower_owner with
                  | ⟨c, hc_pos, htail_lower⟩ =>
                      let E : ℝ := ‖w‖ * Real.exp (-Real.pi * ‖w‖)
                      have hE_pos : 0 < E :=
                        mul_pos hnorm_pos (Real.exp_pos (-Real.pi * ‖w‖))
                      have hcE_pos : 0 < c * E :=
                        mul_pos hc_pos hE_pos
                      exact lt_of_lt_of_le hcE_pos (htail_lower w hw_norm_two)
                have hA_lt_B : ‖A‖ < B := by
                  have hscale_pos : 0 < (1 / ‖w‖) * J :=
                    mul_pos (one_div_pos.mpr hnorm_pos) hJ_pos
                  have hS_eq : S = Ctail * ((1 / ‖w‖) * J) := by
                    calc
                      S = (Ctail / ‖w‖) * J := by
                        rfl
                      _ = (Ctail * (1 / ‖w‖)) * J := by
                        exact congrArg (fun x : ℝ => x * J) (div_eq_mul_one_div Ctail ‖w‖)
                      _ = Ctail * ((1 / ‖w‖) * J) := by
                        exact mul_assoc Ctail (1 / ‖w‖) J
                  have hB_eq : B = (2 * Ctail) * ((1 / ‖w‖) * J) := by
                    calc
                      B = (Cstatic / ‖w‖) * J := by
                        rfl
                      _ = ((2 * Ctail) / ‖w‖) * J := by
                        rfl
                      _ = ((2 * Ctail) * (1 / ‖w‖)) * J := by
                        exact congrArg (fun x : ℝ => x * J)
                          (div_eq_mul_one_div (2 * Ctail) ‖w‖)
                      _ = (2 * Ctail) * ((1 / ‖w‖) * J) := by
                        exact mul_assoc (2 * Ctail) (1 / ‖w‖) J
                  have hA_le_scaled :
                      ‖A‖ ≤ Ctail * ((1 / ‖w‖) * J) :=
                    Eq.subst
                      (motive := fun x : ℝ => ‖A‖ ≤ x)
                      hS_eq
                      hA_le_S
                  have hlt :
                      ‖A‖ < (2 * Ctail) * ((1 / ‖w‖) * J) :=
                    Real.le_mul_pos_scale_lt_two_mul
                      hA_le_scaled hCtail_pos hscale_pos
                  Eq.subst
                    (motive := fun x : ℝ => ‖A‖ < x)
                    hB_eq.symm
                    hlt
                have hevent :
                    ∀ᶠ T : ℝ in atTop,
                      ‖(((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
                          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
                        Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
                        Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
                        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
                        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
                        B :=
                  Complex.eventually_norm_le_of_tendsto_norm_lt
                    htendsto hA_lt_B
                ⟨N, hevent⟩⟩

/-- Assemble the historical solved-static input pair from its two genuine
independent ingredients.

This theorem records the non-circular dependency shape of the old pair:
the first component is structural boundary assembly, while the second follows
from that structural bridge together with an independently proved tail
absorption theorem. -/
theorem Complex.binetSecondFormula_boundarySolvedStatic_inputs_of_boundaryTarget_and_tailAbsorption
    (hboundary :
      Complex.BinetSecondFormulaFiniteHeightBoundaryTarget)
    (htail :
      Complex.BinetSecondFormulaBranchWallContourCancellationTailAbsorption) :
    Complex.BinetSecondFormulaFiniteHeightBoundaryTarget ∧
      Complex.BinetSecondFormulaBoundarySolvedStaticDecayEstimate := by
  exact
    ⟨hboundary,
      Complex.binetSecondFormula_boundarySolvedStaticDecayEstimate_of_boundaryTarget_and_tailAbsorption
        hboundary htail⟩

end
end LFunctions
end Boundary
