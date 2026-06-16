import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaFiniteHeightContour
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaVerticalLimits

/-!
# Finite Abel-Plana formula assembly

This file owns the assembly step from the finite-height cotangent contour and
vertical-side limit inputs to the finite Abel-Plana summation formula for the
logarithmic summand.  `BinetAbelPlanaCore` owns local definitions and residue
algebra; the contour and vertical helper files own the analytic contour/limit
inputs.  This file is the first layer allowed to consume both.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Split a subtraction of a two-term boundary sum into successive
subtractions. -/
theorem Complex.add_sub_add_sub_add_eq_add_sub_sub_sub_add
    (P H A B C R : ℂ) :
    P + H - (A + B) - C + R =
      P + H - A - B - C + R := by
  calc
    P + H - (A + B) - C + R =
        ((P + H - (A + B)) + -C) + R := by
      exact congrArg (fun x : ℂ => x + R)
        (sub_eq_add_neg (P + H - (A + B)) C)
    _ = (((P + H) + -(A + B)) + -C) + R := by
      exact congrArg (fun x : ℂ => (x + -C) + R)
        (sub_eq_add_neg (P + H) (A + B))
    _ = ((P + H) + (-A + -B) + -C) + R := by
      exact congrArg
        (fun x : ℂ => ((P + H) + x + -C) + R)
        (neg_add A B)
    _ = (((P + H) + -A) + -B + -C) + R := by
      exact congrArg (fun x : ℂ => (x + -C) + R)
        (add_assoc (P + H) (-A) (-B)).symm
    _ = ((P + H - A) - B - C) + R := by
      exact congrArg (fun x : ℂ => (x - C) + R)
        (sub_eq_add_neg (P + H - A) B).symm
    _ = (P + H - A - B - C) + R := rfl
    _ = P + H - A - B - C + R := rfl

/-- Stable wrapper for finite-height residue accounting with the orientation
sign forced by `horizontalEdgeError = bottom - top`. -/
theorem Complex.finiteAbelPlana_log_finiteHeightContourError_eq_neg_horizontalEdgeError
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    (T : ℝ)
    (hT : 0 < T) :
    Complex.finiteAbelPlanaLogFiniteHeightContourError N w T =
      -Complex.finiteAbelPlanaLogHorizontalEdgeError N w T := by
  exact
    Complex.finiteAbelPlana_log_finiteHeightContourError_eq_neg_horizontalEdgeError_owner
      hw N T hT

/-- Stable wrapper for horizontal-edge decay. -/
theorem Complex.finiteAbelPlana_log_horizontalEdgeError_tendsto_zero
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    Tendsto
      (fun T : ℝ =>
        Complex.finiteAbelPlanaLogHorizontalEdgeError N w T)
      atTop
      (𝓝 (0 : ℂ)) := by
  exact
    Complex.finiteAbelPlana_log_horizontalEdgeError_tendsto_zero_owner hw N

/-- Stable wrapper for lower vertical improper-integral convergence. -/
theorem Complex.finiteAbelPlana_log_lowerVerticalIntegralUpTo_tendsto_unsplitFull
    {w : ℂ}
    (hw : 0 < w.re) :
    Tendsto
      (fun T : ℝ =>
        Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)
      atTop
      (𝓝 (Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w)) := by
  exact
    Complex.finiteAbelPlana_log_lowerVerticalIntegralUpTo_tendsto_unsplitFull_owner
      hw

/-- Stable wrapper for splitting the lower vertical improper integral. -/
theorem Complex.finiteAbelPlana_log_lowerVerticalFullIntegral_eq_split
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    :
    Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w =
      Complex.finiteAbelPlanaLogSummandLowerVerticalIntegral N w := by
  exact Complex.finiteAbelPlana_log_lowerVerticalFullIntegral_eq_split_owner hw N

/-- Stable wrapper for lower vertical convergence to the named Binet split. -/
theorem Complex.finiteAbelPlana_log_lowerVerticalIntegralUpTo_tendsto_full
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    Tendsto
      (fun T : ℝ =>
        Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)
      atTop
      (𝓝 (Complex.finiteAbelPlanaLogSummandLowerVerticalIntegral N w)) := by
  exact
    Complex.finiteAbelPlana_log_lowerVerticalIntegralUpTo_tendsto_full_owner
      hw N

/-- Stable wrapper for upper vertical improper-integral convergence. -/
theorem Complex.finiteAbelPlana_log_upperVerticalIntegralUpTo_tendsto_unsplitFull
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    Tendsto
      (fun T : ℝ =>
        Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T)
      atTop
      (𝓝 (Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w)) := by
  exact
    Complex.finiteAbelPlana_log_upperVerticalIntegralUpTo_tendsto_unsplitFull_owner
      hw N

/-- Stable wrapper for the upper vertical naming equality. -/
theorem Complex.finiteAbelPlana_log_upperVerticalFullIntegral_eq_named
    (N : ℕ)
    (w : ℂ) :
    Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w =
      Complex.finiteAbelPlanaLogSummandUpperVerticalIntegral N w := by
  exact Complex.finiteAbelPlana_log_upperVerticalFullIntegral_eq_named_owner N w

/-- Stable wrapper for upper vertical convergence to the named residual. -/
theorem Complex.finiteAbelPlana_log_upperVerticalIntegralUpTo_tendsto_full
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    Tendsto
      (fun T : ℝ =>
        Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T)
      atTop
      (𝓝 (Complex.finiteAbelPlanaLogSummandUpperVerticalIntegral N w)) := by
  exact
    Complex.finiteAbelPlana_log_upperVerticalIntegralUpTo_tendsto_full_owner
      hw N

/-- Stable wrapper for convergence of the finite-height named boundary pieces. -/
theorem Complex.finiteAbelPlana_log_boundaryNamedPiecesUpTo_tendsto_full
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    Tendsto
      (fun T : ℝ =>
        Complex.finiteAbelPlanaLogBoundaryNamedPiecesUpTo N w T)
      atTop
      (𝓝 (Complex.finiteAbelPlanaLogBoundaryNamedPieces N w)) := by
  exact
    Complex.finiteAbelPlana_log_boundaryNamedPiecesUpTo_tendsto_full_owner
      hw N

/-- Stable wrapper for vanishing of the finite-height contour error. -/
theorem Complex.finiteAbelPlana_log_finiteHeightContourError_tendsto_zero
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    Tendsto
      (fun T : ℝ =>
        Complex.finiteAbelPlanaLogFiniteHeightContourError N w T)
      atTop
      (𝓝 (0 : ℂ)) := by
  exact
    Complex.finiteAbelPlana_log_finiteHeightContourError_tendsto_zero_owner
      hw N

/-- Finite-height principal-value rectangle cotangent formula. -/
theorem Complex.finiteAbelPlana_log_finiteHeightPrincipalValueCotangentFormula
    {w : ℂ}
    (hw : 0 < w.re) :
    ∀ N : ℕ,
      Tendsto
        (fun T : ℝ =>
          Complex.finiteAbelPlanaLogBoundaryNamedPiecesUpTo N w T)
        atTop
        (𝓝 (Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w)) := by
  intro N
  exact
    Complex.finiteAbelPlana_log_finiteHeightPrincipalValueCotangentFormula_from_contour
      hw N

/-- Finite Abel-Plana principal-value cotangent formula. -/
theorem Complex.finiteAbelPlana_log_principalValueCotangentFormula
    {w : ℂ}
    (hw : 0 < w.re) :
    ∀ N : ℕ,
      Complex.finiteAbelPlanaLogBoundaryNamedPieces N w =
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w := by
  intro N
  have hboundary :
      Tendsto
        (fun T : ℝ =>
          Complex.finiteAbelPlanaLogBoundaryNamedPiecesUpTo N w T)
        atTop
        (𝓝 (Complex.finiteAbelPlanaLogBoundaryNamedPieces N w)) :=
    Complex.finiteAbelPlana_log_boundaryNamedPiecesUpTo_tendsto_full hw N
  have hresidue :
      Tendsto
        (fun T : ℝ =>
          Complex.finiteAbelPlanaLogBoundaryNamedPiecesUpTo N w T)
        atTop
        (𝓝 (Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w)) :=
    Complex.finiteAbelPlana_log_finiteHeightPrincipalValueCotangentFormula
      hw N
  exact tendsto_nhds_unique hboundary hresidue

/-- The decomposed finite Abel-Plana boundary expression equals the residue
sum of the principal-value cotangent-kernel integrand. -/
theorem Complex.finiteAbelPlana_log_boundaryNamedPieces_eq_residueSum
    {w : ℂ}
    (hw : 0 < w.re) :
    ∀ N : ℕ,
      Complex.finiteAbelPlanaLogBoundaryNamedPieces N w =
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w := by
  intro N
  exact Complex.finiteAbelPlana_log_principalValueCotangentFormula hw N

/-- Kernel-level finite Abel-Plana rectangle theorem for the logarithmic
summand, in principal-value endpoint normalization. -/
theorem Complex.finiteAbelPlana_log_rectangleIntegrand_residueTheorem
    {w : ℂ}
    (hw : 0 < w.re) :
    ∀ N : ℕ,
      let M : ℕ := N + 1
      Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w =
        (∫ x : ℝ in (0 : ℝ)..(M : ℝ),
          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
          Complex.finiteAbelPlanaLogSummandLowerVerticalIntegral N w -
          Complex.finiteAbelPlanaLogSummandUpperVerticalIntegral N w := by
  intro N
  have hresidue :
      Complex.finiteAbelPlanaLogBoundaryNamedPieces N w =
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w :=
    Complex.finiteAbelPlana_log_boundaryNamedPieces_eq_residueSum hw N
  have hboundary :
      let M : ℕ := N + 1
      Complex.finiteAbelPlanaLogBoundaryNamedPieces N w =
        (∫ x : ℝ in (0 : ℝ)..(M : ℝ),
          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
          Complex.finiteAbelPlanaLogSummandLowerVerticalIntegral N w -
          Complex.finiteAbelPlanaLogSummandUpperVerticalIntegral N w :=
    Complex.finiteAbelPlana_log_boundaryNamedPieces_unfold N w
  exact hresidue.symm.trans hboundary

/-- Endpoint-restored integral-form finite Abel-Plana theorem for the
logarithmic summand residues.

The rectangle contour theorem is principal-value normalized: endpoint integer
poles are counted with half weight.  The ordinary finite sample sum requires
adding the explicit endpoint restoration. -/
theorem Complex.finiteAbelPlana_log_summand_integralForm_from_rectangleResidues
    {w : ℂ}
    (hw : 0 < w.re) :
    ∀ N : ℕ,
      let M : ℕ := N + 1
      ∑ n in Finset.range (M + 1), Complex.finiteAbelPlanaLogSummand w n =
        (∫ x : ℝ in (0 : ℝ)..(M : ℝ),
          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
          Complex.finiteAbelPlanaLogSummandLowerVerticalIntegral N w -
          Complex.finiteAbelPlanaLogSummandUpperVerticalIntegral N w +
          Complex.finiteAbelPlanaLogEndpointResidueRestoration N w := by
  intro N
  have hsample :
      Complex.finiteAbelPlanaLogIntegerResidueSum N w =
        let M : ℕ := N + 1
        ∑ n in Finset.range (M + 1),
          Complex.finiteAbelPlanaLogSummand w n :=
    Complex.finiteAbelPlana_log_integerResidueSum_eq_summandRange N w
  have hrestore :
      Complex.finiteAbelPlanaLogIntegerResidueSum N w =
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w +
          Complex.finiteAbelPlanaLogEndpointResidueRestoration N w :=
    Complex.finiteAbelPlana_log_integerResidueSum_eq_pvResidue_add_endpointRestoration
      N w
  have hpv :
      let M : ℕ := N + 1
      Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w =
        (∫ x : ℝ in (0 : ℝ)..(M : ℝ),
          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
          Complex.finiteAbelPlanaLogSummandLowerVerticalIntegral N w -
          Complex.finiteAbelPlanaLogSummandUpperVerticalIntegral N w :=
    Complex.finiteAbelPlana_log_rectangleIntegrand_residueTheorem hw N
  calc
    ∑ n in Finset.range (N + 1 + 1), Complex.finiteAbelPlanaLogSummand w n =
        Complex.finiteAbelPlanaLogIntegerResidueSum N w := by
      exact hsample.symm
    _ =
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w +
          Complex.finiteAbelPlanaLogEndpointResidueRestoration N w := by
      exact hrestore
    _ =
        (∫ x : ℝ in (0 : ℝ)..(N + 1 : ℝ),
          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
          Complex.finiteAbelPlanaLogSummandLowerVerticalIntegral N w -
          Complex.finiteAbelPlanaLogSummandUpperVerticalIntegral N w +
          Complex.finiteAbelPlanaLogEndpointResidueRestoration N w := by
      exact congrArg
        (fun t : ℂ =>
          t + Complex.finiteAbelPlanaLogEndpointResidueRestoration N w)
        hpv

/-- Owner-level finite Abel-Plana rectangle/residue identity for the
principal logarithmic summand `z ↦ log (w+z)`, with endpoint restoration
kept explicit. -/
theorem Complex.finiteAbelPlana_log_summand_rectangleResidue_decomposition
    {w : ℂ}
    (hw : 0 < w.re) :
    ∀ N : ℕ,
      let M : ℕ := N + 1
      ∑ n in Finset.range (M + 1), Complex.finiteAbelPlanaLogSummand w n =
        Complex.finiteAbelPlanaLogSummandEndpointPrimitive N w +
          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w +
          Complex.finiteAbelPlanaLogSummandLowerVerticalBoundary N w +
          Complex.finiteAbelPlanaLogSummandUpperVerticalBoundary N w +
          Complex.finiteAbelPlanaLogEndpointResidueRestoration N w := by
  intro N
  have hintegral :
      let M : ℕ := N + 1
      ∑ n in Finset.range (M + 1), Complex.finiteAbelPlanaLogSummand w n =
        (∫ x : ℝ in (0 : ℝ)..(M : ℝ),
          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
          Complex.finiteAbelPlanaLogSummandLowerVerticalIntegral N w -
          Complex.finiteAbelPlanaLogSummandUpperVerticalIntegral N w +
          Complex.finiteAbelPlanaLogEndpointResidueRestoration N w :=
    Complex.finiteAbelPlana_log_summand_integralForm_from_rectangleResidues
      hw N
  have hprimitive :
      let M : ℕ := N + 1
      ∫ x : ℝ in (0 : ℝ)..(M : ℝ),
          Complex.finiteAbelPlanaLogSummand w (x : ℂ) =
        Complex.finiteAbelPlanaLogSummandEndpointPrimitive N w :=
    Complex.finiteAbelPlana_log_summand_realSegmentIntegral_eq_endpointPrimitive
      hw N
  have hlower :
      -Complex.finiteAbelPlanaLogSummandLowerVerticalIntegral N w =
        Complex.finiteAbelPlanaLogSummandLowerVerticalBoundary N w :=
    (Complex.finiteAbelPlana_log_summand_lowerBoundary_eq_neg_lowerIntegral
      N w).symm
  have hupper :
      -Complex.finiteAbelPlanaLogSummandUpperVerticalIntegral N w =
        Complex.finiteAbelPlanaLogSummandUpperVerticalBoundary N w :=
    (Complex.finiteAbelPlana_log_summand_upperBoundary_eq_neg_upperIntegral
      N w).symm
  calc
    ∑ n in Finset.range (N + 1 + 1), Complex.finiteAbelPlanaLogSummand w n =
        (∫ x : ℝ in (0 : ℝ)..(N + 1 : ℝ),
          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
          Complex.finiteAbelPlanaLogSummandLowerVerticalIntegral N w -
          Complex.finiteAbelPlanaLogSummandUpperVerticalIntegral N w +
          Complex.finiteAbelPlanaLogEndpointResidueRestoration N w := by
      exact hintegral
    _ =
        Complex.finiteAbelPlanaLogSummandEndpointPrimitive N w +
          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
          Complex.finiteAbelPlanaLogSummandLowerVerticalIntegral N w -
          Complex.finiteAbelPlanaLogSummandUpperVerticalIntegral N w +
          Complex.finiteAbelPlanaLogEndpointResidueRestoration N w := by
      exact congrArg
        (fun t : ℂ => t +
          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
          Complex.finiteAbelPlanaLogSummandLowerVerticalIntegral N w -
          Complex.finiteAbelPlanaLogSummandUpperVerticalIntegral N w +
          Complex.finiteAbelPlanaLogEndpointResidueRestoration N w)
        hprimitive
    _ =
        Complex.finiteAbelPlanaLogSummandEndpointPrimitive N w +
          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w +
          Complex.finiteAbelPlanaLogSummandLowerVerticalBoundary N w -
          Complex.finiteAbelPlanaLogSummandUpperVerticalIntegral N w +
          Complex.finiteAbelPlanaLogEndpointResidueRestoration N w := by
      exact congrArg
        (fun t : ℂ =>
          Complex.finiteAbelPlanaLogSummandEndpointPrimitive N w +
            Complex.finiteAbelPlanaLogSummandHalfEndpoints N w + t -
            Complex.finiteAbelPlanaLogSummandUpperVerticalIntegral N w +
            Complex.finiteAbelPlanaLogEndpointResidueRestoration N w)
        hlower
    _ =
        Complex.finiteAbelPlanaLogSummandEndpointPrimitive N w +
          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w +
          Complex.finiteAbelPlanaLogSummandLowerVerticalBoundary N w +
          Complex.finiteAbelPlanaLogSummandUpperVerticalBoundary N w +
          Complex.finiteAbelPlanaLogEndpointResidueRestoration N w := by
      exact congrArg
        (fun t : ℂ =>
          Complex.finiteAbelPlanaLogSummandEndpointPrimitive N w +
            Complex.finiteAbelPlanaLogSummandHalfEndpoints N w +
            Complex.finiteAbelPlanaLogSummandLowerVerticalBoundary N w + t +
            Complex.finiteAbelPlanaLogEndpointResidueRestoration N w)
        hupper

/-- Endpoint-restored finite Abel-Plana contour decomposition for the
logarithmic summand residues. -/
theorem Complex.finiteAbelPlana_log_summand_eq_contourDecomposition
    {w : ℂ}
    (hw : 0 < w.re) :
    ∀ N : ℕ,
      let M : ℕ := N + 1
      ∑ n in Finset.range (M + 1), Complex.log (w + n) =
        Complex.finiteAbelPlanaLogSummandEndpointPrimitive N w +
          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w +
          Complex.finiteAbelPlanaLogSummandLowerVerticalBoundary N w +
          Complex.finiteAbelPlanaLogSummandUpperVerticalBoundary N w +
          Complex.finiteAbelPlanaLogEndpointResidueRestoration N w := by
  intro N
  exact Complex.finiteAbelPlana_log_summand_rectangleResidue_decomposition hw N

/-- Endpoint-restored finite Abel-Plana summation formula for the logarithmic
summand residues. -/
theorem Complex.finiteAbelPlana_log_summand_eq_mainBoundaryUpper
    {w : ℂ}
    (hw : 0 < w.re) :
    ∀ N : ℕ,
      let M : ℕ := N + 1
      ∑ n in Finset.range (M + 1), Complex.log (w + n) =
        (((w + (M : ℂ)) * Complex.log (w + (M : ℂ)) -
            (w + (M : ℂ))) -
          (w * Complex.log w - w)) +
          (Complex.log w + Complex.log (w + (M : ℂ))) / 2 -
          Complex.binetAbelPlanaFiniteBoundaryCorrection N w -
          Complex.binetAbelPlanaFiniteLowerContourTail N w -
          Complex.binetAbelPlanaFiniteUpperContourResidual N w +
          Complex.finiteAbelPlanaLogEndpointResidueRestoration N w := by
  intro N
  have hcontour :
      let M : ℕ := N + 1
      ∑ n in Finset.range (M + 1), Complex.log (w + n) =
        Complex.finiteAbelPlanaLogSummandEndpointPrimitive N w +
          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w +
          Complex.finiteAbelPlanaLogSummandLowerVerticalBoundary N w +
          Complex.finiteAbelPlanaLogSummandUpperVerticalBoundary N w +
          Complex.finiteAbelPlanaLogEndpointResidueRestoration N w :=
    Complex.finiteAbelPlana_log_summand_eq_contourDecomposition hw N
  have hprimitive :
      Complex.finiteAbelPlanaLogSummandEndpointPrimitive N w =
        (((w + ((N + 1 : ℕ) : ℂ)) *
              Complex.log (w + ((N + 1 : ℕ) : ℂ)) -
            (w + ((N + 1 : ℕ) : ℂ))) -
          (w * Complex.log w - w)) :=
    rfl
  have hhalf :
      Complex.finiteAbelPlanaLogSummandHalfEndpoints N w =
        (Complex.log w +
          Complex.log (w + ((N + 1 : ℕ) : ℂ))) / 2 := by
    rfl
  have hlower :
      Complex.finiteAbelPlanaLogSummandLowerVerticalBoundary N w =
        -Complex.finiteAbelPlanaLogSummandLowerVerticalIntegral N w :=
    Complex.finiteAbelPlana_log_summand_lowerBoundary_eq_neg_lowerIntegral
      N w
  have hlower_name :
      Complex.finiteAbelPlanaLogSummandLowerVerticalIntegral N w =
        Complex.binetAbelPlanaFiniteBoundaryCorrection N w +
          Complex.binetAbelPlanaFiniteLowerContourTail N w := by
    rfl
  have hupper :
      Complex.finiteAbelPlanaLogSummandUpperVerticalBoundary N w =
        -Complex.finiteAbelPlanaLogSummandUpperVerticalIntegral N w :=
    Complex.finiteAbelPlana_log_summand_upperBoundary_eq_neg_upperIntegral
      N w
  have hupper_name :
      Complex.finiteAbelPlanaLogSummandUpperVerticalIntegral N w =
        Complex.binetAbelPlanaFiniteUpperContourResidual N w := by
    rfl
  exact
    hcontour.trans <| by
      calc
        Complex.finiteAbelPlanaLogSummandEndpointPrimitive N w +
            Complex.finiteAbelPlanaLogSummandHalfEndpoints N w +
            Complex.finiteAbelPlanaLogSummandLowerVerticalBoundary N w +
            Complex.finiteAbelPlanaLogSummandUpperVerticalBoundary N w +
            Complex.finiteAbelPlanaLogEndpointResidueRestoration N w =
            (((w + ((N + 1 : ℕ) : ℂ)) *
                  Complex.log (w + ((N + 1 : ℕ) : ℂ)) -
                (w + ((N + 1 : ℕ) : ℂ))) -
              (w * Complex.log w - w)) +
              Complex.finiteAbelPlanaLogSummandHalfEndpoints N w +
              Complex.finiteAbelPlanaLogSummandLowerVerticalBoundary N w +
              Complex.finiteAbelPlanaLogSummandUpperVerticalBoundary N w +
              Complex.finiteAbelPlanaLogEndpointResidueRestoration N w := by
          exact congrArg
            (fun t : ℂ =>
              t +
                Complex.finiteAbelPlanaLogSummandHalfEndpoints N w +
                Complex.finiteAbelPlanaLogSummandLowerVerticalBoundary N w +
                Complex.finiteAbelPlanaLogSummandUpperVerticalBoundary N w +
                Complex.finiteAbelPlanaLogEndpointResidueRestoration N w)
            hprimitive
        _ =
            (((w + ((N + 1 : ℕ) : ℂ)) *
                  Complex.log (w + ((N + 1 : ℕ) : ℂ)) -
                (w + ((N + 1 : ℕ) : ℂ))) -
              (w * Complex.log w - w)) +
              (Complex.log w +
                Complex.log (w + ((N + 1 : ℕ) : ℂ))) / 2 +
              Complex.finiteAbelPlanaLogSummandLowerVerticalBoundary N w +
              Complex.finiteAbelPlanaLogSummandUpperVerticalBoundary N w +
              Complex.finiteAbelPlanaLogEndpointResidueRestoration N w := by
          exact congrArg
            (fun t : ℂ =>
              (((w + ((N + 1 : ℕ) : ℂ)) *
                    Complex.log (w + ((N + 1 : ℕ) : ℂ)) -
                  (w + ((N + 1 : ℕ) : ℂ))) -
                (w * Complex.log w - w)) +
                t +
                Complex.finiteAbelPlanaLogSummandLowerVerticalBoundary N w +
                Complex.finiteAbelPlanaLogSummandUpperVerticalBoundary N w +
                Complex.finiteAbelPlanaLogEndpointResidueRestoration N w)
            hhalf
        _ =
            (((w + ((N + 1 : ℕ) : ℂ)) *
                  Complex.log (w + ((N + 1 : ℕ) : ℂ)) -
                (w + ((N + 1 : ℕ) : ℂ))) -
              (w * Complex.log w - w)) +
              (Complex.log w +
                Complex.log (w + ((N + 1 : ℕ) : ℂ))) / 2 -
              Complex.finiteAbelPlanaLogSummandLowerVerticalIntegral N w +
              Complex.finiteAbelPlanaLogSummandUpperVerticalBoundary N w +
              Complex.finiteAbelPlanaLogEndpointResidueRestoration N w := by
          exact congrArg
            (fun t : ℂ =>
              (((w + ((N + 1 : ℕ) : ℂ)) *
                    Complex.log (w + ((N + 1 : ℕ) : ℂ)) -
                  (w + ((N + 1 : ℕ) : ℂ))) -
                (w * Complex.log w - w)) +
                (Complex.log w +
                  Complex.log (w + ((N + 1 : ℕ) : ℂ))) / 2 +
                t +
                Complex.finiteAbelPlanaLogSummandUpperVerticalBoundary N w +
                Complex.finiteAbelPlanaLogEndpointResidueRestoration N w)
            hlower
        _ =
            (((w + ((N + 1 : ℕ) : ℂ)) *
                  Complex.log (w + ((N + 1 : ℕ) : ℂ)) -
                (w + ((N + 1 : ℕ) : ℂ))) -
              (w * Complex.log w - w)) +
              (Complex.log w +
                Complex.log (w + ((N + 1 : ℕ) : ℂ))) / 2 -
              (Complex.binetAbelPlanaFiniteBoundaryCorrection N w +
                Complex.binetAbelPlanaFiniteLowerContourTail N w) +
              Complex.finiteAbelPlanaLogSummandUpperVerticalBoundary N w +
              Complex.finiteAbelPlanaLogEndpointResidueRestoration N w := by
          exact congrArg
            (fun t : ℂ =>
              (((w + ((N + 1 : ℕ) : ℂ)) *
                    Complex.log (w + ((N + 1 : ℕ) : ℂ)) -
                  (w + ((N + 1 : ℕ) : ℂ))) -
                (w * Complex.log w - w)) +
                (Complex.log w +
                  Complex.log (w + ((N + 1 : ℕ) : ℂ))) / 2 -
                t +
                Complex.finiteAbelPlanaLogSummandUpperVerticalBoundary N w +
                Complex.finiteAbelPlanaLogEndpointResidueRestoration N w)
            hlower_name
        _ =
            (((w + ((N + 1 : ℕ) : ℂ)) *
                  Complex.log (w + ((N + 1 : ℕ) : ℂ)) -
                (w + ((N + 1 : ℕ) : ℂ))) -
              (w * Complex.log w - w)) +
              (Complex.log w +
                Complex.log (w + ((N + 1 : ℕ) : ℂ))) / 2 -
              (Complex.binetAbelPlanaFiniteBoundaryCorrection N w +
                Complex.binetAbelPlanaFiniteLowerContourTail N w) -
              Complex.finiteAbelPlanaLogSummandUpperVerticalIntegral N w +
              Complex.finiteAbelPlanaLogEndpointResidueRestoration N w := by
          exact congrArg
            (fun t : ℂ =>
              (((w + ((N + 1 : ℕ) : ℂ)) *
                    Complex.log (w + ((N + 1 : ℕ) : ℂ)) -
                  (w + ((N + 1 : ℕ) : ℂ))) -
                (w * Complex.log w - w)) +
                (Complex.log w +
                  Complex.log (w + ((N + 1 : ℕ) : ℂ))) / 2 -
                (Complex.binetAbelPlanaFiniteBoundaryCorrection N w +
                  Complex.binetAbelPlanaFiniteLowerContourTail N w) +
                t +
                Complex.finiteAbelPlanaLogEndpointResidueRestoration N w)
            hupper
        _ =
            (((w + ((N + 1 : ℕ) : ℂ)) *
                  Complex.log (w + ((N + 1 : ℕ) : ℂ)) -
                (w + ((N + 1 : ℕ) : ℂ))) -
              (w * Complex.log w - w)) +
              (Complex.log w +
                Complex.log (w + ((N + 1 : ℕ) : ℂ))) / 2 -
              (Complex.binetAbelPlanaFiniteBoundaryCorrection N w +
                Complex.binetAbelPlanaFiniteLowerContourTail N w) -
              Complex.binetAbelPlanaFiniteUpperContourResidual N w +
              Complex.finiteAbelPlanaLogEndpointResidueRestoration N w := by
          exact congrArg
            (fun t : ℂ =>
              (((w + ((N + 1 : ℕ) : ℂ)) *
                    Complex.log (w + ((N + 1 : ℕ) : ℂ)) -
                  (w + ((N + 1 : ℕ) : ℂ))) -
                (w * Complex.log w - w)) +
                (Complex.log w +
                  Complex.log (w + ((N + 1 : ℕ) : ℂ))) / 2 -
                (Complex.binetAbelPlanaFiniteBoundaryCorrection N w +
                  Complex.binetAbelPlanaFiniteLowerContourTail N w) -
                t +
                Complex.finiteAbelPlanaLogEndpointResidueRestoration N w)
            hupper_name
        _ =
            (((w + (N + 1 : ℂ)) * Complex.log (w + (N + 1 : ℂ)) -
                (w + (N + 1 : ℂ))) -
              (w * Complex.log w - w)) +
              (Complex.log w + Complex.log (w + (N + 1 : ℂ))) / 2 -
              Complex.binetAbelPlanaFiniteBoundaryCorrection N w -
              Complex.binetAbelPlanaFiniteLowerContourTail N w -
              Complex.binetAbelPlanaFiniteUpperContourResidual N w +
              Complex.finiteAbelPlanaLogEndpointResidueRestoration N w := by
          exact
            Complex.add_sub_add_sub_add_eq_add_sub_sub_sub_add
              ((((w + ((N + 1 : ℕ) : ℂ)) *
                    Complex.log (w + ((N + 1 : ℕ) : ℂ)) -
                  (w + ((N + 1 : ℕ) : ℂ))) -
                (w * Complex.log w - w)))
              ((Complex.log w +
                Complex.log (w + ((N + 1 : ℕ) : ℂ))) / 2)
              (Complex.binetAbelPlanaFiniteBoundaryCorrection N w)
              (Complex.binetAbelPlanaFiniteLowerContourTail N w)
              (Complex.binetAbelPlanaFiniteUpperContourResidual N w)
              (Complex.finiteAbelPlanaLogEndpointResidueRestoration N w)

end

end LFunctions
end Boundary
