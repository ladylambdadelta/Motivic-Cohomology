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

/-- Split a subtraction of a two-term boundary sum into successive
subtractions. -/
theorem Complex.add_sub_add_sub_eq_add_sub_sub
    (P H A B C : ℂ) :
    P + H - (A + B) - C =
      P + H - A - B - C := by
  calc
    P + H - (A + B) - C =
        (P + H - (A + B)) + -C := by
      exact sub_eq_add_neg (P + H - (A + B)) C
    _ = ((P + H) + -(A + B)) + -C := by
      exact congrArg (fun x : ℂ => x + -C)
        (sub_eq_add_neg (P + H) (A + B))
    _ = ((P + H) + (-A + -B)) + -C := by
      exact congrArg
        (fun x : ℂ => ((P + H) + x) + -C)
        (neg_add A B)
    _ = (((P + H) + -A) + -B) + -C := by
      exact congrArg (fun x : ℂ => x + -C)
        (add_assoc (P + H) (-A) (-B)).symm
    _ = ((P + H - A) - B) - C := by
      exact congrArg (fun x : ℂ => x - C)
        (sub_eq_add_neg (P + H - A) B).symm
    _ = P + H - A - B - C := rfl

/-- Stable wrapper for finite-height residue accounting with the orientation
sign forced by `horizontalEdgeError = bottom - top`. -/
theorem Complex.finiteAbelPlana_log_finiteHeightContourError_eq_neg_horizontalEdgeError
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    (hdecInteriorPole : ∀ n : ℕ, n ∈ Finset.range N →
      ∀ z : ℂ, Decidable (z = ((n + 1 : ℕ) : ℂ)))
    (T : ℝ)
    (hT : 0 < T)
    (hevent :
      (fun ρ : ℝ =>
          Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ) =ᶠ[
        𝓝[>] (0 : ℝ)]
        (fun ρ : ℝ =>
          (Complex.finiteAbelPlanaLogLeftBoundaryFacePVNormalized N w T ρ +
            Complex.finiteAbelPlanaLogRightBoundaryFacePVNormalized N w T ρ) +
            Complex.finiteAbelPlanaLogHorizontalEdgeError N w T))
    (htarget :
      (((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
            (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
              Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) +
          (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) +
        ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
            (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
              Complex.I *
                Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) +
          (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T))) +
        Complex.finiteAbelPlanaLogHorizontalEdgeError N w T =
          Complex.finiteAbelPlanaLogFiniteHeightNamedSideExpression N w T +
            Complex.finiteAbelPlanaLogHorizontalEdgeError N w T) :
    Complex.finiteAbelPlanaLogFiniteHeightContourError N w T =
      -Complex.finiteAbelPlanaLogHorizontalEdgeError N w T := by
  exact
    Complex.finiteAbelPlana_log_finiteHeightContourError_eq_neg_horizontalEdgeError_owner
      hw N hdecInteriorPole T hT hevent htarget

/-- Stable wrapper for horizontal-edge decay. -/
theorem Complex.finiteAbelPlana_log_horizontalEdgeError_tendsto_zero
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    Filter.Tendsto
      (fun T : ℝ =>
        Complex.finiteAbelPlanaLogHorizontalEdgeError N w T)
      Filter.atTop
      (𝓝 (0 : ℂ)) := by
  exact
    Complex.finiteAbelPlana_log_horizontalEdgeError_tendsto_zero_owner hw N

/-- Stable wrapper for lower vertical improper-integral convergence. -/
theorem Complex.finiteAbelPlana_log_lowerVerticalIntegralUpTo_tendsto_unsplitFull
    {w : ℂ}
    (hw : 0 < w.re) :
    Filter.Tendsto
      (fun T : ℝ =>
        Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)
      Filter.atTop
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
    Filter.Tendsto
      (fun T : ℝ =>
        Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)
      Filter.atTop
      (𝓝 (Complex.finiteAbelPlanaLogSummandLowerVerticalIntegral N w)) := by
  exact
    Complex.finiteAbelPlana_log_lowerVerticalIntegralUpTo_tendsto_full_owner
      hw N

/-- Stable wrapper for upper vertical improper-integral convergence. -/
theorem Complex.finiteAbelPlana_log_upperVerticalIntegralUpTo_tendsto_unsplitFull
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    Filter.Tendsto
      (fun T : ℝ =>
        Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T)
      Filter.atTop
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
    Filter.Tendsto
      (fun T : ℝ =>
        Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T)
      Filter.atTop
      (𝓝 (Complex.finiteAbelPlanaLogSummandUpperVerticalIntegral N w)) := by
  exact
    Complex.finiteAbelPlana_log_upperVerticalIntegralUpTo_tendsto_full_owner
      hw N

/-- Stable wrapper for convergence of the finite-height named boundary pieces. -/
theorem Complex.finiteAbelPlana_log_boundaryNamedPiecesUpTo_tendsto_full
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    Filter.Tendsto
      (fun T : ℝ =>
        Complex.finiteAbelPlanaLogBoundaryNamedPiecesUpTo N w T)
      Filter.atTop
      (𝓝 (Complex.finiteAbelPlanaLogBoundaryNamedPieces N w)) := by
  exact
    Complex.finiteAbelPlana_log_boundaryNamedPiecesUpTo_tendsto_full_owner
      hw N

/-- Stable wrapper for vanishing of the finite-height contour error. -/
theorem Complex.finiteAbelPlana_log_finiteHeightContourError_tendsto_zero
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    (hdecInteriorPole : ∀ n : ℕ, n ∈ Finset.range N →
      ∀ z : ℂ, Decidable (z = ((n + 1 : ℕ) : ℂ)))
    (hbridges : Complex.FiniteHeightPVBridgePackageAt N w) :
    Filter.Tendsto
      (fun T : ℝ =>
        Complex.finiteAbelPlanaLogFiniteHeightContourError N w T)
      Filter.atTop
      (𝓝 (0 : ℂ)) := by
  exact
    Complex.finiteAbelPlana_log_finiteHeightContourError_tendsto_zero_owner
      hw N hdecInteriorPole hbridges

/-- Stable wrapper for endpoint-restored finite-height contour-error
cancellation. -/
theorem Complex.finiteAbelPlana_log_finiteHeightEndpointRestoredContourError_tendsto_zero
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    (hdecInteriorPole : ∀ n : ℕ, n ∈ Finset.range N →
      ∀ z : ℂ, Decidable (z = ((n + 1 : ℕ) : ℂ)))
    (hbridges : Complex.FiniteHeightPVBridgePackageAtEndpointRestored N w) :
    Filter.Tendsto
      (fun T : ℝ =>
        Complex.finiteAbelPlanaLogFiniteHeightEndpointRestoredContourError N w T)
      Filter.atTop
      (𝓝 (0 : ℂ)) := by
  exact
    Complex.finiteAbelPlana_log_finiteHeightEndpointRestoredContourError_tendsto_zero_owner
      hw N hdecInteriorPole hbridges

/-- Finite-height principal-value rectangle cotangent formula. -/
theorem Complex.finiteAbelPlana_log_finiteHeightPrincipalValueCotangentFormula
    {w : ℂ}
    (hw : 0 < w.re)
    (hbridges : Complex.FiniteHeightPVBridgePackage w) :
    ∀ N : ℕ,
      (∀ n : ℕ, n ∈ Finset.range N →
        ∀ z : ℂ, Decidable (z = ((n + 1 : ℕ) : ℂ))) →
      Filter.Tendsto
        (fun T : ℝ =>
          Complex.finiteAbelPlanaLogBoundaryNamedPiecesUpTo N w T)
        Filter.atTop
        (𝓝 (Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w)) := by
  intro N
  intro hdecInteriorPole
  exact
    Complex.finiteAbelPlana_log_finiteHeightPrincipalValueCotangentFormula_from_contour
      hw hbridges N hdecInteriorPole

/-- Finite Abel-Plana principal-value cotangent formula. -/
theorem Complex.finiteAbelPlana_log_principalValueCotangentFormula
    {w : ℂ}
    (hw : 0 < w.re)
    (hbridges : Complex.FiniteHeightPVBridgePackage w) :
    ∀ N : ℕ,
      (∀ n : ℕ, n ∈ Finset.range N →
        ∀ z : ℂ, Decidable (z = ((n + 1 : ℕ) : ℂ))) →
      Complex.finiteAbelPlanaLogBoundaryNamedPieces N w =
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w := by
  intro N
  intro hdecInteriorPole
  have hboundary :
      Filter.Tendsto
        (fun T : ℝ =>
          Complex.finiteAbelPlanaLogBoundaryNamedPiecesUpTo N w T)
        Filter.atTop
        (𝓝 (Complex.finiteAbelPlanaLogBoundaryNamedPieces N w)) :=
    Complex.finiteAbelPlana_log_boundaryNamedPiecesUpTo_tendsto_full hw N
  have hresidue :
      Filter.Tendsto
        (fun T : ℝ =>
          Complex.finiteAbelPlanaLogBoundaryNamedPiecesUpTo N w T)
        Filter.atTop
        (𝓝 (Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w)) :=
    Complex.finiteAbelPlana_log_finiteHeightPrincipalValueCotangentFormula
      hw hbridges N hdecInteriorPole
  exact tendsto_nhds_unique hboundary hresidue

/-- The decomposed finite Abel-Plana boundary expression equals the residue
sum of the principal-value cotangent-kernel integrand. -/
theorem Complex.finiteAbelPlana_log_boundaryNamedPieces_eq_residueSum
    {w : ℂ}
    (hw : 0 < w.re)
    (hbridges : Complex.FiniteHeightPVBridgePackage w) :
    ∀ N : ℕ,
      (∀ n : ℕ, n ∈ Finset.range N →
        ∀ z : ℂ, Decidable (z = ((n + 1 : ℕ) : ℂ))) →
      Complex.finiteAbelPlanaLogBoundaryNamedPieces N w =
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w := by
  intro N
  intro hdecInteriorPole
  exact
    Complex.finiteAbelPlana_log_principalValueCotangentFormula
      hw hbridges N hdecInteriorPole

/-- Kernel-level finite Abel-Plana rectangle theorem for the logarithmic
summand, in principal-value endpoint normalization. -/
theorem Complex.finiteAbelPlana_log_rectangleIntegrand_residueTheorem
    {w : ℂ}
    (hw : 0 < w.re)
    (hbridges : Complex.FiniteHeightPVBridgePackage w) :
    ∀ N : ℕ,
      (∀ n : ℕ, n ∈ Finset.range N →
        ∀ z : ℂ, Decidable (z = ((n + 1 : ℕ) : ℂ))) →
      let M : ℕ := N + 1
      Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w =
        (∫ x : ℝ in (0 : ℝ)..(M : ℝ),
          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
          Complex.finiteAbelPlanaLogSummandLowerVerticalIntegral N w -
          Complex.finiteAbelPlanaLogSummandUpperVerticalIntegral N w := by
  intro N
  intro hdecInteriorPole
  have hresidue :
    Complex.finiteAbelPlanaLogBoundaryNamedPieces N w =
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w :=
    Complex.finiteAbelPlana_log_boundaryNamedPieces_eq_residueSum
      hw hbridges N hdecInteriorPole
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
    (hw : 0 < w.re)
    (hbridges : Complex.FiniteHeightPVBridgePackage w) :
    ∀ N : ℕ,
      (∀ n : ℕ, n ∈ Finset.range N →
        ∀ z : ℂ, Decidable (z = ((n + 1 : ℕ) : ℂ))) →
      let M : ℕ := N + 1
      ∑ n in Finset.range (M + 1), Complex.finiteAbelPlanaLogSummand w n =
        (∫ x : ℝ in (0 : ℝ)..(M : ℝ),
          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
          Complex.finiteAbelPlanaLogSummandLowerVerticalIntegral N w -
            Complex.finiteAbelPlanaLogSummandUpperVerticalIntegral N w +
            Complex.finiteAbelPlanaLogEndpointResidueRestoration N w := by
  intro N
  intro hdecInteriorPole
  let M : ℕ := N + 1
  have hsample :
      Complex.finiteAbelPlanaLogIntegerResidueSum N w =
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
      Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w =
        (∫ x : ℝ in (0 : ℝ)..(M : ℝ),
          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
          Complex.finiteAbelPlanaLogSummandLowerVerticalIntegral N w -
          Complex.finiteAbelPlanaLogSummandUpperVerticalIntegral N w :=
    Complex.finiteAbelPlana_log_rectangleIntegrand_residueTheorem hw hbridges N
      hdecInteriorPole
  calc
    ∑ n in Finset.range (M + 1), Complex.finiteAbelPlanaLogSummand w n =
        Complex.finiteAbelPlanaLogIntegerResidueSum N w := by
      exact hsample.symm
    _ =
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w +
          Complex.finiteAbelPlanaLogEndpointResidueRestoration N w := by
      exact hrestore
    _ =
          (∫ x : ℝ in (0 : ℝ)..(M : ℝ),
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
    (hw : 0 < w.re)
    (hbridges : Complex.FiniteHeightPVBridgePackage w) :
    ∀ N : ℕ,
      (∀ n : ℕ, n ∈ Finset.range N →
        ∀ z : ℂ, Decidable (z = ((n + 1 : ℕ) : ℂ))) →
      let M : ℕ := N + 1
      ∑ n in Finset.range (M + 1), Complex.finiteAbelPlanaLogSummand w n =
        Complex.finiteAbelPlanaLogSummandEndpointPrimitive N w +
          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w +
          Complex.finiteAbelPlanaLogSummandLowerVerticalBoundary N w +
            Complex.finiteAbelPlanaLogSummandUpperVerticalBoundary N w +
            Complex.finiteAbelPlanaLogEndpointResidueRestoration N w := by
  intro N
  intro hdecInteriorPole
  let M : ℕ := N + 1
  have hintegral :
      ∑ n in Finset.range (M + 1), Complex.finiteAbelPlanaLogSummand w n =
        (∫ x : ℝ in (0 : ℝ)..(M : ℝ),
          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
          Complex.finiteAbelPlanaLogSummandLowerVerticalIntegral N w -
          Complex.finiteAbelPlanaLogSummandUpperVerticalIntegral N w +
          Complex.finiteAbelPlanaLogEndpointResidueRestoration N w :=
    Complex.finiteAbelPlana_log_summand_integralForm_from_rectangleResidues
      hw hbridges N hdecInteriorPole
  have hprimitive :
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
    ∑ n in Finset.range (M + 1), Complex.finiteAbelPlanaLogSummand w n =
        (∫ x : ℝ in (0 : ℝ)..(M : ℝ),
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
    (hw : 0 < w.re)
    (hbridges : Complex.FiniteHeightPVBridgePackage w) :
    ∀ N : ℕ,
      (∀ n : ℕ, n ∈ Finset.range N →
        ∀ z : ℂ, Decidable (z = ((n + 1 : ℕ) : ℂ))) →
      let M : ℕ := N + 1
      ∑ n in Finset.range (M + 1), Complex.log (w + n) =
        Complex.finiteAbelPlanaLogSummandEndpointPrimitive N w +
          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w +
          Complex.finiteAbelPlanaLogSummandLowerVerticalBoundary N w +
          Complex.finiteAbelPlanaLogSummandUpperVerticalBoundary N w +
          Complex.finiteAbelPlanaLogEndpointResidueRestoration N w := by
  intro N
  intro hdecInteriorPole
  exact
    Complex.finiteAbelPlana_log_summand_rectangleResidue_decomposition
      hw hbridges N hdecInteriorPole

/-- Endpoint-restored finite Abel-Plana summation formula for the logarithmic
summand residues. -/
theorem Complex.finiteAbelPlana_log_summand_eq_mainBoundaryUpper
    {w : ℂ}
    (hw : 0 < w.re)
    (hbridges : Complex.FiniteHeightPVBridgePackage w) :
    ∀ N : ℕ,
      (∀ n : ℕ, n ∈ Finset.range N →
        ∀ z : ℂ, Decidable (z = ((n + 1 : ℕ) : ℂ))) →
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
  intro hdecInteriorPole
  let M : ℕ := N + 1
  have hcontour :
      ∑ n in Finset.range (M + 1), Complex.log (w + n) =
        Complex.finiteAbelPlanaLogSummandEndpointPrimitive N w +
          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w +
          Complex.finiteAbelPlanaLogSummandLowerVerticalBoundary N w +
          Complex.finiteAbelPlanaLogSummandUpperVerticalBoundary N w +
          Complex.finiteAbelPlanaLogEndpointResidueRestoration N w :=
    Complex.finiteAbelPlana_log_summand_eq_contourDecomposition hw hbridges N
      hdecInteriorPole
  have hprimitive :
      Complex.finiteAbelPlanaLogSummandEndpointPrimitive N w =
        (((w + (M : ℂ)) *
              Complex.log (w + (M : ℂ)) -
            (w + (M : ℂ))) -
          (w * Complex.log w - w)) :=
    rfl
  have hhalf :
      Complex.finiteAbelPlanaLogSummandHalfEndpoints N w =
        (Complex.log w +
          Complex.log (w + (M : ℂ))) / 2 := by
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
              (((w + (M : ℂ)) *
                    Complex.log (w + (M : ℂ)) -
                  (w + (M : ℂ))) -
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
              (((w + (M : ℂ)) *
                    Complex.log (w + (M : ℂ)) -
                  (w + (M : ℂ))) -
              (w * Complex.log w - w)) +
                (Complex.log w +
                  Complex.log (w + (M : ℂ))) / 2 +
              Complex.finiteAbelPlanaLogSummandLowerVerticalBoundary N w +
              Complex.finiteAbelPlanaLogSummandUpperVerticalBoundary N w +
              Complex.finiteAbelPlanaLogEndpointResidueRestoration N w := by
          exact congrArg
            (fun t : ℂ =>
                (((w + (M : ℂ)) *
                      Complex.log (w + (M : ℂ)) -
                    (w + (M : ℂ))) -
                (w * Complex.log w - w)) +
                t +
                Complex.finiteAbelPlanaLogSummandLowerVerticalBoundary N w +
                Complex.finiteAbelPlanaLogSummandUpperVerticalBoundary N w +
                Complex.finiteAbelPlanaLogEndpointResidueRestoration N w)
            hhalf
        _ =
              (((w + (M : ℂ)) *
                    Complex.log (w + (M : ℂ)) -
                  (w + (M : ℂ))) -
              (w * Complex.log w - w)) +
                (Complex.log w +
                  Complex.log (w + (M : ℂ))) / 2 -
              Complex.finiteAbelPlanaLogSummandLowerVerticalIntegral N w +
              Complex.finiteAbelPlanaLogSummandUpperVerticalBoundary N w +
              Complex.finiteAbelPlanaLogEndpointResidueRestoration N w := by
          exact congrArg
            (fun t : ℂ =>
                (((w + (M : ℂ)) *
                      Complex.log (w + (M : ℂ)) -
                    (w + (M : ℂ))) -
                (w * Complex.log w - w)) +
                  (Complex.log w +
                    Complex.log (w + (M : ℂ))) / 2 +
                t +
                Complex.finiteAbelPlanaLogSummandUpperVerticalBoundary N w +
                Complex.finiteAbelPlanaLogEndpointResidueRestoration N w)
            hlower
        _ =
              (((w + (M : ℂ)) *
                    Complex.log (w + (M : ℂ)) -
                  (w + (M : ℂ))) -
              (w * Complex.log w - w)) +
                (Complex.log w +
                  Complex.log (w + (M : ℂ))) / 2 -
              (Complex.binetAbelPlanaFiniteBoundaryCorrection N w +
                Complex.binetAbelPlanaFiniteLowerContourTail N w) +
              Complex.finiteAbelPlanaLogSummandUpperVerticalBoundary N w +
              Complex.finiteAbelPlanaLogEndpointResidueRestoration N w := by
          exact congrArg
            (fun t : ℂ =>
                (((w + (M : ℂ)) *
                      Complex.log (w + (M : ℂ)) -
                    (w + (M : ℂ))) -
                (w * Complex.log w - w)) +
                  (Complex.log w +
                    Complex.log (w + (M : ℂ))) / 2 -
                t +
                Complex.finiteAbelPlanaLogSummandUpperVerticalBoundary N w +
                Complex.finiteAbelPlanaLogEndpointResidueRestoration N w)
            hlower_name
        _ =
              (((w + (M : ℂ)) *
                    Complex.log (w + (M : ℂ)) -
                  (w + (M : ℂ))) -
              (w * Complex.log w - w)) +
                (Complex.log w +
                  Complex.log (w + (M : ℂ))) / 2 -
              (Complex.binetAbelPlanaFiniteBoundaryCorrection N w +
                Complex.binetAbelPlanaFiniteLowerContourTail N w) -
              Complex.finiteAbelPlanaLogSummandUpperVerticalIntegral N w +
              Complex.finiteAbelPlanaLogEndpointResidueRestoration N w := by
          exact congrArg
            (fun t : ℂ =>
                (((w + (M : ℂ)) *
                      Complex.log (w + (M : ℂ)) -
                    (w + (M : ℂ))) -
                (w * Complex.log w - w)) +
                  (Complex.log w +
                    Complex.log (w + (M : ℂ))) / 2 -
                (Complex.binetAbelPlanaFiniteBoundaryCorrection N w +
                  Complex.binetAbelPlanaFiniteLowerContourTail N w) +
                t +
                Complex.finiteAbelPlanaLogEndpointResidueRestoration N w)
            hupper
        _ =
            (((w + (M : ℂ)) *
                  Complex.log (w + (M : ℂ)) -
                (w + (M : ℂ))) -
              (w * Complex.log w - w)) +
              (Complex.log w +
                Complex.log (w + (M : ℂ))) / 2 -
              (Complex.binetAbelPlanaFiniteBoundaryCorrection N w +
                Complex.binetAbelPlanaFiniteLowerContourTail N w) -
              Complex.binetAbelPlanaFiniteUpperContourResidual N w +
              Complex.finiteAbelPlanaLogEndpointResidueRestoration N w := by
          exact congrArg
            (fun t : ℂ =>
              (((w + (M : ℂ)) *
                    Complex.log (w + (M : ℂ)) -
                  (w + (M : ℂ))) -
                (w * Complex.log w - w)) +
                (Complex.log w +
                  Complex.log (w + (M : ℂ))) / 2 -
                (Complex.binetAbelPlanaFiniteBoundaryCorrection N w +
                  Complex.binetAbelPlanaFiniteLowerContourTail N w) -
                t +
                Complex.finiteAbelPlanaLogEndpointResidueRestoration N w)
            hupper_name
        _ =
              (((w + (M : ℂ)) * Complex.log (w + (M : ℂ)) -
                  (w + (M : ℂ))) -
              (w * Complex.log w - w)) +
                (Complex.log w + Complex.log (w + (M : ℂ))) / 2 -
              Complex.binetAbelPlanaFiniteBoundaryCorrection N w -
              Complex.binetAbelPlanaFiniteLowerContourTail N w -
              Complex.binetAbelPlanaFiniteUpperContourResidual N w +
              Complex.finiteAbelPlanaLogEndpointResidueRestoration N w := by
          exact
            Complex.add_sub_add_sub_add_eq_add_sub_sub_sub_add
                ((((w + (M : ℂ)) *
                      Complex.log (w + (M : ℂ)) -
                    (w + (M : ℂ))) -
                (w * Complex.log w - w)))
                ((Complex.log w +
                  Complex.log (w + (M : ℂ))) / 2)
              (Complex.binetAbelPlanaFiniteBoundaryCorrection N w)
              (Complex.binetAbelPlanaFiniteLowerContourTail N w)
              (Complex.binetAbelPlanaFiniteUpperContourResidual N w)
              (Complex.finiteAbelPlanaLogEndpointResidueRestoration N w)

/-- Endpoint indentation and endpoint restoration are the same half-endpoint
normalization term. -/
theorem Complex.finiteAbelPlana_log_endpointPVIndentation_eq_endpointRestoration
    (N : ℕ)
    (w : ℂ) :
    Complex.finiteAbelPlanaLogEndpointPVIndentationContribution N w =
      Complex.finiteAbelPlanaLogEndpointResidueRestoration N w := by
  calc
    Complex.finiteAbelPlanaLogEndpointPVIndentationContribution N w =
        Complex.finiteAbelPlanaLogSummandHalfEndpoints N w := by
      exact Complex.finiteAbelPlana_log_endpointPVIndentationContribution_unfold N w
    _ = Complex.finiteAbelPlanaLogEndpointResidueRestoration N w := by
      rfl

/-- Endpoint-restored principal-value cotangent formula.  The endpoint
indentation carried by the restored finite-height package is exactly the
ordinary endpoint restoration term. -/
theorem Complex.finiteAbelPlana_log_principalValueCotangentFormula_endpointRestored
    {w : ℂ}
    (hw : 0 < w.re)
    (hbridges : Complex.FiniteHeightPVBridgePackageEndpointRestored w) :
    ∀ N : ℕ,
      (∀ n : ℕ, n ∈ Finset.range N →
        ∀ z : ℂ, Decidable (z = ((n + 1 : ℕ) : ℂ))) →
      Complex.finiteAbelPlanaLogBoundaryNamedPieces N w =
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w +
          Complex.finiteAbelPlanaLogEndpointResidueRestoration N w := by
  intro N hdecInteriorPole
  let E : ℂ := Complex.finiteAbelPlanaLogEndpointPVIndentationContribution N w
  have hboundary :
      Filter.Tendsto
        (fun T : ℝ =>
          Complex.finiteAbelPlanaLogBoundaryNamedPiecesUpTo N w T)
        Filter.atTop
        (𝓝 (Complex.finiteAbelPlanaLogBoundaryNamedPieces N w)) :=
    Complex.finiteAbelPlana_log_boundaryNamedPiecesUpTo_tendsto_full hw N
  have hrestored_error :
      Filter.Tendsto
        (fun T : ℝ =>
          Complex.finiteAbelPlanaLogFiniteHeightEndpointRestoredContourError N w T)
        Filter.atTop
        (𝓝 (0 : ℂ)) :=
    Complex.finiteAbelPlana_log_finiteHeightEndpointRestoredContourError_tendsto_zero
      hw N hdecInteriorPole (hbridges N)
  have herror_to_endpoint :
      Filter.Tendsto
        (fun T : ℝ => Complex.finiteAbelPlanaLogFiniteHeightContourError N w T)
        Filter.atTop
        (𝓝 E) := by
    have hfun :
        (fun T : ℝ => Complex.finiteAbelPlanaLogFiniteHeightContourError N w T) =
          (fun T : ℝ =>
            Complex.finiteAbelPlanaLogFiniteHeightEndpointRestoredContourError N w T + E) := by
      funext T
      calc
        Complex.finiteAbelPlanaLogFiniteHeightContourError N w T =
            (Complex.finiteAbelPlanaLogFiniteHeightContourError N w T - E) + E := by
          exact (sub_add_cancel
            (Complex.finiteAbelPlanaLogFiniteHeightContourError N w T) E).symm
        _ =
            Complex.finiteAbelPlanaLogFiniteHeightEndpointRestoredContourError N w T + E := by
          rfl
    have hsum :
        Filter.Tendsto
          (fun T : ℝ =>
            Complex.finiteAbelPlanaLogFiniteHeightEndpointRestoredContourError N w T + E)
          Filter.atTop
          (𝓝 (0 + E)) :=
      hrestored_error.add tendsto_const_nhds
    have htarget : 0 + E = E :=
      zero_add E
    have htarget_nhds :
        𝓝 (0 + E) = 𝓝 E :=
      congrArg (fun q : ℂ => 𝓝 q) htarget
    have hsum_endpoint :
        Filter.Tendsto
          (fun T : ℝ =>
            Complex.finiteAbelPlanaLogFiniteHeightEndpointRestoredContourError N w T + E)
          Filter.atTop
          (𝓝 E) :=
      htarget_nhds ▸ hsum
    exact hfun ▸ hsum_endpoint
  have hboundary_to_pv_endpoint :
      Filter.Tendsto
        (fun T : ℝ =>
          Complex.finiteAbelPlanaLogBoundaryNamedPiecesUpTo N w T)
        Filter.atTop
        (𝓝 (Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w + E)) := by
    have hdecomp :
        (fun T : ℝ =>
          Complex.finiteAbelPlanaLogBoundaryNamedPiecesUpTo N w T) =
          (fun T : ℝ =>
            Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w +
              Complex.finiteAbelPlanaLogFiniteHeightContourError N w T) := by
      funext T
      exact
        Complex.finiteAbelPlana_log_boundaryNamedPiecesUpTo_eq_residueSum_add_error
          N w T
    have hsum :
        Filter.Tendsto
          (fun T : ℝ =>
            Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w +
              Complex.finiteAbelPlanaLogFiniteHeightContourError N w T)
          Filter.atTop
          (𝓝 (Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w + E)) :=
      tendsto_const_nhds.add herror_to_endpoint
    exact hdecomp.symm ▸ hsum
  have hboundary_eq :
      Complex.finiteAbelPlanaLogBoundaryNamedPieces N w =
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w + E :=
    tendsto_nhds_unique hboundary hboundary_to_pv_endpoint
  have hendpoint :
      E = Complex.finiteAbelPlanaLogEndpointResidueRestoration N w :=
    Complex.finiteAbelPlana_log_endpointPVIndentation_eq_endpointRestoration N w
  exact Eq.trans hboundary_eq
    (congrArg
      (fun q : ℂ => Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w + q)
      hendpoint)

/-- The named finite Abel-Plana boundary pieces normalize to the Binet finite
main boundary expression. -/
theorem Complex.finiteAbelPlana_log_boundaryNamedPieces_eq_mainBoundaryUpper
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    let M : ℕ := N + 1
    Complex.finiteAbelPlanaLogBoundaryNamedPieces N w =
      (((w + (M : ℂ)) * Complex.log (w + (M : ℂ)) -
          (w + (M : ℂ))) -
        (w * Complex.log w - w)) +
        (Complex.log w + Complex.log (w + (M : ℂ))) / 2 -
        Complex.binetAbelPlanaFiniteBoundaryCorrection N w -
        Complex.binetAbelPlanaFiniteLowerContourTail N w -
          Complex.binetAbelPlanaFiniteUpperContourResidual N w := by
  let M : ℕ := N + 1
  have hboundary :
      Complex.finiteAbelPlanaLogBoundaryNamedPieces N w =
        (∫ x : ℝ in (0 : ℝ)..(M : ℝ),
          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
          Complex.finiteAbelPlanaLogSummandLowerVerticalIntegral N w -
          Complex.finiteAbelPlanaLogSummandUpperVerticalIntegral N w :=
    Complex.finiteAbelPlana_log_boundaryNamedPieces_unfold N w
  have hprimitive :
      (∫ x : ℝ in (0 : ℝ)..(M : ℝ),
          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) =
        (((w + (M : ℂ)) * Complex.log (w + (M : ℂ)) -
            (w + (M : ℂ))) -
          (w * Complex.log w - w)) := by
    exact Eq.trans
      (Complex.finiteAbelPlana_log_summand_realSegmentIntegral_eq_endpointPrimitive
        hw N)
      (Complex.finiteAbelPlanaLogSummandEndpointPrimitive_unfold N w)
  have hhalf :
      Complex.finiteAbelPlanaLogSummandHalfEndpoints N w =
        (Complex.log w + Complex.log (w + (M : ℂ))) / 2 := by
    rfl
  have hlower_name :
      Complex.finiteAbelPlanaLogSummandLowerVerticalIntegral N w =
        Complex.binetAbelPlanaFiniteBoundaryCorrection N w +
          Complex.binetAbelPlanaFiniteLowerContourTail N w := by
    rfl
  have hupper_name :
      Complex.finiteAbelPlanaLogSummandUpperVerticalIntegral N w =
        Complex.binetAbelPlanaFiniteUpperContourResidual N w := by
    rfl
  calc
    Complex.finiteAbelPlanaLogBoundaryNamedPieces N w =
        (∫ x : ℝ in (0 : ℝ)..(M : ℝ),
          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
          Complex.finiteAbelPlanaLogSummandLowerVerticalIntegral N w -
          Complex.finiteAbelPlanaLogSummandUpperVerticalIntegral N w := by
      exact hboundary
    _ =
        (((w + (M : ℂ)) * Complex.log (w + (M : ℂ)) -
            (w + (M : ℂ))) -
          (w * Complex.log w - w)) +
          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
          Complex.finiteAbelPlanaLogSummandLowerVerticalIntegral N w -
          Complex.finiteAbelPlanaLogSummandUpperVerticalIntegral N w := by
      exact congrArg
        (fun t : ℂ =>
          t +
            Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
            Complex.finiteAbelPlanaLogSummandLowerVerticalIntegral N w -
            Complex.finiteAbelPlanaLogSummandUpperVerticalIntegral N w)
        hprimitive
    _ =
        (((w + (M : ℂ)) * Complex.log (w + (M : ℂ)) -
            (w + (M : ℂ))) -
          (w * Complex.log w - w)) +
          (Complex.log w + Complex.log (w + (M : ℂ))) / 2 -
          Complex.finiteAbelPlanaLogSummandLowerVerticalIntegral N w -
          Complex.finiteAbelPlanaLogSummandUpperVerticalIntegral N w := by
      exact congrArg
        (fun t : ℂ =>
          (((w + (M : ℂ)) * Complex.log (w + (M : ℂ)) -
              (w + (M : ℂ))) -
            (w * Complex.log w - w)) +
            t -
            Complex.finiteAbelPlanaLogSummandLowerVerticalIntegral N w -
            Complex.finiteAbelPlanaLogSummandUpperVerticalIntegral N w)
        hhalf
    _ =
        (((w + (M : ℂ)) * Complex.log (w + (M : ℂ)) -
            (w + (M : ℂ))) -
          (w * Complex.log w - w)) +
          (Complex.log w + Complex.log (w + (M : ℂ))) / 2 -
          (Complex.binetAbelPlanaFiniteBoundaryCorrection N w +
            Complex.binetAbelPlanaFiniteLowerContourTail N w) -
          Complex.finiteAbelPlanaLogSummandUpperVerticalIntegral N w := by
      exact congrArg
        (fun t : ℂ =>
          (((w + (M : ℂ)) * Complex.log (w + (M : ℂ)) -
              (w + (M : ℂ))) -
            (w * Complex.log w - w)) +
            (Complex.log w + Complex.log (w + (M : ℂ))) / 2 -
            t -
            Complex.finiteAbelPlanaLogSummandUpperVerticalIntegral N w)
        hlower_name
    _ =
        (((w + (M : ℂ)) * Complex.log (w + (M : ℂ)) -
            (w + (M : ℂ))) -
          (w * Complex.log w - w)) +
          (Complex.log w + Complex.log (w + (M : ℂ))) / 2 -
          (Complex.binetAbelPlanaFiniteBoundaryCorrection N w +
            Complex.binetAbelPlanaFiniteLowerContourTail N w) -
          Complex.binetAbelPlanaFiniteUpperContourResidual N w := by
      exact congrArg
        (fun t : ℂ =>
          (((w + (M : ℂ)) * Complex.log (w + (M : ℂ)) -
              (w + (M : ℂ))) -
            (w * Complex.log w - w)) +
            (Complex.log w + Complex.log (w + (M : ℂ))) / 2 -
            (Complex.binetAbelPlanaFiniteBoundaryCorrection N w +
              Complex.binetAbelPlanaFiniteLowerContourTail N w) -
            t)
        hupper_name
    _ =
        (((w + (M : ℂ)) * Complex.log (w + (M : ℂ)) -
            (w + (M : ℂ))) -
          (w * Complex.log w - w)) +
          (Complex.log w + Complex.log (w + (M : ℂ))) / 2 -
          Complex.binetAbelPlanaFiniteBoundaryCorrection N w -
          Complex.binetAbelPlanaFiniteLowerContourTail N w -
          Complex.binetAbelPlanaFiniteUpperContourResidual N w := by
      exact
        Complex.add_sub_add_sub_eq_add_sub_sub
          ((((w + (M : ℂ)) * Complex.log (w + (M : ℂ)) -
              (w + (M : ℂ))) -
            (w * Complex.log w - w)))
          ((Complex.log w + Complex.log (w + (M : ℂ))) / 2)
          (Complex.binetAbelPlanaFiniteBoundaryCorrection N w)
          (Complex.binetAbelPlanaFiniteLowerContourTail N w)
          (Complex.binetAbelPlanaFiniteUpperContourResidual N w)

/-- Endpoint-restored finite Abel-Plana summation formula for the logarithmic
summand.  In this normalization the endpoint restoration is already part of the
principal-value side, so no extra endpoint term remains on the right. -/
theorem Complex.finiteAbelPlana_log_summand_eq_mainBoundaryUpper_endpointRestored
    {w : ℂ}
    (hw : 0 < w.re)
    (hbridges : Complex.FiniteHeightPVBridgePackageEndpointRestored w) :
    ∀ N : ℕ,
      (∀ n : ℕ, n ∈ Finset.range N →
        ∀ z : ℂ, Decidable (z = ((n + 1 : ℕ) : ℂ))) →
      let M : ℕ := N + 1
      ∑ n in Finset.range (M + 1), Complex.log (w + n) =
        (((w + (M : ℂ)) * Complex.log (w + (M : ℂ)) -
            (w + (M : ℂ))) -
          (w * Complex.log w - w)) +
          (Complex.log w + Complex.log (w + (M : ℂ))) / 2 -
          Complex.binetAbelPlanaFiniteBoundaryCorrection N w -
          Complex.binetAbelPlanaFiniteLowerContourTail N w -
            Complex.binetAbelPlanaFiniteUpperContourResidual N w := by
  intro N hdecInteriorPole
  let M : ℕ := N + 1
  have hsample :
      Complex.finiteAbelPlanaLogIntegerResidueSum N w =
        ∑ n in Finset.range (M + 1),
          Complex.finiteAbelPlanaLogSummand w n :=
    Complex.finiteAbelPlana_log_integerResidueSum_eq_summandRange N w
  have hrestore :
      Complex.finiteAbelPlanaLogIntegerResidueSum N w =
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w +
          Complex.finiteAbelPlanaLogEndpointResidueRestoration N w :=
    Complex.finiteAbelPlana_log_integerResidueSum_eq_pvResidue_add_endpointRestoration
      N w
  have hboundary_residue :
      Complex.finiteAbelPlanaLogBoundaryNamedPieces N w =
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w +
          Complex.finiteAbelPlanaLogEndpointResidueRestoration N w :=
    Complex.finiteAbelPlana_log_principalValueCotangentFormula_endpointRestored
      hw hbridges N hdecInteriorPole
  have hsample_boundary :
      ∑ n in Finset.range (M + 1), Complex.log (w + n) =
        Complex.finiteAbelPlanaLogBoundaryNamedPieces N w := by
    calc
      ∑ n in Finset.range (M + 1), Complex.log (w + n) =
          Complex.finiteAbelPlanaLogIntegerResidueSum N w := by
        exact hsample.symm
      _ =
          Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w +
            Complex.finiteAbelPlanaLogEndpointResidueRestoration N w := by
        exact hrestore
      _ = Complex.finiteAbelPlanaLogBoundaryNamedPieces N w := by
        exact hboundary_residue.symm
  have hboundary_main :
      Complex.finiteAbelPlanaLogBoundaryNamedPieces N w =
        (((w + (M : ℂ)) * Complex.log (w + (M : ℂ)) -
            (w + (M : ℂ))) -
          (w * Complex.log w - w)) +
          (Complex.log w + Complex.log (w + (M : ℂ))) / 2 -
          Complex.binetAbelPlanaFiniteBoundaryCorrection N w -
          Complex.binetAbelPlanaFiniteLowerContourTail N w -
            Complex.binetAbelPlanaFiniteUpperContourResidual N w :=
    Complex.finiteAbelPlana_log_boundaryNamedPieces_eq_mainBoundaryUpper hw N
  exact hsample_boundary.trans hboundary_main

end

end LFunctions
end Boundary
