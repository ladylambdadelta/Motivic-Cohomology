import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part31
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ProjectionCore

/-!
# Explicit-formula projected contour spine

This owner layer keeps selected-channel projection transport separate from the
finite-rectangle residue-calculus path.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology

namespace ZetaAdmissibleFunction

/-! ## Projected contour spine for vertical channels -/

/-- The scheduled rectangle residue-equality error, viewed as a contour-side input to a
selected vertical channel projection. -/
noncomputable def explicitFormulaScheduledProjectedRectangleResidueEqualityError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (_channel : ExplicitFormulaScheduledVerticalChannelProjection) : ℂ :=
  explicitFormulaScheduledRectangleResidueEqualityError f F h u

/-- The scheduled horizontal contour error, viewed as an input to a selected vertical channel
projection. -/
noncomputable def explicitFormulaScheduledProjectedHorizontalError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (_channel : ExplicitFormulaScheduledVerticalChannelProjection) : ℂ :=
  explicitFormulaFamilyHorizontalResidueWindowError f F
    (h.height_schedule.height u)

/-- The full projected contour spine error combines finite rectangle residue equality,
projected horizontal decay, and projected vertical decomposition. -/
noncomputable def explicitFormulaScheduledProjectedContourSpineError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection) : ℂ :=
  explicitFormulaScheduledProjectedRectangleResidueEqualityError f F h u channel +
    explicitFormulaScheduledProjectedHorizontalError f F h u channel +
      explicitFormulaScheduledProjectedVerticalDecompositionError f F h u channel

/-- Projecting the finite scheduled rectangle residue equality introduces no new algebra. -/
theorem explicitFormulaScheduledProjectedRectangleResidueEqualityError_eq_rectangleError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection) :
    explicitFormulaScheduledProjectedRectangleResidueEqualityError f F h u channel =
      explicitFormulaScheduledRectangleResidueEqualityError f F h u := by
  exact Eq.refl _

/-- The projected finite rectangle residue-equality error vanishes along the scheduled
boundary-avoiding rectangles. -/
theorem explicitFormulaScheduledProjectedRectangleResidueEqualityError_tendsto_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection)
    (hfinite :
      ∀ u : ℝ,
        zetaCompletedExplicitFormulaContourIntegral f
            (F.rectangle (h.height_schedule.height u)) =
          explicitFormulaCompletedZeroContourHeightWindowResidueSum f
            (h.height_schedule.height u)) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaScheduledProjectedRectangleResidueEqualityError f F h u channel)
      atTop
      (𝓝 0) := by
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaScheduledProjectedRectangleResidueEqualityError f F h u channel) =
        (fun u : ℝ =>
          explicitFormulaScheduledRectangleResidueEqualityError f F h u) := by
    exact funext
      (fun u : ℝ =>
        explicitFormulaScheduledProjectedRectangleResidueEqualityError_eq_rectangleError
          f F h u channel)
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    (explicitFormulaScheduledRectangleResidueEqualityError_tendsto_zero_core_ownerFiniteRectangleResidueEquality
      f F h hfinite)

/-- Projected horizontal decay for a selected vertical channel. -/
theorem explicitFormulaScheduledProjectedHorizontalError_tendsto_zero_ownerProjectedHorizontalDecay
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (E : CompletedZetaZeroExcisedStrip
      (min F.toContourFamily.c (1 - F.toContourFamily.c))
      (max F.toContourFamily.c (1 - F.toContourFamily.c)))
    (hTopMem :
      ∀ (T x : ℝ), x ∈ Set.uIcc F.toContourFamily.c (1 - F.toContourFamily.c) →
        zetaCompletedExplicitFormulaTopPath (F.toContourFamily.rectangle T) x ∈ E.carrier)
    (hBottomMem :
      ∀ (T x : ℝ), x ∈ Set.uIcc F.toContourFamily.c (1 - F.toContourFamily.c) →
        zetaCompletedExplicitFormulaBottomPath (F.toContourFamily.rectangle T) x ∈ E.carrier)
    (N : ℕ)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaScheduledProjectedHorizontalError
          f F.toContourFamily h u channel)
      atTop
      (𝓝 0) := by
  exact
    explicitFormulaFamilyHorizontalResidueWindowError_tendsto_zero_scheduled
      f F.toContourFamily h E hTopMem hBottomMem N

/-- Projected horizontal decay for a selected vertical channel, using the scheduled
horizontal carrier constructed by the analytic package. -/
theorem explicitFormulaScheduledProjectedHorizontalError_tendsto_zero_of_scheduledCarrier
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (N : ℕ)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaScheduledProjectedHorizontalError
          f F.toContourFamily h u channel)
      atTop
      (𝓝 0) := by
  exact
    explicitFormulaFamilyHorizontalResidueWindowError_tendsto_zero_of_scheduledCarrier
      f F.toContourFamily h N

/-- The projected contour spine error vanishes once the three owner inputs are supplied:
scheduled rectangle residue equality, projected horizontal decay, and projected vertical
decomposition. -/
theorem explicitFormulaScheduledProjectedContourSpineError_tendsto_zero_ownerProjectedContourSpine
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection)
    (E : CompletedZetaZeroExcisedStrip
      (min F.toContourFamily.c (1 - F.toContourFamily.c))
      (max F.toContourFamily.c (1 - F.toContourFamily.c)))
    (hTopMem :
      ∀ (T x : ℝ), x ∈ Set.uIcc F.toContourFamily.c (1 - F.toContourFamily.c) →
        zetaCompletedExplicitFormulaTopPath (F.toContourFamily.rectangle T) x ∈ E.carrier)
    (hBottomMem :
      ∀ (T x : ℝ), x ∈ Set.uIcc F.toContourFamily.c (1 - F.toContourFamily.c) →
        zetaCompletedExplicitFormulaBottomPath (F.toContourFamily.rectangle T) x ∈ E.carrier)
    (N : ℕ)
    (hvertical :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledProjectedVerticalDecompositionError
            f F.toContourFamily h u channel)
        atTop
        (𝓝 0))
    (hfinite :
      ∀ u : ℝ,
        zetaCompletedExplicitFormulaContourIntegral f
            (F.toContourFamily.rectangle (h.height_schedule.height u)) =
          explicitFormulaCompletedZeroContourHeightWindowResidueSum f
            (h.height_schedule.height u)) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaScheduledProjectedContourSpineError
          f F.toContourFamily h u channel)
      atTop
      (𝓝 0) := by
  have hresidue :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledProjectedRectangleResidueEqualityError
            f F.toContourFamily h u channel)
        atTop
        (𝓝 0) :=
    explicitFormulaScheduledProjectedRectangleResidueEqualityError_tendsto_zero
      f F.toContourFamily h channel hfinite
  have hhorizontal :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledProjectedHorizontalError
            f F.toContourFamily h u channel)
        atTop
        (𝓝 0) :=
    explicitFormulaScheduledProjectedHorizontalError_tendsto_zero_ownerProjectedHorizontalDecay
      f F h E hTopMem hBottomMem N channel
  have hsum :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledProjectedRectangleResidueEqualityError
              f F.toContourFamily h u channel +
            explicitFormulaScheduledProjectedHorizontalError
              f F.toContourFamily h u channel +
              explicitFormulaScheduledProjectedVerticalDecompositionError
                f F.toContourFamily h u channel)
        atTop
        (𝓝 (0 + 0 + 0 : ℂ)) :=
    (hresidue.add hhorizontal).add hvertical
  have htarget : (0 + 0 + 0 : ℂ) = 0 := by
    exact Eq.trans (add_zero (0 + 0)) (add_zero 0)
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaScheduledProjectedContourSpineError
          f F.toContourFamily h u channel) =
        (fun u : ℝ =>
          explicitFormulaScheduledProjectedRectangleResidueEqualityError
              f F.toContourFamily h u channel +
            explicitFormulaScheduledProjectedHorizontalError
              f F.toContourFamily h u channel +
              explicitFormulaScheduledProjectedVerticalDecompositionError
                f F.toContourFamily h u channel) := by
    exact funext (fun u : ℝ => Eq.refl _)
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            explicitFormulaScheduledProjectedRectangleResidueEqualityError
                f F.toContourFamily h u channel +
              explicitFormulaScheduledProjectedHorizontalError
                f F.toContourFamily h u channel +
                explicitFormulaScheduledProjectedVerticalDecompositionError
                  f F.toContourFamily h u channel)
          atTop
          (𝓝 z))
      htarget
      hsum)

/-- The projected contour spine error vanishes using the analytic package's constructed
scheduled horizontal carrier. -/
theorem explicitFormulaScheduledProjectedContourSpineError_tendsto_zero_of_scheduledCarrier
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection)
    (N : ℕ)
    (hvertical :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledProjectedVerticalDecompositionError
            f F.toContourFamily h u channel)
        atTop
        (𝓝 0))
    (hfinite :
      ∀ u : ℝ,
        zetaCompletedExplicitFormulaContourIntegral f
            (F.toContourFamily.rectangle (h.height_schedule.height u)) =
          explicitFormulaCompletedZeroContourHeightWindowResidueSum f
            (h.height_schedule.height u)) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaScheduledProjectedContourSpineError
          f F.toContourFamily h u channel)
      atTop
      (𝓝 0) := by
  have hresidue :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledProjectedRectangleResidueEqualityError
            f F.toContourFamily h u channel)
        atTop
        (𝓝 0) :=
    explicitFormulaScheduledProjectedRectangleResidueEqualityError_tendsto_zero
      f F.toContourFamily h channel hfinite
  have hhorizontal :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledProjectedHorizontalError
            f F.toContourFamily h u channel)
        atTop
        (𝓝 0) :=
    explicitFormulaScheduledProjectedHorizontalError_tendsto_zero_of_scheduledCarrier
      f F h N channel
  have hsum :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledProjectedRectangleResidueEqualityError
              f F.toContourFamily h u channel +
            explicitFormulaScheduledProjectedHorizontalError
              f F.toContourFamily h u channel +
              explicitFormulaScheduledProjectedVerticalDecompositionError
                f F.toContourFamily h u channel)
        atTop
        (𝓝 (0 + 0 + 0 : ℂ)) :=
    (hresidue.add hhorizontal).add hvertical
  have htarget : (0 + 0 + 0 : ℂ) = 0 := by
    exact Eq.trans (add_zero (0 + 0)) (add_zero 0)
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaScheduledProjectedContourSpineError
          f F.toContourFamily h u channel) =
        (fun u : ℝ =>
          explicitFormulaScheduledProjectedRectangleResidueEqualityError
              f F.toContourFamily h u channel +
            explicitFormulaScheduledProjectedHorizontalError
              f F.toContourFamily h u channel +
              explicitFormulaScheduledProjectedVerticalDecompositionError
                f F.toContourFamily h u channel) := by
    exact funext (fun u : ℝ => Eq.refl _)
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            explicitFormulaScheduledProjectedRectangleResidueEqualityError
                f F.toContourFamily h u channel +
              explicitFormulaScheduledProjectedHorizontalError
                f F.toContourFamily h u channel +
                explicitFormulaScheduledProjectedVerticalDecompositionError
                  f F.toContourFamily h u channel)
          atTop
          (𝓝 z))
      htarget
      hsum)

/-- The shared selected-channel transport theorem is a thin wrapper over a supplied
projected vertical-decomposition input. -/
theorem explicitFormulaScheduledVerticalChannelProjectionTransportRemainder_tendsto_zero_ownerProjectedContourSpine
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection)
    (hvertical :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledProjectedVerticalDecompositionError
            f F.toContourFamily h u channel)
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaScheduledVerticalChannelProjectionTransportRemainder
          f F.toContourFamily (h.height_schedule.height u) channel)
      atTop
      (𝓝 0) := by
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaScheduledVerticalChannelProjectionTransportRemainder
          f F.toContourFamily (h.height_schedule.height u) channel) =
        (fun u : ℝ =>
          explicitFormulaScheduledProjectedVerticalDecompositionError
            f F.toContourFamily h u channel) := by
    exact funext (fun u : ℝ => Eq.refl _)
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    hvertical

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
