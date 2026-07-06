import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part31

/-!
# Explicit-formula finite rectangle residues

This owner layer contains finite-rectangle residue equalities, scheduled avoidance, and residue-window error transport.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology

namespace ZetaAdmissibleFunction

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
          explicitFormulaCompletedZeroHeightWindowResidueSum f
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
          explicitFormulaCompletedZeroHeightWindowResidueSum f
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
          explicitFormulaCompletedZeroHeightWindowResidueSum f
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

/-- Core finite-rectangle contour residue theorem, after zero-excision/window accounting.

The scheduled finite-rectangle residue equality controls the contour-minus-residue error,
and the finite zero-window accounting error is identically zero. -/
theorem explicitFormulaFamilyContourZeroSideWindowError_tendsto_zero_core_ownerFiniteRectangleResidueTheorem
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hfinite :
      ∀ u : ℝ,
        zetaCompletedExplicitFormulaContourIntegral f
            (F.rectangle (h.height_schedule.height u)) =
          explicitFormulaCompletedZeroHeightWindowResidueSum f
            (h.height_schedule.height u)) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaFamilyContourZeroSideWindowError f F
          (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  have hresidue :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledRectangleResidueEqualityError f F h u)
        atTop
        (𝓝 0) :=
    explicitFormulaScheduledRectangleResidueEqualityError_tendsto_zero_core_ownerFiniteRectangleResidueEquality
      f F h hfinite
  have hwindow :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledZeroWindowAccountingError f F h u)
        atTop
        (𝓝 0) :=
    explicitFormulaScheduledZeroWindowAccountingError_tendsto_zero f F h
  have hsum :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledRectangleResidueEqualityError f F h u +
            explicitFormulaScheduledZeroWindowAccountingError f F h u)
        atTop
        (𝓝 (0 + 0 : ℂ)) :=
    hresidue.add hwindow
  have htarget : (0 + 0 : ℂ) = 0 :=
    add_zero 0
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaFamilyContourZeroSideWindowError f F
          (h.height_schedule.height u)) =
        (fun u : ℝ =>
          explicitFormulaScheduledRectangleResidueEqualityError f F h u +
            explicitFormulaScheduledZeroWindowAccountingError f F h u) := by
    exact funext
      (fun u : ℝ =>
        explicitFormulaFamilyContourZeroSideWindowError_scheduled_eq_residueEquality_add_accounting
          f F h u)
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            explicitFormulaScheduledRectangleResidueEqualityError f F h u +
              explicitFormulaScheduledZeroWindowAccountingError f F h u)
          atTop
          (𝓝 z))
      htarget
      hsum)

/-- Core finite-rectangle vertical zero-side theorem.

This is the finite-rectangle residue-calculus input after zero-excision/window
normalization and after removing the horizontal contour sides: the right-minus-left
vertical side differs from the finite zero-side window by an error tending to zero. -/
theorem explicitFormulaFamilyVerticalZeroSideWindowError_tendsto_zero_core_ownerFiniteRectangleResidueTheorem
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (T x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath (F.rectangle T) x ∈ E.carrier)
    (hBottomMem :
      ∀ (T x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x ∈ E.carrier)
    (N : ℕ)
    (hfinite :
      ∀ u : ℝ,
        zetaCompletedExplicitFormulaContourIntegral f
            (F.rectangle (h.height_schedule.height u)) =
          explicitFormulaCompletedZeroHeightWindowResidueSum f
            (h.height_schedule.height u)) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaFamilyVerticalZeroSideWindowError f F
          (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  have hcontour :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyContourZeroSideWindowError f F
            (h.height_schedule.height u))
        atTop
        (𝓝 0) :=
    explicitFormulaFamilyContourZeroSideWindowError_tendsto_zero_core_ownerFiniteRectangleResidueTheorem
      f F h hfinite
  have hhorizontal :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyHorizontalResidueWindowError f F
            (h.height_schedule.height u))
        atTop
        (𝓝 0) :=
    explicitFormulaFamilyHorizontalResidueWindowError_tendsto_zero_scheduled
      f F h E hTopMem hBottomMem N
  have hsub :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyContourZeroSideWindowError f F
              (h.height_schedule.height u) -
            explicitFormulaFamilyHorizontalResidueWindowError f F
              (h.height_schedule.height u))
        atTop
        (𝓝 (0 - 0 : ℂ)) :=
    hcontour.sub hhorizontal
  have htarget : (0 - 0 : ℂ) = 0 :=
    sub_self 0
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaFamilyVerticalZeroSideWindowError f F
          (h.height_schedule.height u)) =
        (fun u : ℝ =>
          explicitFormulaFamilyContourZeroSideWindowError f F
              (h.height_schedule.height u) -
            explicitFormulaFamilyHorizontalResidueWindowError f F
              (h.height_schedule.height u)) := by
    exact funext
      (fun u : ℝ =>
        explicitFormulaFamilyVerticalZeroSideWindowError_eq_contourZeroSide_sub_horizontal
          f F (h.height_schedule.height u))
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            explicitFormulaFamilyContourZeroSideWindowError f F
                (h.height_schedule.height u) -
              explicitFormulaFamilyHorizontalResidueWindowError f F
                (h.height_schedule.height u))
          atTop
          (𝓝 z))
      htarget
      hsub)

/-- Core finite-rectangle vertical zero-side theorem using the analytic package's
scheduled horizontal carrier. -/
theorem explicitFormulaFamilyVerticalZeroSideWindowError_tendsto_zero_of_scheduledCarrier_ownerFiniteRectangleResidueTheorem
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (N : ℕ)
    (hfinite :
      ∀ u : ℝ,
        zetaCompletedExplicitFormulaContourIntegral f
            (F.rectangle (h.height_schedule.height u)) =
          explicitFormulaCompletedZeroHeightWindowResidueSum f
            (h.height_schedule.height u)) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaFamilyVerticalZeroSideWindowError f F
          (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  have hcontour :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyContourZeroSideWindowError f F
            (h.height_schedule.height u))
        atTop
        (𝓝 0) :=
    explicitFormulaFamilyContourZeroSideWindowError_tendsto_zero_core_ownerFiniteRectangleResidueTheorem
      f F h hfinite
  have hhorizontal :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyHorizontalResidueWindowError f F
            (h.height_schedule.height u))
        atTop
        (𝓝 0) :=
    explicitFormulaFamilyHorizontalResidueWindowError_tendsto_zero_of_scheduledCarrier
      f F h N
  have hsub :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyContourZeroSideWindowError f F
              (h.height_schedule.height u) -
            explicitFormulaFamilyHorizontalResidueWindowError f F
              (h.height_schedule.height u))
        atTop
        (𝓝 (0 - 0 : ℂ)) :=
    hcontour.sub hhorizontal
  have htarget : (0 - 0 : ℂ) = 0 :=
    sub_self 0
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaFamilyVerticalZeroSideWindowError f F
          (h.height_schedule.height u)) =
        (fun u : ℝ =>
          explicitFormulaFamilyContourZeroSideWindowError f F
              (h.height_schedule.height u) -
            explicitFormulaFamilyHorizontalResidueWindowError f F
              (h.height_schedule.height u)) := by
    exact funext
      (fun u : ℝ =>
        explicitFormulaFamilyVerticalZeroSideWindowError_eq_contourZeroSide_sub_horizontal
          f F (h.height_schedule.height u))
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            explicitFormulaFamilyContourZeroSideWindowError f F
                (h.height_schedule.height u) -
              explicitFormulaFamilyHorizontalResidueWindowError f F
                (h.height_schedule.height u))
          atTop
          (𝓝 z))
      htarget
      hsub)

/-- The vertical residue-window error vanishes by zero-excision/window equality from the
zero-side finite-rectangle residue theorem. -/
theorem explicitFormulaFamilyVerticalResidueWindowError_tendsto_zero_core_ownerFiniteRectangleResidueTheorem
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (T x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath (F.rectangle T) x ∈ E.carrier)
    (hBottomMem :
      ∀ (T x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x ∈ E.carrier)
    (N : ℕ)
    (hfinite :
      ∀ u : ℝ,
        zetaCompletedExplicitFormulaContourIntegral f
            (F.rectangle (h.height_schedule.height u)) =
          explicitFormulaCompletedZeroHeightWindowResidueSum f
            (h.height_schedule.height u)) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaFamilyVerticalResidueWindowError f F
          (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  have hzeroSide :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyVerticalZeroSideWindowError f F
            (h.height_schedule.height u))
        atTop
        (𝓝 0) :=
    explicitFormulaFamilyVerticalZeroSideWindowError_tendsto_zero_core_ownerFiniteRectangleResidueTheorem
      f F h E hTopMem hBottomMem N hfinite
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaFamilyVerticalResidueWindowError f F
          (h.height_schedule.height u)) =
        (fun u : ℝ =>
          explicitFormulaFamilyVerticalZeroSideWindowError f F
            (h.height_schedule.height u)) := by
    exact funext
      (fun u : ℝ =>
        explicitFormulaFamilyVerticalResidueWindowError_eq_zeroSideWindowError
          f F (h.height_schedule.height u))
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    hzeroSide

/-- The vertical residue-window error vanishes using the analytic package's scheduled
horizontal carrier. -/
theorem explicitFormulaFamilyVerticalResidueWindowError_tendsto_zero_of_scheduledCarrier_ownerFiniteRectangleResidueTheorem
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (N : ℕ)
    (hfinite :
      ∀ u : ℝ,
        zetaCompletedExplicitFormulaContourIntegral f
            (F.rectangle (h.height_schedule.height u)) =
          explicitFormulaCompletedZeroHeightWindowResidueSum f
            (h.height_schedule.height u)) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaFamilyVerticalResidueWindowError f F
          (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  have hzeroSide :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyVerticalZeroSideWindowError f F
            (h.height_schedule.height u))
        atTop
        (𝓝 0) :=
    explicitFormulaFamilyVerticalZeroSideWindowError_tendsto_zero_of_scheduledCarrier_ownerFiniteRectangleResidueTheorem
      f F h N hfinite
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaFamilyVerticalResidueWindowError f F
          (h.height_schedule.height u)) =
        (fun u : ℝ =>
          explicitFormulaFamilyVerticalZeroSideWindowError f F
            (h.height_schedule.height u)) := by
    exact funext
      (fun u : ℝ =>
        explicitFormulaFamilyVerticalResidueWindowError_eq_zeroSideWindowError
          f F (h.height_schedule.height u))
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    hzeroSide

/-- Core finite-rectangle residue-calculus error theorem.

The full contour residue-window error splits into the vertical finite-residue error plus
the horizontal side error.  The finite-rectangle residue theorem controls the former, and
horizontal edge decay controls the latter. -/
theorem explicitFormulaFamilyResidueWindowError_tendsto_zero_core_ownerResidueCalculus
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (T x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath (F.rectangle T) x ∈ E.carrier)
    (hBottomMem :
      ∀ (T x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x ∈ E.carrier)
    (N : ℕ)
    (hfinite :
      ∀ u : ℝ,
        zetaCompletedExplicitFormulaContourIntegral f
            (F.rectangle (h.height_schedule.height u)) =
          explicitFormulaCompletedZeroHeightWindowResidueSum f
            (h.height_schedule.height u)) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaFamilyResidueWindowError f F
          (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  have hvertical :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyVerticalResidueWindowError f F
            (h.height_schedule.height u))
        atTop
        (𝓝 0) :=
    explicitFormulaFamilyVerticalResidueWindowError_tendsto_zero_core_ownerFiniteRectangleResidueTheorem
      f F h E hTopMem hBottomMem N hfinite
  have hhorizontal :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyHorizontalResidueWindowError f F
            (h.height_schedule.height u))
        atTop
        (𝓝 0) :=
    explicitFormulaFamilyHorizontalResidueWindowError_tendsto_zero_scheduled
      f F h E hTopMem hBottomMem N
  have hsum :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyVerticalResidueWindowError f F
              (h.height_schedule.height u) +
            explicitFormulaFamilyHorizontalResidueWindowError f F
              (h.height_schedule.height u))
        atTop
        (𝓝 (0 + 0 : ℂ)) :=
    hvertical.add hhorizontal
  have htarget : (0 + 0 : ℂ) = 0 :=
    add_zero 0
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaFamilyResidueWindowError f F
          (h.height_schedule.height u)) =
        (fun u : ℝ =>
          explicitFormulaFamilyVerticalResidueWindowError f F
              (h.height_schedule.height u) +
            explicitFormulaFamilyHorizontalResidueWindowError f F
              (h.height_schedule.height u)) := by
    exact funext
      (fun u : ℝ =>
        explicitFormulaFamilyResidueWindowError_eq_vertical_add_horizontal
          f F (h.height_schedule.height u))
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            explicitFormulaFamilyVerticalResidueWindowError f F
                (h.height_schedule.height u) +
              explicitFormulaFamilyHorizontalResidueWindowError f F
                (h.height_schedule.height u))
          atTop
          (𝓝 z))
      htarget
      hsum)

/-- Core finite-rectangle residue-calculus error theorem using the analytic package's
scheduled horizontal carrier. -/
theorem explicitFormulaFamilyResidueWindowError_tendsto_zero_of_scheduledCarrier_core_ownerResidueCalculus
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (N : ℕ)
    (hfinite :
      ∀ u : ℝ,
        zetaCompletedExplicitFormulaContourIntegral f
            (F.rectangle (h.height_schedule.height u)) =
          explicitFormulaCompletedZeroHeightWindowResidueSum f
            (h.height_schedule.height u)) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaFamilyResidueWindowError f F
          (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  have hvertical :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyVerticalResidueWindowError f F
            (h.height_schedule.height u))
        atTop
        (𝓝 0) :=
    explicitFormulaFamilyVerticalResidueWindowError_tendsto_zero_of_scheduledCarrier_ownerFiniteRectangleResidueTheorem
      f F h N hfinite
  have hhorizontal :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyHorizontalResidueWindowError f F
            (h.height_schedule.height u))
        atTop
        (𝓝 0) :=
    explicitFormulaFamilyHorizontalResidueWindowError_tendsto_zero_of_scheduledCarrier
      f F h N
  have hsum :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyVerticalResidueWindowError f F
              (h.height_schedule.height u) +
            explicitFormulaFamilyHorizontalResidueWindowError f F
              (h.height_schedule.height u))
        atTop
        (𝓝 (0 + 0 : ℂ)) :=
    hvertical.add hhorizontal
  have htarget : (0 + 0 : ℂ) = 0 :=
    add_zero 0
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaFamilyResidueWindowError f F
          (h.height_schedule.height u)) =
        (fun u : ℝ =>
          explicitFormulaFamilyVerticalResidueWindowError f F
              (h.height_schedule.height u) +
            explicitFormulaFamilyHorizontalResidueWindowError f F
              (h.height_schedule.height u)) := by
    exact funext
      (fun u : ℝ =>
        explicitFormulaFamilyResidueWindowError_eq_vertical_add_horizontal
          f F (h.height_schedule.height u))
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            explicitFormulaFamilyVerticalResidueWindowError f F
                (h.height_schedule.height u) +
              explicitFormulaFamilyHorizontalResidueWindowError f F
                (h.height_schedule.height u))
          atTop
          (𝓝 z))
      htarget
      hsum)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
