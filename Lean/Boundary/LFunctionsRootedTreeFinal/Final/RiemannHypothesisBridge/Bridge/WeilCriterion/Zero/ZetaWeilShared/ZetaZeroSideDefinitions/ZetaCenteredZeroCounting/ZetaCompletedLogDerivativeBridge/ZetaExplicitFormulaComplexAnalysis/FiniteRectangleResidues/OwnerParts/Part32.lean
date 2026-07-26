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
          explicitFormulaCompletedZeroContourHeightWindowResidueSum f
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
          explicitFormulaCompletedZeroContourHeightWindowResidueSum f
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
          explicitFormulaCompletedZeroContourHeightWindowResidueSum f
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

/-- Core finite-rectangle vertical zero-side theorem with fixed-degree scheduled
horizontal decay. -/
theorem explicitFormulaFamilyVerticalZeroSideWindowError_tendsto_zero_of_polynomialScheduledPackage_ownerFiniteRectangleResidueTheorem
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hPoly : ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage f F)
    (hschedule : hPoly.height_schedule = h.height_schedule)
    (hfinite :
      ∀ u : ℝ,
        zetaCompletedExplicitFormulaContourIntegral f
            (F.rectangle (h.height_schedule.height u)) =
          explicitFormulaCompletedZeroContourHeightWindowResidueSum f
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
  have hhorizontalPoly :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyHorizontalResidueWindowError f F
            (hPoly.height_schedule.height u))
        atTop
        (𝓝 0) :=
    explicitFormulaFamilyHorizontalResidueWindowError_tendsto_zero_of_polynomialScheduledPackage
      f F hPoly
  have hscheduleFunction :
      (fun u : ℝ =>
          explicitFormulaFamilyHorizontalResidueWindowError f F
            (hPoly.height_schedule.height u)) =
        (fun u : ℝ =>
          explicitFormulaFamilyHorizontalResidueWindowError f F
            (h.height_schedule.height u)) :=
    congrArg
      (fun schedule : ExplicitFormulaCofinalHeightSchedule F =>
        fun u : ℝ =>
          explicitFormulaFamilyHorizontalResidueWindowError f F
            (schedule.height u))
      hschedule
  have hhorizontal :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyHorizontalResidueWindowError f F
            (h.height_schedule.height u))
        atTop
        (𝓝 0) :=
    Eq.subst
      (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
      hscheduleFunction
      hhorizontalPoly
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
          explicitFormulaCompletedZeroContourHeightWindowResidueSum f
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
          explicitFormulaCompletedZeroContourHeightWindowResidueSum f
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

/-- The vertical residue-window error vanishes with fixed-degree scheduled
horizontal decay. -/
theorem explicitFormulaFamilyVerticalResidueWindowError_tendsto_zero_of_polynomialScheduledPackage_ownerFiniteRectangleResidueTheorem
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hPoly : ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage f F)
    (hschedule : hPoly.height_schedule = h.height_schedule)
    (hfinite :
      ∀ u : ℝ,
        zetaCompletedExplicitFormulaContourIntegral f
            (F.rectangle (h.height_schedule.height u)) =
          explicitFormulaCompletedZeroContourHeightWindowResidueSum f
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
    explicitFormulaFamilyVerticalZeroSideWindowError_tendsto_zero_of_polynomialScheduledPackage_ownerFiniteRectangleResidueTheorem
      f F h hPoly hschedule hfinite
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
          explicitFormulaCompletedZeroContourHeightWindowResidueSum f
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

/-- The residue-window limit after the finite vertical-residue calculation has been
discharged.  This is the canonical analytic assembly point: the remaining horizontal
term is supplied by the independent scheduled decay theorem. -/
theorem explicitFormulaFamilyResidueWindowError_tendsto_zero_of_verticalResidueLimit_ownerResidueCalculus
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hvertical :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyVerticalResidueWindowError f F
            (h.height_schedule.height u))
        atTop
        (𝓝 0))
    (hhorizontal :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyHorizontalResidueWindowError f F
            (h.height_schedule.height u))
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaFamilyResidueWindowError f F
          (h.height_schedule.height u))
      atTop
      (𝓝 0) :=
  explicitFormulaFamilyResidueWindowError_tendsto_zero_of_scheduled_vertical_and_horizontal
    f F h hvertical hhorizontal

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
          explicitFormulaCompletedZeroContourHeightWindowResidueSum f
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
