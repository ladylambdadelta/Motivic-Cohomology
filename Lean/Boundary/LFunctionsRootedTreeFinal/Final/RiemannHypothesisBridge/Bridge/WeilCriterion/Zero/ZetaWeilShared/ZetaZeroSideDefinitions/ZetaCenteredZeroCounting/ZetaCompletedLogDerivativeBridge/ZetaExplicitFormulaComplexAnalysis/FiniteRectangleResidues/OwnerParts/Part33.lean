import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part32

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

/-- Core contour-residue assembly theorem.

This contour-side residue theorem is assembled from finite-rectangle residue calculus,
with the pointwise scheduled primitive
`explicitFormulaScheduledRectangleResidueEqualityError_eq_zero_of_avoidsBoundary_ownerFiniteRectangleResidueEquality`
providing the boundary-avoiding rectangle computation. -/
theorem zetaCompletedExplicitFormulaContourIntegral_tendsto_zeroSideComplex_core_ownerContourResidueTheorem
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
            (h.height_schedule.height u))
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          zetaZeroSideContribution (ρ : ℂ) f)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaContourIntegral f
          (F.rectangle (h.height_schedule.height u)))
      atTop
      (𝓝 (zetaCompletedZeroSideComplex f)) := by
  have hwindow :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaCompletedZeroContourHeightWindowResidueSum f
            (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedZeroSideComplex f)) :=
    (explicitFormulaCompletedZeroContourHeightWindowResidueSum_tendsto_zeroSideComplex_ownerZeroLimit f hsum).comp
      h.height_schedule.cofinal
  have herror :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyResidueWindowError f F
            (h.height_schedule.height u))
        atTop
        (𝓝 0) :=
    explicitFormulaFamilyResidueWindowError_tendsto_zero_core_ownerResidueCalculus f F h
      E hTopMem hBottomMem N hfinite
  have hsum :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaCompletedZeroContourHeightWindowResidueSum f
              (h.height_schedule.height u) +
            explicitFormulaFamilyResidueWindowError f F
              (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedZeroSideComplex f + 0)) :=
    hwindow.add herror
  have htarget :
      zetaCompletedZeroSideComplex f + 0 =
        zetaCompletedZeroSideComplex f :=
    add_zero _
  have hpointwise :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaContourIntegral f
          (F.rectangle (h.height_schedule.height u))) =
      (fun u : ℝ =>
          explicitFormulaCompletedZeroContourHeightWindowResidueSum f
              (h.height_schedule.height u) +
            explicitFormulaFamilyResidueWindowError f F
              (h.height_schedule.height u)) := by
    exact funext
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaContourIntegral_eq_heightWindowResidueSum_add_error
          f F (h.height_schedule.height u))
  exact Eq.subst
    (motive := fun u : ℝ → ℂ =>
      Tendsto u atTop (𝓝 (zetaCompletedZeroSideComplex f)))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            explicitFormulaCompletedZeroContourHeightWindowResidueSum f
                (h.height_schedule.height u) +
              explicitFormulaFamilyResidueWindowError f F
                (h.height_schedule.height u))
          atTop
          (𝓝 z))
      htarget
      hsum)

/-- Core contour-residue assembly theorem using the analytic package's scheduled
horizontal carrier. -/
theorem zetaCompletedExplicitFormulaContourIntegral_tendsto_zeroSideComplex_of_scheduledCarrier_core_ownerContourResidueTheorem
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (N : ℕ)
    (hfinite :
      ∀ u : ℝ,
        zetaCompletedExplicitFormulaContourIntegral f
            (F.rectangle (h.height_schedule.height u)) =
          explicitFormulaCompletedZeroContourHeightWindowResidueSum f
            (h.height_schedule.height u))
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          zetaZeroSideContribution (ρ : ℂ) f)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaContourIntegral f
          (F.rectangle (h.height_schedule.height u)))
      atTop
      (𝓝 (zetaCompletedZeroSideComplex f)) := by
  have hwindow :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaCompletedZeroContourHeightWindowResidueSum f
            (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedZeroSideComplex f)) :=
    (explicitFormulaCompletedZeroContourHeightWindowResidueSum_tendsto_zeroSideComplex_ownerZeroLimit f hsum).comp
      h.height_schedule.cofinal
  have herror :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyResidueWindowError f F
            (h.height_schedule.height u))
        atTop
        (𝓝 0) :=
    explicitFormulaFamilyResidueWindowError_tendsto_zero_of_scheduledCarrier_core_ownerResidueCalculus
      f F h N hfinite
  have hsum :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaCompletedZeroContourHeightWindowResidueSum f
              (h.height_schedule.height u) +
            explicitFormulaFamilyResidueWindowError f F
              (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedZeroSideComplex f + 0)) :=
    hwindow.add herror
  have htarget :
      zetaCompletedZeroSideComplex f + 0 =
        zetaCompletedZeroSideComplex f :=
    add_zero _
  have hpointwise :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaContourIntegral f
          (F.rectangle (h.height_schedule.height u))) =
      (fun u : ℝ =>
          explicitFormulaCompletedZeroContourHeightWindowResidueSum f
              (h.height_schedule.height u) +
            explicitFormulaFamilyResidueWindowError f F
              (h.height_schedule.height u)) := by
    exact funext
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaContourIntegral_eq_heightWindowResidueSum_add_error
          f F (h.height_schedule.height u))
  exact Eq.subst
    (motive := fun u : ℝ → ℂ =>
      Tendsto u atTop (𝓝 (zetaCompletedZeroSideComplex f)))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            explicitFormulaCompletedZeroContourHeightWindowResidueSum f
                (h.height_schedule.height u) +
              explicitFormulaFamilyResidueWindowError f F
                (h.height_schedule.height u))
          atTop
          (𝓝 z))
      htarget
      hsum)

/-- Owner finite-rectangle residue-calculus error theorem.

After the finite completed-zero height-window residue sum is subtracted from the
rectangle contour integral, the residual rectangle error tends to zero along an admissible
contour family. -/
theorem explicitFormulaFamilyResidueWindowError_tendsto_zero_ownerResidueCalculus
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
    (hfinite :
      ∀ u : ℝ,
        zetaCompletedExplicitFormulaContourIntegral f
            (F.toContourFamily.rectangle (h.height_schedule.height u)) =
          explicitFormulaCompletedZeroContourHeightWindowResidueSum f
            (h.height_schedule.height u)) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaFamilyResidueWindowError f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  exact
    explicitFormulaFamilyResidueWindowError_tendsto_zero_core_ownerResidueCalculus
      f F.toContourFamily
      h
      E
      hTopMem
      hBottomMem
      N
      hfinite

/-- Owner finite-rectangle residue-calculus error theorem using the analytic package's
constructed scheduled horizontal carrier. -/
theorem explicitFormulaFamilyResidueWindowError_tendsto_zero_of_scheduledCarrier_ownerResidueCalculus
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (N : ℕ)
    (hfinite :
      ∀ u : ℝ,
        zetaCompletedExplicitFormulaContourIntegral f
            (F.toContourFamily.rectangle (h.height_schedule.height u)) =
          explicitFormulaCompletedZeroContourHeightWindowResidueSum f
            (h.height_schedule.height u)) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaFamilyResidueWindowError f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  exact
    explicitFormulaFamilyResidueWindowError_tendsto_zero_of_scheduledCarrier_core_ownerResidueCalculus
      f F.toContourFamily h N hfinite

/-- The completed-zeta rectangle residue calculus reconstructs the complex zero-side
residue sum from the limiting contour integral. -/
theorem zetaCompletedExplicitFormulaContourIntegral_tendsto_zeroSideComplex_ownerResidueCalculus
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
    (hfinite :
      ∀ u : ℝ,
        zetaCompletedExplicitFormulaContourIntegral f
            (F.toContourFamily.rectangle (h.height_schedule.height u)) =
          explicitFormulaCompletedZeroContourHeightWindowResidueSum f
            (h.height_schedule.height u))
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          zetaZeroSideContribution (ρ : ℂ) f)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaContourIntegral f
          (F.toContourFamily.rectangle (h.height_schedule.height u)))
      atTop
      (𝓝 (zetaCompletedZeroSideComplex f)) := by
  exact
    zetaCompletedExplicitFormulaContourIntegral_tendsto_zeroSideComplex_core_ownerContourResidueTheorem
      f F.toContourFamily
      h
      E
      hTopMem
      hBottomMem
      N
      hfinite
      hsum

/-- The completed-zeta rectangle residue calculus reconstructs the complex zero-side
residue sum using the analytic package's constructed scheduled horizontal carrier. -/
theorem zetaCompletedExplicitFormulaContourIntegral_tendsto_zeroSideComplex_of_scheduledCarrier_ownerResidueCalculus
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (N : ℕ)
    (hfinite :
      ∀ u : ℝ,
        zetaCompletedExplicitFormulaContourIntegral f
            (F.toContourFamily.rectangle (h.height_schedule.height u)) =
          explicitFormulaCompletedZeroContourHeightWindowResidueSum f
            (h.height_schedule.height u))
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          zetaZeroSideContribution (ρ : ℂ) f)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaContourIntegral f
          (F.toContourFamily.rectangle (h.height_schedule.height u)))
      atTop
      (𝓝 (zetaCompletedZeroSideComplex f)) := by
  exact
    zetaCompletedExplicitFormulaContourIntegral_tendsto_zeroSideComplex_of_scheduledCarrier_core_ownerContourResidueTheorem
      f F.toContourFamily
      h
      N
      hfinite
      hsum

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
