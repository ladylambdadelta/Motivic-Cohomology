import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleBoundaryDefect

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open LSeries ArithmeticFunction
open MeasureTheory
open scoped ArithmeticFunction
open scoped Topology

namespace ZetaAdmissibleFunction

/-- Algebraic assembly of the two true left-zero analytic estimates.

The inputs are exactly the two upstream estimates exposed by the Cauchy
rectangle identity: the residue/boundary defect and the isolated `s = 0`
horizontal remainder.  This lemma contains no analytic shortcut; it only
transports those two bounds through the already proved boundary decomposition. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPole_scheduledRectangleCauchyCancellation_of_boundaryDefect_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (A B : ℝ)
    (hApos : 0 < A)
    (hBpos : 0 < B)
    (hboundary :
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u) -
          zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
            f F (h.height_schedule.height u)‖
          ≤ A *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)))
    (hhorizontal :
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
          f F h u‖
          ≤ ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖ +
            B *
              (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
          f F h u‖
          ≤
            ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖ +
              C *
                (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  refine ⟨A + B, add_pos hApos hBpos, ?_⟩
  intro u
  let q : ℝ :=
    (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))
  let D : ℝ :=
    ‖zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
        f F (h.height_schedule.height u) -
      zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
        f F (h.height_schedule.height u)‖
  let H : ℝ :=
    ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
      f F h u‖
  let S : ℝ :=
    ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖
  have hdecomp :
      ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
        f F h u‖ ≤ D + H :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_norm_le_boundaryDefect_add_horizontal
      f F h u
  have hD : D ≤ A * q :=
    hboundary u
  have hH : H ≤ S + B * q :=
    hhorizontal u
  have hsum : D + H ≤ A * q + (S + B * q) :=
    add_le_add hD hH
  have hrotate :
      A * q + (S + B * q) = S + (A * q + B * q) := by
    calc
      A * q + (S + B * q) = (A * q + S) + B * q := by
        exact (add_assoc (A * q) S (B * q)).symm
      _ = (S + A * q) + B * q := by
        exact congrArg (fun x : ℝ => x + B * q) (add_comm (A * q) S)
      _ = S + (A * q + B * q) := by
        exact add_assoc S (A * q) (B * q)
  have hfactor :
      A * q + B * q = (A + B) * q :=
    (add_mul A B q).symm
  have htarget :
      A * q + (S + B * q) = S + (A + B) * q :=
    Eq.trans hrotate (congrArg (fun x : ℝ => S + x) hfactor)
  exact le_trans hdecomp (le_trans hsum (le_of_eq htarget))

/-- Adding a nonnegative explicit horizontal side term preserves an isolated
zero-pole horizontal inverse-quadratic estimate. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_norm_le_explicit_add_of_inverseQuadratic
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (B : ℝ)
    (hhorizontal :
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
          f F h u‖
          ≤ B *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))) :
    ∀ u : ℝ,
      ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
        f F h u‖
        ≤ ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖ +
          B *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  intro u
  let S : ℝ :=
    ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖
  let q : ℝ :=
    (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))
  let H : ℝ :=
    ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
      f F h u‖
  have hH : H ≤ B * q :=
    hhorizontal u
  have hnonneg : 0 ≤ S :=
    norm_nonneg (explicitFormulaScheduledHorizontalSideDifference f F h u)
  have hadd : B * q ≤ S + B * q := by
    calc
      B * q = 0 + B * q := by
        exact (zero_add (B * q)).symm
      _ ≤ S + B * q := by
        exact add_le_add_right hnonneg (B * q)
  exact le_trans hH hadd

/-- Exact sink for the left-zero scheduled rectangle cancellation from the
genuine tangent-contour Cauchy defect. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPole_scheduledRectangleCauchyCancellation_of_tangentCauchy_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (A B : ℝ)
    (hApos : 0 < A)
    (hBpos : 0 < B)
    (htangent :
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u) +
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) * Complex.I‖
          ≤ A *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)))
    (hhorizontal :
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
          f F h u‖
          ≤ B *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
          f F h u‖
          ≤
            ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖ +
              C *
                (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  refine ⟨A + B, add_pos hApos hBpos, ?_⟩
  intro u
  let q : ℝ :=
    (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))
  let E : ℝ :=
    ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖
  let L : ℝ :=
    ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
      f F h u‖
  let D : ℝ :=
    ‖zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
        f F (h.height_schedule.height u) +
      zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
        f F (h.height_schedule.height u) * Complex.I‖
  let H : ℝ :=
    ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
      f F h u‖
  have hdecomp : L ≤ D + H :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_norm_le_tangentBoundaryDefect_add_horizontal
      f F h u
  have hD : D ≤ A * q :=
    htangent u
  have hH : H ≤ B * q :=
    hhorizontal u
  have hsum : D + H ≤ A * q + B * q :=
    add_le_add hD hH
  have hfactor : A * q + B * q = (A + B) * q :=
    (add_mul A B q).symm
  have htail : L ≤ (A + B) * q :=
    le_trans hdecomp (le_trans hsum (le_of_eq hfactor))
  have hEnonneg : 0 ≤ E :=
    norm_nonneg (explicitFormulaScheduledHorizontalSideDifference f F h u)
  have hadd : (A + B) * q ≤ E + (A + B) * q := by
    calc
      (A + B) * q = 0 + (A + B) * q := by
        exact (zero_add ((A + B) * q)).symm
      _ ≤ E + (A + B) * q := by
        exact add_le_add_right hEnonneg ((A + B) * q)
  exact le_trans htail hadd

/-- Exact sink for the left-zero scheduled rectangle cancellation.

The remaining analytic input is the all-height Cauchy estimate for the left
off-pole `s = 0` face.  Once that owner theorem is available, the already
proved boundary-defect identity and isolated horizontal estimate discharge the
scheduled rectangle cancellation statement. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPole_scheduledRectangleCauchyCancellation_of_leftCauchy_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (A B : ℝ)
    (hApos : 0 < A)
    (hBpos : 0 < B)
    (hleft :
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
          f F (h.height_schedule.height u)‖
          ≤ A *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)))
    (hhorizontal :
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
          f F h u‖
          ≤ B *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
          f F h u‖
          ≤
            ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖ +
              C *
                (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  match
    zetaCompletedExplicitFormulaCorrectionZeroPoleBoundaryDefect_inverseQuadratic_of_left_horizontal
      f F h A B hApos hBpos hleft hhorizontal with
  | ⟨D, hDpos, hD⟩ =>
      exact
        zetaCompletedExplicitFormulaCorrectionLeftZeroPole_scheduledRectangleCauchyCancellation_of_boundaryDefect_horizontal
          f F h D B hDpos hBpos hD
          (zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_norm_le_explicit_add_of_inverseQuadratic
            f F h B hhorizontal)

/-- The scheduled Cauchy rectangle cancellation package for the left-face
off-pole `s = 0` correction integral.

The remaining analytic input is the raw positive-height standard rectangle
Cauchy theorem for the isolated zero-pole kernel, with the honest `2πi`
normalization:
`zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
  f F T =
  (2 * (Real.pi : ℂ) * Complex.I) *
    (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)))`.
The project/standard orientation defect and normalized-residue transports are
already proved above. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPole_scheduledRectangleCauchyCancellation_ownerGap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
          f F h u‖
          ≤
            ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖ +
              A *
                (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  sorry

/-- Horizontal-edge cancellation for the scheduled left-face opposite-pole
integral. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPole_horizontalEdgeCancellation_inverseQuadraticBound_ownerGap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier)
    (hBottomMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) :
    ∃ B : ℝ,
      0 < B ∧
      ∀ u : ℝ,
        ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖
          ≤ B *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  exact
    explicitFormulaScheduledHorizontalSideDifference_inverseQuadraticBound_ownerGap
      f F h E hTopMem hBottomMem

/-- Algebraic assembly of the scheduled Cauchy rectangle cancellation and the
horizontal-edge inverse-quadratic bound for the left-face off-pole pole. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPole_inverseQuadraticBound_from_cauchyHorizontal_ownerGap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier)
    (hBottomMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) :
    ∃ M : ℝ,
      0 < M ∧
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
          f F h u‖
          ≤ M *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  match
    zetaCompletedExplicitFormulaCorrectionLeftZeroPole_scheduledRectangleCauchyCancellation_ownerGap
      f F h,
    zetaCompletedExplicitFormulaCorrectionLeftZeroPole_horizontalEdgeCancellation_inverseQuadraticBound_ownerGap
      f F h E hTopMem hBottomMem with
  | ⟨A, hApos, hA⟩, ⟨B, hBpos, hB⟩ =>
      refine ⟨A + B, add_pos hApos hBpos, ?_⟩
      intro u
      let q : ℝ :=
        (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))
      have hrectangle :
          ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
            f F h u‖
            ≤
              ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖ +
                A * q :=
        hA u
      have hhorizontal :
          ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖
            ≤ B * q :=
        hB u
      have hcombined :
          ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖ + A * q
            ≤ B * q + A * q :=
        add_le_add_right hhorizontal (A * q)
      have hcommuted :
          B * q + A * q = A * q + B * q :=
        add_comm (B * q) (A * q)
      have hfactored :
          A * q + B * q = (A + B) * q :=
        (add_mul A B q).symm
      have htarget :
          B * q + A * q = (A + B) * q :=
        Eq.trans hcommuted hfactored
      exact le_trans hrectangle (le_trans hcombined (le_of_eq htarget))

/-- The scheduled Cauchy/oscillatory cancellation package for the left-face
off-pole `s = 0` correction integral. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPole_scheduledContourCancellation_inverseQuadraticBound_ownerGap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier)
    (hBottomMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) :
    ∃ M : ℝ,
      0 < M ∧
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
          f F h u‖
          ≤ M *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  exact
    zetaCompletedExplicitFormulaCorrectionLeftZeroPole_inverseQuadraticBound_from_cauchyHorizontal_ownerGap
      f F h E hTopMem hBottomMem

/-- Definition transport from the named scheduled left-face oscillatory integral
to the explicit integral used in the correction channel. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPole_scheduledOscillatoryIntegral_eq_named
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (∫ t in
        Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        (-1 /
            zetaCompletedExplicitFormulaLeftPath
              (F.rectangle (h.height_schedule.height u)) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath
                (F.rectangle (h.height_schedule.height u)) t - 1 / 2)) =
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
        f F h u :=
  rfl

/-- Scheduled Cauchy cancellation for the explicit left-face off-pole `s = 0`
correction integral.

As on the right face, fixed horizontal displacement and expanding height mean
that denominator separation gives only a local algebraic input.  The inverse
quadratic scheduled bound belongs to the contour/oscillatory cancellation
argument for the whole vertical integral. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPole_scheduledOscillatoryIntegral_inverseQuadraticBound_ownerGap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier)
    (hBottomMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) :
    ∃ M : ℝ,
      0 < M ∧
      ∀ u : ℝ,
        ‖∫ t in
            Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            (-1 /
                zetaCompletedExplicitFormulaLeftPath
                  (F.rectangle (h.height_schedule.height u)) t) *
                zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaLeftPath
                    (F.rectangle (h.height_schedule.height u)) t - 1 / 2)‖
          ≤ M *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  match
    zetaCompletedExplicitFormulaCorrectionLeftZeroPole_scheduledContourCancellation_inverseQuadraticBound_ownerGap
      f F h E hTopMem hBottomMem with
  | ⟨M, hMpos, hbound⟩ =>
      refine ⟨M, hMpos, ?_⟩
      intro u
      have hnamed :
          (∫ t in
              Set.Icc
                (-(F.rectangle (h.height_schedule.height u)).T)
                (F.rectangle (h.height_schedule.height u)).T,
              (-1 /
                  zetaCompletedExplicitFormulaLeftPath
                    (F.rectangle (h.height_schedule.height u)) t) *
                zetaCompletedExplicitFormulaPhi f
                  (zetaCompletedExplicitFormulaLeftPath
                      (F.rectangle (h.height_schedule.height u)) t - 1 / 2)) =
            zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
              f F h u :=
        zetaCompletedExplicitFormulaCorrectionLeftZeroPole_scheduledOscillatoryIntegral_eq_named
          f F h u
      exact Eq.symm hnamed ▸ hbound u

/-- Definition transport from the left-face off-pole correction integral to its
explicit oscillatory-integral cancellation estimate. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_scheduledCauchyCancellation_rawInverseQuadraticBound_ownerGap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier)
    (hBottomMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) :
    ∃ M : ℝ,
      0 < M ∧
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
          f F (h.height_schedule.height u)‖
          ≤ M *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  exact
    zetaCompletedExplicitFormulaCorrectionLeftZeroPole_scheduledOscillatoryIntegral_inverseQuadraticBound_ownerGap
      f F h E hTopMem hBottomMem

/-- Algebraic transport from the scheduled left-face Cauchy cancellation estimate
to the public inverse-quadratic off-pole bound. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_scheduledCauchyCancellation_inverseQuadraticBound_ownerGap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier)
    (hBottomMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) :
    ∃ M : ℝ,
      0 < M ∧
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
          f F (h.height_schedule.height u)‖
          ≤ M *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  exact
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_scheduledCauchyCancellation_rawInverseQuadraticBound_ownerGap
      f F h E hTopMem hBottomMem

/-- Off-pole left-face correction tail estimate for the `s = 0` pole.

This public estimate is a thin wrapper over the scheduled Cauchy cancellation
theorem, not a pointwise-majorization estimate on the full expanding interval. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_offPoleTailBound_ownerGap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier)
    (hBottomMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) :
    ∃ M : ℝ,
      0 < M ∧
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
          f F (h.height_schedule.height u)‖
          ≤ M *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  exact
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_scheduledCauchyCancellation_inverseQuadraticBound_ownerGap
      f F h E hTopMem hBottomMem

/-- The off-pole left-face correction tail majorant tends to zero along the
cofinal scheduled heights. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_tailMajorant_tendsto_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (M : ℝ) :
    Tendsto
      (fun u : ℝ =>
        M * (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)))
      atTop
      (𝓝 0) := by
  exact
    zetaCompletedExplicitFormulaCorrection_scheduledInverseQuadraticTailMajorant_tendsto_zero
      F h.height_schedule M

/-- The left-face `s = 0` correction integral vanishes by the off-pole
denominator bound and rapid vertical-strip decay of the test transform. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_tendsto_zero_of_offPoleTailBound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (M : ℝ)
    (hMpos : 0 < M)
    (hbound :
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
          f F (h.height_schedule.height u)‖
          ≤ M *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  exact
    squeeze_zero_norm hbound
      (zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_tailMajorant_tendsto_zero
        f F h M)

/-- Left-face one-pole Cauchy limit for the `s = 0` pole contribution. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_tendsto_zero_ownerChannelTransportAnalytic
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  match
    ExplicitFormulaFamilyAnalyticPackage.scheduled_horizontalFamilyZeroExcisedStrip
      h with
  | ⟨E, hTopMem, hBottomMem⟩ =>
      match
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_offPoleTailBound_ownerGap
          f F h E hTopMem hBottomMem with
      | ⟨C, hCpos, hCbound⟩ =>
          exact
            zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_tendsto_zero_of_offPoleTailBound
              f F h C hCpos hCbound

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
