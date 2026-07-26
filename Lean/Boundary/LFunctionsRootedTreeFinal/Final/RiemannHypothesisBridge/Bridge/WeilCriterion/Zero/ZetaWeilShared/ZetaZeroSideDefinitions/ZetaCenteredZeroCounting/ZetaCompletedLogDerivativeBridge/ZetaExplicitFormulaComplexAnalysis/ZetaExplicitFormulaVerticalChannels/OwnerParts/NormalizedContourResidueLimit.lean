import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.HorizontalEdgeBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.NormalizedContourProjection
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.NormalizedCorrectionTarget

/-!
# Normalized contour residue limit
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- A normalized tangent residue limit and horizontal decay imply the same residue limit
for the normalized project-oriented contour. -/
theorem zetaCompletedExplicitFormulaNormalizedContourIntegral_tendsto_of_tangent_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (residueSum : ℂ)
    (htangent :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaNormalizedTangentContourIntegral f
            (F.rectangle (h.height_schedule.height u)))
        atTop (𝓝 residueSum))
    (hhorizontal :
      Tendsto
        (fun u : ℝ => explicitFormulaScheduledHorizontalSideDifference f F h u)
        atTop (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaNormalizedContourIntegral f
          (F.rectangle (h.height_schedule.height u)))
      atTop (𝓝 residueSum) := by
  have htangentRaw :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaTangentContourIntegral f
            (F.rectangle (h.height_schedule.height u)))
        atTop
        (𝓝 (explicitFormulaTwoPiI * residueSum)) := by
    have hscaled := htangent.const_mul explicitFormulaTwoPiI
    have hpointwise :
        (fun u : ℝ =>
          explicitFormulaTwoPiI *
            zetaCompletedExplicitFormulaNormalizedTangentContourIntegral f
              (F.rectangle (h.height_schedule.height u))) =
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaTangentContourIntegral f
            (F.rectangle (h.height_schedule.height u))) := by
      exact funext (fun u : ℝ => by
        have hright :
            zetaCompletedExplicitFormulaNormalizedTangentContourIntegral f
                (F.rectangle (h.height_schedule.height u)) * explicitFormulaTwoPiI =
              zetaCompletedExplicitFormulaTangentContourIntegral f
                (F.rectangle (h.height_schedule.height u)) :=
          (eq_div_iff explicitFormulaTwoPiI_ne_zero).mp (Eq.refl
            (zetaCompletedExplicitFormulaNormalizedTangentContourIntegral f
              (F.rectangle (h.height_schedule.height u))))
        exact Eq.trans
          (mul_comm explicitFormulaTwoPiI
            (zetaCompletedExplicitFormulaNormalizedTangentContourIntegral f
              (F.rectangle (h.height_schedule.height u))))
          hright)
    exact Eq.subst
      (motive := fun values : ℝ → ℂ =>
        Tendsto values atTop (𝓝 (explicitFormulaTwoPiI * residueSum)))
      hpointwise hscaled
  have hrotated :
      Tendsto
        (fun u : ℝ =>
          (-Complex.I) *
            zetaCompletedExplicitFormulaTangentContourIntegral f
              (F.rectangle (h.height_schedule.height u)))
        atTop
        (𝓝 (explicitFormulaTwoPi * residueSum)) := by
    have hbase := htangentRaw.const_mul (-Complex.I)
    exact Eq.subst
      (motive := fun target : ℂ =>
        Tendsto
          (fun u : ℝ =>
            (-Complex.I) *
              zetaCompletedExplicitFormulaTangentContourIntegral f
                (F.rectangle (h.height_schedule.height u)))
          atTop (𝓝 target))
      (explicitFormula_negI_mul_twoPiI_mul residueSum)
      hbase
  have hcorrection :
      Tendsto
        (fun u : ℝ =>
          ((1 : ℂ) - Complex.I) *
            explicitFormulaScheduledHorizontalSideDifference f F h u)
        atTop (𝓝 0) := by
    have hbase := hhorizontal.const_mul ((1 : ℂ) - Complex.I)
    exact Eq.subst
      (motive := fun target : ℂ =>
        Tendsto
          (fun u : ℝ =>
            ((1 : ℂ) - Complex.I) *
              explicitFormulaScheduledHorizontalSideDifference f F h u)
          atTop (𝓝 target))
      (mul_zero ((1 : ℂ) - Complex.I)) hbase
  have hprojectRaw :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaContourIntegral f
            (F.rectangle (h.height_schedule.height u)))
        atTop (𝓝 (explicitFormulaTwoPi * residueSum)) := by
    have hsum := hrotated.add hcorrection
    have hpointwise :
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaContourIntegral f
            (F.rectangle (h.height_schedule.height u))) =
        (fun u : ℝ =>
          (-Complex.I) *
              zetaCompletedExplicitFormulaTangentContourIntegral f
                (F.rectangle (h.height_schedule.height u)) +
            ((1 : ℂ) - Complex.I) *
              explicitFormulaScheduledHorizontalSideDifference f F h u) := by
      exact funext (fun u : ℝ =>
        zetaCompletedExplicitFormulaContourIntegral_eq_negI_mul_tangent_add_horizontalCorrection
          f (F.rectangle (h.height_schedule.height u)))
    have htarget : explicitFormulaTwoPi * residueSum + 0 =
        explicitFormulaTwoPi * residueSum := add_zero _
    exact Eq.subst
      (motive := fun values : ℝ → ℂ =>
        Tendsto values atTop (𝓝 (explicitFormulaTwoPi * residueSum)))
      hpointwise.symm
      (Eq.subst
        (motive := fun target : ℂ =>
          Tendsto
            (fun u : ℝ =>
              (-Complex.I) *
                  zetaCompletedExplicitFormulaTangentContourIntegral f
                    (F.rectangle (h.height_schedule.height u)) +
                ((1 : ℂ) - Complex.I) *
                  explicitFormulaScheduledHorizontalSideDifference f F h u)
            atTop (𝓝 target))
        htarget hsum)
  have hnormalized := hprojectRaw.div_const explicitFormulaTwoPi
  have htarget :
      (explicitFormulaTwoPi * residueSum) / explicitFormulaTwoPi = residueSum := by
    calc
      (explicitFormulaTwoPi * residueSum) / explicitFormulaTwoPi =
          (residueSum * explicitFormulaTwoPi) / explicitFormulaTwoPi := by
        exact congrArg (fun value : ℂ => value / explicitFormulaTwoPi)
          (mul_comm explicitFormulaTwoPi residueSum)
      _ = residueSum := mul_div_cancel_right₀ residueSum explicitFormulaTwoPi_ne_zero
  exact Eq.subst
    (motive := fun target : ℂ =>
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaNormalizedContourIntegral f
            (F.rectangle (h.height_schedule.height u)))
        atTop (𝓝 target))
    htarget hnormalized

/-- Eventual selected-radius residue equality in the direction used by limit transport. -/
theorem explicitFormulaRectangle_poleCorrectedResidueSum_eventually_eq_normalizedTangent
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ∀ᶠ u in atTop,
      explicitFormulaRectangle_poleCorrectedResidueSum f
          (h.height_schedule.height u) =
        zetaCompletedExplicitFormulaNormalizedTangentContourIntegral f
          (F.rectangle (h.height_schedule.height u)) :=
  h.height_schedule.eventually_height_pos.mono
    (fun u hu =>
      (zetaCompletedExplicitFormulaNormalizedTangentContourIntegral_eq_poleCorrectedResidueSum_selected
        f F h hu
      (explicitFormulaCompletedZeroContourHeightWindow_mem_iff_interiorSingular
        F (h.height_schedule.height u))).symm)

/-- Pole-corrected finite zero-residue windows converge to the completed zero
side plus the fixed completed-pole packet along any cofinal height schedule. -/
theorem explicitFormulaRectangle_poleCorrectedResidueSum_tendsto_zeroSideComplex_add_poles
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (heightSchedule : ExplicitFormulaCofinalHeightSchedule F)
    (hsum :
      Summable
        (fun rho : {rho : ℂ // ZetaCompletedZero rho} =>
          zetaZeroSideContribution (rho : ℂ) f)) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaRectangle_poleCorrectedResidueSum f
          (heightSchedule.height u))
      atTop
      (𝓝 (zetaCompletedZeroSideComplex f +
        explicitFormulaRectangle_completedPoleResidueSum f)) := by
  have hwindow :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaCompletedZeroContourHeightWindowResidueSum f
            (heightSchedule.height u))
        atTop (𝓝 (zetaCompletedZeroSideComplex f)) :=
    (explicitFormulaCompletedZeroContourHeightWindowResidueSum_tendsto_zeroSideComplex_ownerZeroLimit
      f hsum).comp heightSchedule.cofinal
  have hpole :
      Tendsto
        (fun _u : ℝ => explicitFormulaRectangle_completedPoleResidueSum f)
        atTop (𝓝 (explicitFormulaRectangle_completedPoleResidueSum f)) :=
    tendsto_const_nhds
  have hsumLimit := hwindow.add hpole
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaRectangle_poleCorrectedResidueSum f
          (heightSchedule.height u)) =
      (fun u : ℝ =>
        explicitFormulaCompletedZeroContourHeightWindowResidueSum f
            (heightSchedule.height u) +
          explicitFormulaRectangle_completedPoleResidueSum f) := by
    exact funext
      (fun u : ℝ =>
        explicitFormulaRectangle_poleCorrectedResidueSum_eq
          f (heightSchedule.height u))
  exact Eq.subst
    (motive := fun values : ℝ → ℂ =>
      Tendsto values atTop
        (𝓝 (zetaCompletedZeroSideComplex f +
          explicitFormulaRectangle_completedPoleResidueSum f)))
    hpointwise.symm
    hsumLimit

/-- The normalized pole-corrected project contour converges to the completed zero-side
series along the scheduled rectangles. -/
theorem explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral_tendsto_zeroSideComplex
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
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier)
    (hsum :
      Summable
        (fun rho : {rho : ℂ // ZetaCompletedZero rho} =>
          zetaZeroSideContribution (rho : ℂ) f)) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral
          f F (h.height_schedule.height u))
      atTop (𝓝 (zetaCompletedZeroSideComplex f)) := by
  have hpole :
      Tendsto
        (fun _u : ℝ => explicitFormulaRectangle_completedPoleResidueSum f)
        atTop (𝓝 (explicitFormulaRectangle_completedPoleResidueSum f)) :=
    tendsto_const_nhds
  have hpoleCorrected :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaRectangle_poleCorrectedResidueSum f
            (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedZeroSideComplex f +
          explicitFormulaRectangle_completedPoleResidueSum f)) := by
    exact
      explicitFormulaRectangle_poleCorrectedResidueSum_tendsto_zeroSideComplex_add_poles
        f F h.height_schedule hsum
  have htangent :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaNormalizedTangentContourIntegral f
            (F.rectangle (h.height_schedule.height u)))
        atTop
        (𝓝 (zetaCompletedZeroSideComplex f +
          explicitFormulaRectangle_completedPoleResidueSum f)) :=
    hpoleCorrected.congr'
      (explicitFormulaRectangle_poleCorrectedResidueSum_eventually_eq_normalizedTangent
        f F h)
  have hhorizontal :
      Tendsto
        (fun u : ℝ => explicitFormulaScheduledHorizontalSideDifference f F h u)
        atTop (𝓝 0) :=
    Boundary.LFunctions.ZetaAdmissibleFunction.explicitFormulaScheduledHorizontalSideDifference_tendsto_zero_owner
      f F h E hTopMem hBottomMem
  have hproject :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaNormalizedContourIntegral f
            (F.rectangle (h.height_schedule.height u)))
        atTop
        (𝓝 (zetaCompletedZeroSideComplex f +
          explicitFormulaRectangle_completedPoleResidueSum f)) :=
    zetaCompletedExplicitFormulaNormalizedContourIntegral_tendsto_of_tangent_horizontal
      f F h
      (zetaCompletedZeroSideComplex f + explicitFormulaRectangle_completedPoleResidueSum f)
      htangent hhorizontal
  have hcorrected := hproject.sub hpole
  have htarget :
      zetaCompletedZeroSideComplex f + explicitFormulaRectangle_completedPoleResidueSum f -
          explicitFormulaRectangle_completedPoleResidueSum f =
        zetaCompletedZeroSideComplex f :=
    add_sub_cancel_right
      (zetaCompletedZeroSideComplex f)
      (explicitFormulaRectangle_completedPoleResidueSum f)
  exact Eq.subst
    (motive := fun target : ℂ =>
      Tendsto
        (fun u : ℝ =>
          explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral
            f F (h.height_schedule.height u))
        atTop (𝓝 target))
    htarget hcorrected

/-- The scheduled normalized vertical side with the completed-pole residue
packet removed in the residue-theorem coordinates. -/
noncomputable def explicitFormulaScheduledNormalizedPoleCorrectedVerticalDifference
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) : ℂ :=
  (zetaCompletedExplicitFormulaRightLineIntegral f
        (F.rectangle (h.height_schedule.height u)) -
      zetaCompletedExplicitFormulaLeftLineIntegral f
        (F.rectangle (h.height_schedule.height u))) /
      explicitFormulaTwoPi -
    explicitFormulaRectangle_completedPoleResidueSum f

/-- Adding and then removing the same right summand commutes past one
independent subtraction. -/
theorem explicitFormula_add_sub_sub_right
    (first second poles : ℂ) :
    (first + second - poles) - second = first - poles := by
  calc
    (first + second - poles) - second =
        ((first + second) + (-poles)) + (-second) := by
      exact congrArg (fun value : ℂ => value + (-second))
        (sub_eq_add_neg (first + second) poles)
    _ = (first + second) + ((-poles) + (-second)) := by
      exact add_assoc (first + second) (-poles) (-second)
    _ = (first + second) + ((-second) + (-poles)) := by
      exact congrArg (fun value : ℂ => (first + second) + value)
        (add_comm (-poles) (-second))
    _ = first + (second + ((-second) + (-poles))) := by
      exact add_assoc first second ((-second) + (-poles))
    _ = first + ((second + (-second)) + (-poles)) := by
      exact congrArg (fun value : ℂ => first + value)
        (add_assoc second (-second) (-poles)).symm
    _ = first + (0 + (-poles)) := by
      exact congrArg
        (fun value : ℂ => first + (value + (-poles)))
        (add_neg_cancel second)
    _ = first + (-poles) := by
      exact congrArg (fun value : ℂ => first + value)
        (zero_add (-poles))
    _ = first - poles := by
      exact (sub_eq_add_neg first poles).symm

/-- Four-side project orientation grouped into vertical and horizontal
differences. -/
theorem explicitFormula_four_side_project_split
    (right left top bottom : ℂ) :
    right - left + top - bottom =
      (right - left) + (top - bottom) := by
  calc
    right - left + top - bottom =
        (right - left + top) + (-bottom) := by
      exact sub_eq_add_neg (right - left + top) bottom
    _ = (right - left) + (top + (-bottom)) := by
      exact add_assoc (right - left) top (-bottom)
    _ = (right - left) + (top - bottom) := by
      exact congrArg (fun value : ℂ => (right - left) + value)
        (sub_eq_add_neg top bottom).symm

/-- The normalized pole-corrected vertical side is the normalized
pole-corrected project contour minus the normalized horizontal side. -/
theorem explicitFormulaScheduledNormalizedPoleCorrectedVerticalDifference_eq_contour_sub_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    explicitFormulaScheduledNormalizedPoleCorrectedVerticalDifference f F h u =
      explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral
          f F (h.height_schedule.height u) -
        explicitFormulaScheduledHorizontalSideDifference f F h u /
          explicitFormulaTwoPi := by
  let vertical : ℂ :=
    zetaCompletedExplicitFormulaRightLineIntegral f
        (F.rectangle (h.height_schedule.height u)) -
      zetaCompletedExplicitFormulaLeftLineIntegral f
        (F.rectangle (h.height_schedule.height u))
  let horizontal : ℂ :=
    explicitFormulaScheduledHorizontalSideDifference f F h u
  let poles : ℂ := explicitFormulaRectangle_completedPoleResidueSum f
  have hcontour :
      zetaCompletedExplicitFormulaContourIntegral f
          (F.rectangle (h.height_schedule.height u)) =
        vertical + horizontal := by
    calc
      zetaCompletedExplicitFormulaContourIntegral f
          (F.rectangle (h.height_schedule.height u)) =
          zetaCompletedExplicitFormulaRightLineIntegral f
                (F.rectangle (h.height_schedule.height u)) -
            zetaCompletedExplicitFormulaLeftLineIntegral f
                (F.rectangle (h.height_schedule.height u)) +
            zetaCompletedExplicitFormulaTopLineIntegral f
                (F.rectangle (h.height_schedule.height u)) -
            zetaCompletedExplicitFormulaBottomLineIntegral f
                (F.rectangle (h.height_schedule.height u)) := by
        exact zetaCompletedExplicitFormulaContourIntegral_eq
          f (F.rectangle (h.height_schedule.height u))
      _ =
          vertical +
            (zetaCompletedExplicitFormulaTopLineIntegral f
                (F.rectangle (h.height_schedule.height u)) -
              zetaCompletedExplicitFormulaBottomLineIntegral f
                (F.rectangle (h.height_schedule.height u))) := by
        exact explicitFormula_four_side_project_split
          (zetaCompletedExplicitFormulaRightLineIntegral f
            (F.rectangle (h.height_schedule.height u)))
          (zetaCompletedExplicitFormulaLeftLineIntegral f
            (F.rectangle (h.height_schedule.height u)))
          (zetaCompletedExplicitFormulaTopLineIntegral f
            (F.rectangle (h.height_schedule.height u)))
          (zetaCompletedExplicitFormulaBottomLineIntegral f
            (F.rectangle (h.height_schedule.height u)))
      _ = vertical + horizontal := Eq.refl _
  have hdivision :
      (vertical + horizontal) / explicitFormulaTwoPi =
        vertical / explicitFormulaTwoPi +
          horizontal / explicitFormulaTwoPi := by
    exact add_div vertical horizontal explicitFormulaTwoPi
  calc
    explicitFormulaScheduledNormalizedPoleCorrectedVerticalDifference f F h u =
        vertical / explicitFormulaTwoPi - poles := Eq.refl _
    _ = (vertical / explicitFormulaTwoPi +
          horizontal / explicitFormulaTwoPi - poles) -
        horizontal / explicitFormulaTwoPi := by
      exact
        (explicitFormula_add_sub_sub_right
          (vertical / explicitFormulaTwoPi)
          (horizontal / explicitFormulaTwoPi)
          poles).symm
    _ = ((vertical + horizontal) / explicitFormulaTwoPi - poles) -
          horizontal / explicitFormulaTwoPi := by
      exact congrArg
        (fun value : ℂ => (value - poles) -
          horizontal / explicitFormulaTwoPi)
        hdivision.symm
    _ =
        (zetaCompletedExplicitFormulaContourIntegral f
            (F.rectangle (h.height_schedule.height u)) /
            explicitFormulaTwoPi - poles) -
          horizontal / explicitFormulaTwoPi := by
      exact congrArg
        (fun value : ℂ => (value / explicitFormulaTwoPi - poles) -
          horizontal / explicitFormulaTwoPi)
        hcontour.symm
    _ = explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral
          f F (h.height_schedule.height u) -
        explicitFormulaScheduledHorizontalSideDifference f F h u /
          explicitFormulaTwoPi := Eq.refl _

/-- The normalized pole-corrected vertical side converges to the completed
zero-side series along the scheduled rectangles. -/
theorem explicitFormulaScheduledNormalizedPoleCorrectedVerticalDifference_tendsto_zeroSideComplex
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
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier)
    (hsum :
      Summable
        (fun rho : {rho : ℂ // ZetaCompletedZero rho} =>
          zetaZeroSideContribution (rho : ℂ) f)) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaScheduledNormalizedPoleCorrectedVerticalDifference
          f F h u)
      atTop (𝓝 (zetaCompletedZeroSideComplex f)) := by
  have hcontour :=
    explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral_tendsto_zeroSideComplex
      f F h E hTopMem hBottomMem hsum
  have hhorizontal :=
    Boundary.LFunctions.ZetaAdmissibleFunction.explicitFormulaScheduledHorizontalSideDifference_tendsto_zero_owner
      f F h E hTopMem hBottomMem
  have hnormalizedHorizontal :=
    hhorizontal.div_const explicitFormulaTwoPi
  have hdifference := hcontour.sub hnormalizedHorizontal
  have hzeroDiv :
      (0 : ℂ) / explicitFormulaTwoPi = 0 :=
    zero_div explicitFormulaTwoPi
  have htarget :
      zetaCompletedZeroSideComplex f - 0 / explicitFormulaTwoPi =
        zetaCompletedZeroSideComplex f :=
    Eq.trans (congrArg (fun term : ℂ => zetaCompletedZeroSideComplex f - term) hzeroDiv)
      (sub_zero _)
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral
            f F (h.height_schedule.height u) -
          explicitFormulaScheduledHorizontalSideDifference f F h u /
            explicitFormulaTwoPi) =
        (fun u : ℝ =>
          explicitFormulaScheduledNormalizedPoleCorrectedVerticalDifference
            f F h u) := by
    exact funext (fun u : ℝ =>
      (explicitFormulaScheduledNormalizedPoleCorrectedVerticalDifference_eq_contour_sub_horizontal
        f F h u).symm)
  exact Eq.subst
    (motive := fun values : ℝ → ℂ =>
      Tendsto values atTop (𝓝 (zetaCompletedZeroSideComplex f)))
    hpointwise
    (Eq.subst
      (motive := fun target : ℂ =>
        Tendsto
          (fun u : ℝ =>
            explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral
                f F (h.height_schedule.height u) -
              explicitFormulaScheduledHorizontalSideDifference f F h u /
                explicitFormulaTwoPi)
          atTop (𝓝 target))
      htarget hdifference)

/-- A raw standard-contour vertical limit transports to the normalized
pole-corrected standard-contour target. -/
theorem explicitFormulaScheduledNormalizedPoleCorrectedVerticalDifference_tendsto_standardBoundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hvertical :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaRightLineIntegral f
                (F.rectangle (h.height_schedule.height u)) -
            zetaCompletedExplicitFormulaLeftLineIntegral f
                (F.rectangle (h.height_schedule.height u)))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaStandardContourBoundarySum f))) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaScheduledNormalizedPoleCorrectedVerticalDifference
          f F h u)
      atTop
      (𝓝
        (zetaCompletedExplicitFormulaResidueNormalizedStandardContourBoundarySum f)) := by
  have hdivided := hvertical.div_const explicitFormulaTwoPi
  have hpoles :
      Tendsto
        (fun _u : ℝ => explicitFormulaRectangle_completedPoleResidueSum f)
        atTop
        (𝓝 (explicitFormulaRectangle_completedPoleResidueSum f)) :=
    tendsto_const_nhds
  have hsubtracted := hdivided.sub hpoles
  exact hsubtracted

/-- Uniqueness of the normalized scheduled vertical limit identifies the
residue-normalized standard-contour boundary target with the completed zero-side series. -/
theorem zetaCompletedExplicitFormulaResidueNormalizedStandardContourBoundarySum_eq_zeroSideComplex
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
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier)
    (hsum :
      Summable
        (fun rho : {rho : ℂ // ZetaCompletedZero rho} =>
          zetaZeroSideContribution (rho : ℂ) f))
    (hvertical :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaRightLineIntegral f
                (F.rectangle (h.height_schedule.height u)) -
            zetaCompletedExplicitFormulaLeftLineIntegral f
                (F.rectangle (h.height_schedule.height u)))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaStandardContourBoundarySum f))) :
    zetaCompletedExplicitFormulaResidueNormalizedStandardContourBoundarySum f =
      zetaCompletedZeroSideComplex f := by
  have hstandard :=
    explicitFormulaScheduledNormalizedPoleCorrectedVerticalDifference_tendsto_standardBoundary
      f F h hvertical
  have hzeros :=
    explicitFormulaScheduledNormalizedPoleCorrectedVerticalDifference_tendsto_zeroSideComplex
      f F h E hTopMem hBottomMem hsum
  exact tendsto_nhds_unique hstandard hzeros

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
