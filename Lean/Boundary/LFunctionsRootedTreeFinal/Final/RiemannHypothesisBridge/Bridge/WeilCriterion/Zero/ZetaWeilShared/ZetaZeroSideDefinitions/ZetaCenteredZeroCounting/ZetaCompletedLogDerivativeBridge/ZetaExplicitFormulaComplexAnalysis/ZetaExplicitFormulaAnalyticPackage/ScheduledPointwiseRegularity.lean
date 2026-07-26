import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaAnalyticPackage.ScheduledLogDerivControl

/-!
# Scheduled pointwise regularity

This file owns the pointwise horizontal regularity supplied by a cofinal
boundary-avoiding schedule.  It does not use full completed log-derivative
control.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- A scheduled top horizontal point is not a completed contour singularity. -/
theorem ExplicitFormulaCofinalHeightSchedule.topPath_not_singular
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    ¬ explicitFormulaContourSingularPoint
      (zetaCompletedExplicitFormulaTopPath
        (F.rectangle (schedule.height u)) x) :=
  explicitFormulaContourFamily_topPath_not_singular_of_avoidsBoundary
    F (schedule.height u) x (schedule.avoids_boundary u) hx

/-- A scheduled bottom horizontal point is not a completed contour singularity. -/
theorem ExplicitFormulaCofinalHeightSchedule.bottomPath_not_singular
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    ¬ explicitFormulaContourSingularPoint
      (zetaCompletedExplicitFormulaBottomPath
        (F.rectangle (schedule.height u)) x) :=
  explicitFormulaContourFamily_bottomPath_not_singular_of_avoidsBoundary
    F (schedule.height u) x (schedule.avoids_boundary u) hx

/-- A scheduled top horizontal point is away from completed zeta zeros. -/
theorem ExplicitFormulaCofinalHeightSchedule.topPath_completedRiemannZeta_ne_zero
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    completedRiemannZeta
      (zetaCompletedExplicitFormulaTopPath
        (F.rectangle (schedule.height u)) x) ≠ 0 :=
  explicitFormulaContourSingularPoint.completedRiemannZeta_ne_zero_of_not
    (schedule.topPath_not_singular u x hx)

/-- A scheduled bottom horizontal point is away from completed zeta zeros. -/
theorem ExplicitFormulaCofinalHeightSchedule.bottomPath_completedRiemannZeta_ne_zero
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    completedRiemannZeta
      (zetaCompletedExplicitFormulaBottomPath
        (F.rectangle (schedule.height u)) x) ≠ 0 :=
  explicitFormulaContourSingularPoint.completedRiemannZeta_ne_zero_of_not
    (schedule.bottomPath_not_singular u x hx)

/-- A scheduled top horizontal point is away from the completed Gamma zero locus. -/
theorem ExplicitFormulaCofinalHeightSchedule.topPath_GammaReal_ne_zero
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    Complex.Gammaℝ
      (zetaCompletedExplicitFormulaTopPath
        (F.rectangle (schedule.height u)) x) ≠ 0 :=
  explicitFormulaContourSingularPoint.gamma_ne_zero_of_not
    (schedule.topPath_not_singular u x hx)

/-- A scheduled bottom horizontal point is away from the completed Gamma zero locus. -/
theorem ExplicitFormulaCofinalHeightSchedule.bottomPath_GammaReal_ne_zero
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    Complex.Gammaℝ
      (zetaCompletedExplicitFormulaBottomPath
        (F.rectangle (schedule.height u)) x) ≠ 0 :=
  explicitFormulaContourSingularPoint.gamma_ne_zero_of_not
    (schedule.bottomPath_not_singular u x hx)

/-- A scheduled top horizontal point avoids the half-argument completed Gamma zero locus. -/
theorem ExplicitFormulaCofinalHeightSchedule.topPath_GammaReal_half_ne_zero
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    Complex.Gammaℝ
      (zetaCompletedExplicitFormulaTopPath
        (F.rectangle (schedule.height u)) x / 2) ≠ 0 :=
  explicitFormulaContourSingularPoint.gamma_half_ne_zero_of_not
    (schedule.topPath_not_singular u x hx)

/-- A scheduled bottom horizontal point avoids the half-argument completed Gamma zero locus. -/
theorem ExplicitFormulaCofinalHeightSchedule.bottomPath_GammaReal_half_ne_zero
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    Complex.Gammaℝ
      (zetaCompletedExplicitFormulaBottomPath
        (F.rectangle (schedule.height u)) x / 2) ≠ 0 :=
  explicitFormulaContourSingularPoint.gamma_half_ne_zero_of_not
    (schedule.bottomPath_not_singular u x hx)

/-- Scheduled top horizontal points satisfy the zero-excised strip conditions. -/
theorem ExplicitFormulaCofinalHeightSchedule.topPath_zeroExcisedPointwise
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    (min F.c (1 - F.c) ≤
        (zetaCompletedExplicitFormulaTopPath
          (F.rectangle (schedule.height u)) x).re ∧
      (zetaCompletedExplicitFormulaTopPath
          (F.rectangle (schedule.height u)) x).re ≤
        max F.c (1 - F.c)) ∧
    zetaCompletedExplicitFormulaTopPath
      (F.rectangle (schedule.height u)) x ≠ 0 ∧
    zetaCompletedExplicitFormulaTopPath
      (F.rectangle (schedule.height u)) x ≠ 1 ∧
    completedRiemannZeta
      (zetaCompletedExplicitFormulaTopPath
        (F.rectangle (schedule.height u)) x) ≠ 0 ∧
    Complex.Gammaℝ
      (zetaCompletedExplicitFormulaTopPath
        (F.rectangle (schedule.height u)) x) ≠ 0 ∧
    Complex.Gammaℝ
      (zetaCompletedExplicitFormulaTopPath
        (F.rectangle (schedule.height u)) x / 2) ≠ 0 :=
  And.intro
    (And.intro
      (Eq.subst
        (motive := fun y : ℝ => min F.c (1 - F.c) ≤ y)
        (zetaCompletedExplicitFormulaTopPath_re_eq
          (F.rectangle (schedule.height u)) x).symm
        hx.1)
      (Eq.subst
        (motive := fun y : ℝ => y ≤ max F.c (1 - F.c))
        (zetaCompletedExplicitFormulaTopPath_re_eq
          (F.rectangle (schedule.height u)) x).symm
        hx.2))
    (And.intro
      (explicitFormulaContourSingularPoint.ne_zero_of_not
        (schedule.topPath_not_singular u x hx))
      (And.intro
        (explicitFormulaContourSingularPoint.ne_one_of_not
          (schedule.topPath_not_singular u x hx))
        (And.intro
          (schedule.topPath_completedRiemannZeta_ne_zero u x hx)
          (And.intro
            (schedule.topPath_GammaReal_ne_zero u x hx)
            (schedule.topPath_GammaReal_half_ne_zero u x hx)))))

/-- Scheduled bottom horizontal points satisfy the zero-excised strip conditions. -/
theorem ExplicitFormulaCofinalHeightSchedule.bottomPath_zeroExcisedPointwise
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    (min F.c (1 - F.c) ≤
        (zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (schedule.height u)) x).re ∧
      (zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (schedule.height u)) x).re ≤
        max F.c (1 - F.c)) ∧
    zetaCompletedExplicitFormulaBottomPath
      (F.rectangle (schedule.height u)) x ≠ 0 ∧
    zetaCompletedExplicitFormulaBottomPath
      (F.rectangle (schedule.height u)) x ≠ 1 ∧
    completedRiemannZeta
      (zetaCompletedExplicitFormulaBottomPath
        (F.rectangle (schedule.height u)) x) ≠ 0 ∧
    Complex.Gammaℝ
      (zetaCompletedExplicitFormulaBottomPath
        (F.rectangle (schedule.height u)) x) ≠ 0 ∧
    Complex.Gammaℝ
      (zetaCompletedExplicitFormulaBottomPath
        (F.rectangle (schedule.height u)) x / 2) ≠ 0 :=
  And.intro
    (And.intro
      (Eq.subst
        (motive := fun y : ℝ => min F.c (1 - F.c) ≤ y)
        (zetaCompletedExplicitFormulaBottomPath_re_eq
          (F.rectangle (schedule.height u)) x).symm
        hx.1)
      (Eq.subst
        (motive := fun y : ℝ => y ≤ max F.c (1 - F.c))
        (zetaCompletedExplicitFormulaBottomPath_re_eq
          (F.rectangle (schedule.height u)) x).symm
        hx.2))
    (And.intro
      (explicitFormulaContourSingularPoint.ne_zero_of_not
        (schedule.bottomPath_not_singular u x hx))
      (And.intro
        (explicitFormulaContourSingularPoint.ne_one_of_not
          (schedule.bottomPath_not_singular u x hx))
        (And.intro
          (schedule.bottomPath_completedRiemannZeta_ne_zero u x hx)
          (And.intro
            (schedule.bottomPath_GammaReal_ne_zero u x hx)
            (schedule.bottomPath_GammaReal_half_ne_zero u x hx)))))

/-- A scheduled package inherits top horizontal pointwise regularity from its schedule. -/
theorem ExplicitFormulaScheduledFamilyAnalyticPackage.topPath_zeroExcisedPointwise
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    (min F.c (1 - F.c) ≤
        (zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x).re ∧
      (zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x).re ≤
        max F.c (1 - F.c)) ∧
    zetaCompletedExplicitFormulaTopPath
      (F.rectangle (h.height_schedule.height u)) x ≠ 0 ∧
    zetaCompletedExplicitFormulaTopPath
      (F.rectangle (h.height_schedule.height u)) x ≠ 1 ∧
    completedRiemannZeta
      (zetaCompletedExplicitFormulaTopPath
        (F.rectangle (h.height_schedule.height u)) x) ≠ 0 ∧
    Complex.Gammaℝ
      (zetaCompletedExplicitFormulaTopPath
        (F.rectangle (h.height_schedule.height u)) x) ≠ 0 ∧
    Complex.Gammaℝ
      (zetaCompletedExplicitFormulaTopPath
        (F.rectangle (h.height_schedule.height u)) x / 2) ≠ 0 :=
  h.height_schedule.topPath_zeroExcisedPointwise u x hx

/-- A scheduled package inherits bottom horizontal pointwise regularity from its schedule. -/
theorem ExplicitFormulaScheduledFamilyAnalyticPackage.bottomPath_zeroExcisedPointwise
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    (min F.c (1 - F.c) ≤
        (zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x).re ∧
      (zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x).re ≤
        max F.c (1 - F.c)) ∧
    zetaCompletedExplicitFormulaBottomPath
      (F.rectangle (h.height_schedule.height u)) x ≠ 0 ∧
    zetaCompletedExplicitFormulaBottomPath
      (F.rectangle (h.height_schedule.height u)) x ≠ 1 ∧
    completedRiemannZeta
      (zetaCompletedExplicitFormulaBottomPath
        (F.rectangle (h.height_schedule.height u)) x) ≠ 0 ∧
    Complex.Gammaℝ
      (zetaCompletedExplicitFormulaBottomPath
        (F.rectangle (h.height_schedule.height u)) x) ≠ 0 ∧
    Complex.Gammaℝ
      (zetaCompletedExplicitFormulaBottomPath
        (F.rectangle (h.height_schedule.height u)) x / 2) ≠ 0 :=
  h.height_schedule.bottomPath_zeroExcisedPointwise u x hx

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
