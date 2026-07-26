import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CanonicalScheduledAnalyticPackage
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaAdmissibleTransformRegularity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaHorizontalEdgeBounds.ScheduledPolynomialGrowth

/-!
# Canonical scheduled polynomial package from path bounds

This file owns the direct polynomial scheduled package constructor for the
canonical autocorrelation horizontal paths.  The input is a concrete polynomial
bound on the actual top and bottom scheduled paths, not a global full strip
control package.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

namespace ZetaAdmissibleFunction

theorem zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_norm_bound_of_pathBounds
    (f : ZetaAdmissibleFunction) (G : ℂ → ℂ) (K : ℕ) (C : ℝ)
    (topBound :
      ∀ u x : ℝ,
        x ∈ Set.uIcc
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
          (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
        ‖G
          (zetaCompletedExplicitFormulaTopPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x)‖ ≤
          C *
            (1 +
              ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K)
    (bottomBound :
      ∀ u x : ℝ,
        x ∈ Set.uIcc
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
          (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
        ‖G
          (zetaCompletedExplicitFormulaBottomPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x)‖ ≤
          C *
            (1 +
              ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K)
    (z : ℂ)
    (hz :
      z ∈
        (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).carrier) :
    ‖G z‖ ≤ C * (1 + ‖z.im‖) ^ K :=
  let family : ExplicitFormulaContourFamily :=
    zetaCompletedExplicitFormula_autocorrelation_contourFamily f
  let schedule : ExplicitFormulaCofinalHeightSchedule family :=
    zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f
  Or.elim hz
    (fun htop =>
      Exists.elim htop
        (fun u htop_u =>
          Exists.elim htop_u
            (fun x htop_x =>
              let path : ℂ :=
                zetaCompletedExplicitFormulaTopPath
                  (family.rectangle (schedule.height u)) x
              let heightEquality :
                  ‖path.im‖ = ‖schedule.height u‖ :=
                zetaCompletedExplicitFormulaTopPath_im_norm
                  (family.rectangle (schedule.height u)) x
              let pathBound :
                  ‖G path‖ ≤ C * (1 + ‖path.im‖) ^ K :=
                Eq.subst
                  (motive := fun target : ℝ =>
                    ‖G path‖ ≤ C * (1 + target) ^ K)
                  heightEquality.symm
                  (topBound u x htop_x.1)
              Eq.subst
                (motive := fun w : ℂ =>
                  ‖G w‖ ≤ C * (1 + ‖w.im‖) ^ K)
                htop_x.2.symm
                pathBound)))
    (fun hbottom =>
      Exists.elim hbottom
        (fun u hbottom_u =>
          Exists.elim hbottom_u
            (fun x hbottom_x =>
              let path : ℂ :=
                zetaCompletedExplicitFormulaBottomPath
                  (family.rectangle (schedule.height u)) x
              let heightEquality :
                  ‖path.im‖ = ‖schedule.height u‖ :=
                zetaCompletedExplicitFormulaBottomPath_im_norm
                  (family.rectangle (schedule.height u)) x
              let pathBound :
                  ‖G path‖ ≤ C * (1 + ‖path.im‖) ^ K :=
                Eq.subst
                  (motive := fun target : ℝ =>
                    ‖G path‖ ≤ C * (1 + target) ^ K)
                  heightEquality.symm
                  (bottomBound u x hbottom_x.1)
              Eq.subst
                (motive := fun w : ℂ =>
                  ‖G w‖ ≤ C * (1 + ‖w.im‖) ^ K)
                hbottom_x.2.symm
                pathBound)))

theorem zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_bound_of_top_path
    (f : ZetaAdmissibleFunction) (K : ℕ) (C : ℝ)
    (topBound :
      ∀ u x : ℝ,
        x ∈ Set.uIcc
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
          (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
        ‖completedZetaNegLogDeriv
          (zetaCompletedExplicitFormulaTopPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x)‖ ≤
          C *
            (1 +
              ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K)
    (u x : ℝ)
    (hx :
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :
    let path : ℂ :=
      zetaCompletedExplicitFormulaTopPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
          ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
        x
    ‖completedZetaNegLogDeriv path‖ ≤
      C * (1 + ‖path.im‖) ^ K :=
  let family : ExplicitFormulaContourFamily :=
    zetaCompletedExplicitFormula_autocorrelation_contourFamily f
  let schedule : ExplicitFormulaCofinalHeightSchedule family :=
    zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f
  let path : ℂ :=
    zetaCompletedExplicitFormulaTopPath
      (family.rectangle (schedule.height u)) x
  let heightEquality :
      ‖path.im‖ = ‖schedule.height u‖ :=
    zetaCompletedExplicitFormulaTopPath_im_norm
      (family.rectangle (schedule.height u)) x
  let targetEquality :
      C * (1 + ‖schedule.height u‖) ^ K =
        C * (1 + ‖path.im‖) ^ K :=
    congrArg
      (fun r : ℝ => C * (1 + r) ^ K)
      heightEquality.symm
  Eq.subst
    (motive := fun target : ℝ =>
      ‖completedZetaNegLogDeriv path‖ ≤ target)
    targetEquality
    (topBound u x hx)

theorem zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_bound_of_bottom_path
    (f : ZetaAdmissibleFunction) (K : ℕ) (C : ℝ)
    (bottomBound :
      ∀ u x : ℝ,
        x ∈ Set.uIcc
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
          (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
        ‖completedZetaNegLogDeriv
          (zetaCompletedExplicitFormulaBottomPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x)‖ ≤
          C *
            (1 +
              ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K)
    (u x : ℝ)
    (hx :
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :
    let path : ℂ :=
      zetaCompletedExplicitFormulaBottomPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
          ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
        x
    ‖completedZetaNegLogDeriv path‖ ≤
      C * (1 + ‖path.im‖) ^ K :=
  let family : ExplicitFormulaContourFamily :=
    zetaCompletedExplicitFormula_autocorrelation_contourFamily f
  let schedule : ExplicitFormulaCofinalHeightSchedule family :=
    zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f
  let path : ℂ :=
    zetaCompletedExplicitFormulaBottomPath
      (family.rectangle (schedule.height u)) x
  let heightEquality :
      ‖path.im‖ = ‖schedule.height u‖ :=
    zetaCompletedExplicitFormulaBottomPath_im_norm
      (family.rectangle (schedule.height u)) x
  let targetEquality :
      C * (1 + ‖schedule.height u‖) ^ K =
        C * (1 + ‖path.im‖) ^ K :=
    congrArg
      (fun r : ℝ => C * (1 + r) ^ K)
      heightEquality.symm
  Eq.subst
    (motive := fun target : ℝ =>
      ‖completedZetaNegLogDeriv path‖ ≤ target)
    targetEquality
    (bottomBound u x hx)

theorem zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_bound_of_pathBounds
    (f : ZetaAdmissibleFunction) (K : ℕ) (C : ℝ)
    (topBound :
      ∀ u x : ℝ,
        x ∈ Set.uIcc
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
          (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
        ‖completedZetaNegLogDeriv
          (zetaCompletedExplicitFormulaTopPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x)‖ ≤
          C *
            (1 +
              ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K)
    (bottomBound :
      ∀ u x : ℝ,
        x ∈ Set.uIcc
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
          (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
        ‖completedZetaNegLogDeriv
          (zetaCompletedExplicitFormulaBottomPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x)‖ ≤
          C *
            (1 +
              ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K)
    (z : ℂ)
    (hz :
      z ∈
        (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).carrier) :
    ‖completedZetaNegLogDeriv z‖ ≤
      C * (1 + ‖z.im‖) ^ K :=
  zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_norm_bound_of_pathBounds
    f completedZetaNegLogDeriv K C topBound bottomBound z hz

def zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalPolynomialLogDerivControl_of_pathBounds
    (f : ZetaAdmissibleFunction) (K : ℕ) (C : ℝ)
    (C_pos : 0 < C)
    (topBound :
      ∀ u x : ℝ,
        x ∈ Set.uIcc
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
          (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
        ‖completedZetaNegLogDeriv
          (zetaCompletedExplicitFormulaTopPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x)‖ ≤
          C *
            (1 +
              ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K)
    (bottomBound :
      ∀ u x : ℝ,
        x ∈ Set.uIcc
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
          (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
        ‖completedZetaNegLogDeriv
          (zetaCompletedExplicitFormulaBottomPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x)‖ ≤
          C *
            (1 +
              ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K) :
    ExplicitFormulaScheduledHorizontalPolynomialLogDerivControl
      (convolutionAutocorrelation f)
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
      (zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f) :=
  { carrier :=
      zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f
    top_mem :=
      zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_top_mem
        f
    bottom_mem :=
      zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_bottom_mem
        f
    growth_degree := K
    bound_constant := C
    bound_constant_pos := C_pos
    bound :=
      zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_bound_of_pathBounds
        f K C topBound bottomBound }

def zetaCompletedExplicitFormulaAutocorrelationScheduledPolynomialFamilyAnalyticPackage_of_pathBounds
    (f : ZetaAdmissibleFunction) (K : ℕ) (C : ℝ)
    (C_pos : 0 < C)
    (topBound :
      ∀ u x : ℝ,
        x ∈ Set.uIcc
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
          (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
        ‖completedZetaNegLogDeriv
          (zetaCompletedExplicitFormulaTopPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x)‖ ≤
          C *
            (1 +
              ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K)
    (bottomBound :
      ∀ u x : ℝ,
        x ∈ Set.uIcc
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
          (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
        ‖completedZetaNegLogDeriv
          (zetaCompletedExplicitFormulaBottomPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x)‖ ≤
          C *
            (1 +
              ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K) :
    ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
      (convolutionAutocorrelation f)
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f) :=
  { phi_control :=
      (zetaPhiAnalyticControl_autocorrelation_of_concreteControl
        zetaPhiAutocorrelationConcreteControl_owner) f
    height_schedule :=
      zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f
    horizontal_logderiv_control :=
      zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalPolynomialLogDerivControl_of_pathBounds
        f K C C_pos topBound bottomBound }

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
