import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Descent.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.IntervalHomotopy.Generators.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.IntervalHomotopy.Localization.Owner

/-!
# Analytic interval homotopy

This file owns the analytic homotopy localization corresponding to interval
deformation of trace presentations.

This is the analytic analogue of homotopy invariance, phrased through
deformation of certified trace presentations.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open scoped CategoryTheory

/-- Interval Stokes has the named localized forward arrow as hom. -/
theorem TraceIntervalHomotopy.stokesIso_hom
    (source target : QTraceExpression) :
    (TraceIntervalHomotopyLocalization.stokesIso source target).hom =
      TraceLocalizationInput.intervalStokesForwardArrow source target :=
  TraceIntervalHomotopyLocalization.stokesIso_hom
    source
    target

/-- Interval Stokes has the named localized inverse arrow as inverse. -/
theorem TraceIntervalHomotopy.stokesIso_inv
    (source target : QTraceExpression) :
    (TraceIntervalHomotopyLocalization.stokesIso source target).inv =
      TraceLocalizationInput.intervalStokesInverseArrow source target :=
  TraceIntervalHomotopyLocalization.stokesIso_inv
    source
    target

/-- Interval Stokes hom followed by inverse is identity in the localization quotient. -/
theorem TraceIntervalHomotopy.stokesIso_hom_comp_inv
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceIntervalHomotopyLocalization.stokesIso source target).hom
        (TraceIntervalHomotopyLocalization.stokesIso source target).inv =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.intervalStokes source target).sourceObject :=
  TraceIntervalHomotopyLocalization.stokesIso_hom_comp_inv
    source
    target

/-- Interval Stokes inverse followed by hom is identity in the localization quotient. -/
theorem TraceIntervalHomotopy.stokesIso_inv_comp_hom
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceIntervalHomotopyLocalization.stokesIso source target).inv
        (TraceIntervalHomotopyLocalization.stokesIso source target).hom =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.intervalStokes source target).targetObject :=
  TraceIntervalHomotopyLocalization.stokesIso_inv_comp_hom
    source
    target

/-- Interval Stokes hom followed by inverse is categorical identity. -/
theorem TraceIntervalHomotopy.stokesIso_hom_comp_inv_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceIntervalHomotopyLocalization.stokesIso source target).hom ≫
        (TraceIntervalHomotopyLocalization.stokesIso source target).inv =
      (𝟙 (TraceLocalizationInput.intervalStokes source target).localizedSourceObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.intervalStokes source target).localizedSourceObject
          (TraceLocalizationInput.intervalStokes source target).localizedSourceObject) :=
  TraceIntervalHomotopyLocalization.stokesIso_hom_comp_inv_eq_categoryIdentity
    source
    target

/-- Interval Stokes inverse followed by hom is categorical identity. -/
theorem TraceIntervalHomotopy.stokesIso_inv_comp_hom_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceIntervalHomotopyLocalization.stokesIso source target).inv ≫
        (TraceIntervalHomotopyLocalization.stokesIso source target).hom =
      (𝟙 (TraceLocalizationInput.intervalStokes source target).localizedTargetObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.intervalStokes source target).localizedTargetObject
          (TraceLocalizationInput.intervalStokes source target).localizedTargetObject) :=
  TraceIntervalHomotopyLocalization.stokesIso_inv_comp_hom_eq_categoryIdentity
    source
    target

/-- Interval Fubini has the named localized forward arrow as hom. -/
theorem TraceIntervalHomotopy.fubiniIso_hom
    (source target : QTraceExpression) :
    (TraceIntervalHomotopyLocalization.fubiniIso source target).hom =
      TraceLocalizationInput.intervalFubiniForwardArrow source target :=
  TraceIntervalHomotopyLocalization.fubiniIso_hom
    source
    target

/-- Interval Fubini has the named localized inverse arrow as inverse. -/
theorem TraceIntervalHomotopy.fubiniIso_inv
    (source target : QTraceExpression) :
    (TraceIntervalHomotopyLocalization.fubiniIso source target).inv =
      TraceLocalizationInput.intervalFubiniInverseArrow source target :=
  TraceIntervalHomotopyLocalization.fubiniIso_inv
    source
    target

/-- Interval Fubini hom followed by inverse is identity in the localization quotient. -/
theorem TraceIntervalHomotopy.fubiniIso_hom_comp_inv
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceIntervalHomotopyLocalization.fubiniIso source target).hom
        (TraceIntervalHomotopyLocalization.fubiniIso source target).inv =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.intervalFubini source target).sourceObject :=
  TraceIntervalHomotopyLocalization.fubiniIso_hom_comp_inv
    source
    target

/-- Interval Fubini inverse followed by hom is identity in the localization quotient. -/
theorem TraceIntervalHomotopy.fubiniIso_inv_comp_hom
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceIntervalHomotopyLocalization.fubiniIso source target).inv
        (TraceIntervalHomotopyLocalization.fubiniIso source target).hom =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.intervalFubini source target).targetObject :=
  TraceIntervalHomotopyLocalization.fubiniIso_inv_comp_hom
    source
    target

/-- Interval Fubini hom followed by inverse is categorical identity. -/
theorem TraceIntervalHomotopy.fubiniIso_hom_comp_inv_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceIntervalHomotopyLocalization.fubiniIso source target).hom ≫
        (TraceIntervalHomotopyLocalization.fubiniIso source target).inv =
      (𝟙 (TraceLocalizationInput.intervalFubini source target).localizedSourceObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.intervalFubini source target).localizedSourceObject
          (TraceLocalizationInput.intervalFubini source target).localizedSourceObject) :=
  TraceIntervalHomotopyLocalization.fubiniIso_hom_comp_inv_eq_categoryIdentity
    source
    target

/-- Interval Fubini inverse followed by hom is categorical identity. -/
theorem TraceIntervalHomotopy.fubiniIso_inv_comp_hom_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceIntervalHomotopyLocalization.fubiniIso source target).inv ≫
        (TraceIntervalHomotopyLocalization.fubiniIso source target).hom =
      (𝟙 (TraceLocalizationInput.intervalFubini source target).localizedTargetObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.intervalFubini source target).localizedTargetObject
          (TraceLocalizationInput.intervalFubini source target).localizedTargetObject) :=
  TraceIntervalHomotopyLocalization.fubiniIso_inv_comp_hom_eq_categoryIdentity
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
