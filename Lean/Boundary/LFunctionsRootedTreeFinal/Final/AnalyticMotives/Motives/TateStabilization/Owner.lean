import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.IntervalHomotopy.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.TateStabilization.Generators.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.TateStabilization.Localization.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Owner

/-!
# Tate stabilization

This file owns the stabilization step that inverts the analytic Tate object.

The Tate object arises from the trace calculus itself, via the analytic
weight-shift and residue normalizations, before comparison with geometric
motives.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open scoped CategoryTheory

/-- Tate weight-drop has the named localized forward arrow as hom. -/
theorem TraceTateStabilization.weightDropIso_hom
    (source target : QTraceExpression) :
    (TraceTateStabilizationLocalization.weightDropIso source target).hom =
      TraceLocalizationInput.tateWeightDropForwardArrow source target :=
  TraceTateStabilizationLocalization.weightDropIso_hom
    source
    target

/-- Tate weight-drop has the named localized inverse arrow as inverse. -/
theorem TraceTateStabilization.weightDropIso_inv
    (source target : QTraceExpression) :
    (TraceTateStabilizationLocalization.weightDropIso source target).inv =
      TraceLocalizationInput.tateWeightDropInverseArrow source target :=
  TraceTateStabilizationLocalization.weightDropIso_inv
    source
    target

/-- Tate weight-drop hom followed by inverse is identity in the localization quotient. -/
theorem TraceTateStabilization.weightDropIso_hom_comp_inv
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceTateStabilizationLocalization.weightDropIso source target).hom
        (TraceTateStabilizationLocalization.weightDropIso source target).inv =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.tateWeightDrop source target).sourceObject :=
  TraceTateStabilizationLocalization.weightDropIso_hom_comp_inv
    source
    target

/-- Tate weight-drop inverse followed by hom is identity in the localization quotient. -/
theorem TraceTateStabilization.weightDropIso_inv_comp_hom
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceTateStabilizationLocalization.weightDropIso source target).inv
        (TraceTateStabilizationLocalization.weightDropIso source target).hom =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.tateWeightDrop source target).targetObject :=
  TraceTateStabilizationLocalization.weightDropIso_inv_comp_hom
    source
    target

/-- Tate weight-drop hom followed by inverse is categorical identity. -/
theorem TraceTateStabilization.weightDropIso_hom_comp_inv_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceTateStabilizationLocalization.weightDropIso source target).hom ≫
        (TraceTateStabilizationLocalization.weightDropIso source target).inv =
      (𝟙 (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject
          (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject) :=
  TraceTateStabilizationLocalization.weightDropIso_hom_comp_inv_eq_categoryIdentity
    source
    target

/-- Tate weight-drop inverse followed by hom is categorical identity. -/
theorem TraceTateStabilization.weightDropIso_inv_comp_hom_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceTateStabilizationLocalization.weightDropIso source target).inv ≫
        (TraceTateStabilizationLocalization.weightDropIso source target).hom =
      (𝟙 (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject
          (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject) :=
  TraceTateStabilizationLocalization.weightDropIso_inv_comp_hom_eq_categoryIdentity
    source
    target

/-- Tate stabilization uses the unstable-envelope Tate weight-drop isomorphism. -/
theorem TraceTateStabilization.weightDropUnstableIso_eq
    (source target : QTraceExpression) :
    TraceUnstableAnalyticMotive.tateWeightDropIso source target =
      TraceLocalizationInput.tateWeightDropLocalizedIso source target :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_eq
    source
    target

/-- The unstable Tate weight-drop hom is the named localized forward arrow. -/
theorem TraceTateStabilization.weightDropUnstableIso_hom
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom =
      TraceLocalizationInput.tateWeightDropForwardArrow source target :=
  rfl

/-- The unstable Tate weight-drop inverse is the named localized inverse arrow. -/
theorem TraceTateStabilization.weightDropUnstableIso_inv
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv =
      TraceLocalizationInput.tateWeightDropInverseArrow source target :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
