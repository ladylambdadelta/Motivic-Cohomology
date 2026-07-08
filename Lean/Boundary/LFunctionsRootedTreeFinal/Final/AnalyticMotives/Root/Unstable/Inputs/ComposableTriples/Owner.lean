import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.ComposableTriples.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Unstable.Inputs.ComposableTriples.ForwardWords.Owner

/-!
# Public composable triples inside the unstable envelope

This file exposes unstable endpoint facts for composable triples through the
public analytic-motives root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: the first unstable source is the triple source localized object. -/
theorem AnalyticMotivesRoot.first_unstableSource_eq_sourceLocalizedObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.first.unstableSource =
      triple.sourceLocalizedObject :=
  TraceAnalyticMotive.first_unstableSource_eq_sourceLocalizedObject
    triple

/-- Public wrapper: the first unstable target is the first middle localized object. -/
theorem AnalyticMotivesRoot.first_unstableTarget_eq_firstMiddleLocalizedObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.first.unstableTarget =
      triple.firstMiddleLocalizedObject :=
  TraceAnalyticMotive.first_unstableTarget_eq_firstMiddleLocalizedObject
    triple

/-- Public wrapper: the second unstable source is the first middle localized object. -/
theorem AnalyticMotivesRoot.second_unstableSource_eq_firstMiddleLocalizedObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.second.unstableSource =
      triple.firstMiddleLocalizedObject :=
  TraceAnalyticMotive.second_unstableSource_eq_firstMiddleLocalizedObject
    triple

/-- Public wrapper: the second unstable target is the second middle localized object. -/
theorem AnalyticMotivesRoot.second_unstableTarget_eq_secondMiddleLocalizedObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.second.unstableTarget =
      triple.secondMiddleLocalizedObject :=
  TraceAnalyticMotive.second_unstableTarget_eq_secondMiddleLocalizedObject
    triple

/-- Public wrapper: the third unstable source is the second middle localized object. -/
theorem AnalyticMotivesRoot.third_unstableSource_eq_secondMiddleLocalizedObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.third.unstableSource =
      triple.secondMiddleLocalizedObject :=
  TraceAnalyticMotive.third_unstableSource_eq_secondMiddleLocalizedObject
    triple

/-- Public wrapper: the third unstable target is the triple target localized object. -/
theorem AnalyticMotivesRoot.third_unstableTarget_eq_targetLocalizedObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.third.unstableTarget =
      triple.targetLocalizedObject :=
  TraceAnalyticMotive.third_unstableTarget_eq_targetLocalizedObject
    triple

/-- Public wrapper: the first unstable target is the second unstable source. -/
theorem AnalyticMotivesRoot.first_unstableTarget_eq_second_unstableSource
    (triple : TraceLocalizationInputComposableTriple) :
    triple.first.unstableTarget =
      triple.second.unstableSource :=
  TraceAnalyticMotive.first_unstableTarget_eq_second_unstableSource
    triple

/-- Public wrapper: the second unstable target is the third unstable source. -/
theorem AnalyticMotivesRoot.second_unstableTarget_eq_third_unstableSource
    (triple : TraceLocalizationInputComposableTriple) :
    triple.second.unstableTarget =
      triple.third.unstableSource :=
  TraceAnalyticMotive.second_unstableTarget_eq_third_unstableSource
    triple

end AnalyticMotives
end LFunctions
end Boundary
