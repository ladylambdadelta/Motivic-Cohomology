import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.Representatives.Owner

/-!
# Root wrappers for unstable input representatives

This file exposes the concrete one-step word representatives of unstable
localization-input arrows through the motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Root wrapper: the unstable forward arrow is the forward input word class. -/
theorem TraceAnalyticMotive.unstableForward_eq_wordClass
    (input : TraceLocalizationInput) :
    input.unstableForward =
      TraceLocalizationWordClass.ofInputForward input :=
  TraceLocalizationInput.unstableForward_eq_wordClass
    input

/-- Root wrapper: the unstable forward arrow is represented by the forward input word. -/
theorem TraceAnalyticMotive.unstableForward_eq_ofWord
    (input : TraceLocalizationInput) :
    input.unstableForward =
      TraceLocalizationWordClass.ofWord
        (TraceLocalizationWord.ofInputForward input) :=
  TraceLocalizationInput.unstableForward_eq_ofWord
    input

/-- Root wrapper: the unstable forward chosen representative has one atom. -/
theorem TraceAnalyticMotive.unstableForward_representative_atomCount
    (input : TraceLocalizationInput) :
    (TraceLocalizationWord.ofInputForward input).atomCount =
      0 + 1 :=
  TraceLocalizationInput.unstableForward_representative_atomCount
    input

/-- Root wrapper: the unstable inverse arrow is the inverse input word class. -/
theorem TraceAnalyticMotive.unstableInverse_eq_wordClass
    (input : TraceLocalizationInput) :
    input.unstableInverse =
      TraceLocalizationWordClass.ofInputInverse input :=
  TraceLocalizationInput.unstableInverse_eq_wordClass
    input

/-- Root wrapper: the unstable inverse arrow is represented by the inverse input word. -/
theorem TraceAnalyticMotive.unstableInverse_eq_ofWord
    (input : TraceLocalizationInput) :
    input.unstableInverse =
      TraceLocalizationWordClass.ofWord
        (TraceLocalizationWord.ofInputInverse input) :=
  TraceLocalizationInput.unstableInverse_eq_ofWord
    input

/-- Root wrapper: the unstable inverse chosen representative has one atom. -/
theorem TraceAnalyticMotive.unstableInverse_representative_atomCount
    (input : TraceLocalizationInput) :
    (TraceLocalizationWord.ofInputInverse input).atomCount =
      0 + 1 :=
  TraceLocalizationInput.unstableInverse_representative_atomCount
    input

end AnalyticMotives
end LFunctions
end Boundary
