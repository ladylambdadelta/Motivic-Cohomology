import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Owner

/-!
# Word representatives of unstable input arrows

This file records that the unstable forward and inverse arrows attached to a
localization input are exactly the localized classes of the corresponding
one-step trace words.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The unstable forward arrow is the forward input word class. -/
theorem TraceLocalizationInput.unstableForward_eq_wordClass
    (input : TraceLocalizationInput) :
    input.unstableForward =
      TraceLocalizationWordClass.ofInputForward input :=
  TraceLocalizationInput.localizedForwardArrow_eq_wordClass
    input

/-- The unstable forward arrow is represented by the one-forward-input word. -/
theorem TraceLocalizationInput.unstableForward_eq_ofWord
    (input : TraceLocalizationInput) :
    input.unstableForward =
      TraceLocalizationWordClass.ofWord
        (TraceLocalizationWord.ofInputForward input) :=
  TraceLocalizationInput.localizedForwardArrow_eq_ofWord
    input

/-- The chosen word representative of the unstable forward arrow has one atom. -/
theorem TraceLocalizationInput.unstableForward_representative_atomCount
    (input : TraceLocalizationInput) :
    (TraceLocalizationWord.ofInputForward input).atomCount =
      0 + 1 :=
  TraceLocalizationInput.localizedForwardArrow_representative_atomCount
    input

/-- The unstable inverse arrow is the inverse input word class. -/
theorem TraceLocalizationInput.unstableInverse_eq_wordClass
    (input : TraceLocalizationInput) :
    input.unstableInverse =
      TraceLocalizationWordClass.ofInputInverse input :=
  TraceLocalizationInput.localizedInverseArrow_eq_wordClass
    input

/-- The unstable inverse arrow is represented by the one-inverse-input word. -/
theorem TraceLocalizationInput.unstableInverse_eq_ofWord
    (input : TraceLocalizationInput) :
    input.unstableInverse =
      TraceLocalizationWordClass.ofWord
        (TraceLocalizationWord.ofInputInverse input) :=
  TraceLocalizationInput.localizedInverseArrow_eq_ofWord
    input

/-- The chosen word representative of the unstable inverse arrow has one atom. -/
theorem TraceLocalizationInput.unstableInverse_representative_atomCount
    (input : TraceLocalizationInput) :
    (TraceLocalizationWord.ofInputInverse input).atomCount =
      0 + 1 :=
  TraceLocalizationInput.localizedInverseArrow_representative_atomCount
    input

end AnalyticMotives
end LFunctions
end Boundary
