import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.Words.Owner

/-!
# Cancellation cells for formal localization words

This file owns the formal cancellation cells that make localization-input
atoms invertible in the later localized word calculus.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The formal word consisting of a generator followed by its formal inverse. -/
def TraceLocalizationWord.forwardThenInverse
    (input : TraceLocalizationInput) :
    TraceLocalizationWord input.sourceObject input.sourceObject :=
  TraceLocalizationWord.comp
    (TraceLocalizationWord.ofInputForward input)
    (TraceLocalizationWord.ofInputInverse input)

/-- The formal word consisting of a formal inverse followed by its generator. -/
def TraceLocalizationWord.inverseThenForward
    (input : TraceLocalizationInput) :
    TraceLocalizationWord input.targetObject input.targetObject :=
  TraceLocalizationWord.comp
    (TraceLocalizationWord.ofInputInverse input)
    (TraceLocalizationWord.ofInputForward input)

/-- Forward then inverse is the concatenation of the corresponding one-atom words. -/
theorem TraceLocalizationWord.forwardThenInverse_eq_comp
    (input : TraceLocalizationInput) :
    TraceLocalizationWord.forwardThenInverse input =
      TraceLocalizationWord.comp
        (TraceLocalizationWord.ofInputForward input)
        (TraceLocalizationWord.ofInputInverse input) :=
  rfl

/-- Inverse then forward is the concatenation of the corresponding one-atom words. -/
theorem TraceLocalizationWord.inverseThenForward_eq_comp
    (input : TraceLocalizationInput) :
    TraceLocalizationWord.inverseThenForward input =
      TraceLocalizationWord.comp
        (TraceLocalizationWord.ofInputInverse input)
        (TraceLocalizationWord.ofInputForward input) :=
  rfl

/-- Primitive reduction cells in the formal localization word calculus. -/
inductive TraceLocalizationWordReduction :
    {source target : TraceCorQObject} →
      TraceLocalizationWord source target →
      TraceLocalizationWord source target →
      Type where
  | forwardInverse (input : TraceLocalizationInput) :
      TraceLocalizationWordReduction
        (TraceLocalizationWord.forwardThenInverse input)
        (TraceLocalizationWord.identity input.sourceObject)
  | inverseForward (input : TraceLocalizationInput) :
      TraceLocalizationWordReduction
        (TraceLocalizationWord.inverseThenForward input)
        (TraceLocalizationWord.identity input.targetObject)

/-- The forward-inverse cancellation cell for a localization input. -/
def TraceLocalizationWordReduction.forwardInverseCell
    (input : TraceLocalizationInput) :
    TraceLocalizationWordReduction
      (TraceLocalizationWord.forwardThenInverse input)
      (TraceLocalizationWord.identity input.sourceObject) :=
  TraceLocalizationWordReduction.forwardInverse input

/-- The inverse-forward cancellation cell for a localization input. -/
def TraceLocalizationWordReduction.inverseForwardCell
    (input : TraceLocalizationInput) :
    TraceLocalizationWordReduction
      (TraceLocalizationWord.inverseThenForward input)
      (TraceLocalizationWord.identity input.targetObject) :=
  TraceLocalizationWordReduction.inverseForward input

/-- The forward-inverse named cell is the primitive forward-inverse constructor. -/
theorem TraceLocalizationWordReduction.forwardInverseCell_eq_constructor
    (input : TraceLocalizationInput) :
    TraceLocalizationWordReduction.forwardInverseCell input =
      TraceLocalizationWordReduction.forwardInverse input :=
  rfl

/-- The inverse-forward named cell is the primitive inverse-forward constructor. -/
theorem TraceLocalizationWordReduction.inverseForwardCell_eq_constructor
    (input : TraceLocalizationInput) :
    TraceLocalizationWordReduction.inverseForwardCell input =
      TraceLocalizationWordReduction.inverseForward input :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
