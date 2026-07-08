import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.Cancellation.Owner

/-!
# Reduction closure for formal localization words

This file owns the generated word relation obtained from primitive cancellation
cells by symmetry, transitivity, and word contexts.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The generated relation on formal localization words. -/
inductive TraceLocalizationWordRelation :
    {source target : TraceCorQObject} →
      TraceLocalizationWord source target →
      TraceLocalizationWord source target →
      Type where
  | ofReduction
      {source target : TraceCorQObject}
      {left right : TraceLocalizationWord source target}
      (reduction : TraceLocalizationWordReduction left right) :
      TraceLocalizationWordRelation left right
  | refl
      {source target : TraceCorQObject}
      (word : TraceLocalizationWord source target) :
      TraceLocalizationWordRelation word word
  | symm
      {source target : TraceCorQObject}
      {left right : TraceLocalizationWord source target}
      (relation : TraceLocalizationWordRelation left right) :
      TraceLocalizationWordRelation right left
  | trans
      {source target : TraceCorQObject}
      {left middle right : TraceLocalizationWord source target}
      (first : TraceLocalizationWordRelation left middle)
      (second : TraceLocalizationWordRelation middle right) :
      TraceLocalizationWordRelation left right
  | prefixStep
      {first second third : TraceCorQObject}
      {left right : TraceLocalizationWord second third}
      (prefixWord : TraceLocalizationWord first second)
      (relation : TraceLocalizationWordRelation left right) :
      TraceLocalizationWordRelation
        (TraceLocalizationWord.comp prefixWord left)
        (TraceLocalizationWord.comp prefixWord right)
  | suffix
      {first second third : TraceCorQObject}
      {left right : TraceLocalizationWord first second}
      (relation : TraceLocalizationWordRelation left right)
      (suffix : TraceLocalizationWord second third) :
      TraceLocalizationWordRelation
        (TraceLocalizationWord.comp left suffix)
        (TraceLocalizationWord.comp right suffix)

/-- A primitive reduction generates a word relation. -/
def TraceLocalizationWordRelation.ofCancellation
    {source target : TraceCorQObject}
    {left right : TraceLocalizationWord source target}
    (reduction : TraceLocalizationWordReduction left right) :
    TraceLocalizationWordRelation left right :=
  TraceLocalizationWordRelation.ofReduction reduction

/-- The named cancellation relation is the primitive-reduction constructor. -/
theorem TraceLocalizationWordRelation.ofCancellation_eq_ofReduction
    {source target : TraceCorQObject}
    {left right : TraceLocalizationWord source target}
    (reduction : TraceLocalizationWordReduction left right) :
    TraceLocalizationWordRelation.ofCancellation reduction =
      TraceLocalizationWordRelation.ofReduction reduction :=
  rfl

/-- Forward-inverse cancellation generates a word relation. -/
def TraceLocalizationWordRelation.forwardInverse
    (input : TraceLocalizationInput) :
    TraceLocalizationWordRelation
      (TraceLocalizationWord.forwardThenInverse input)
      (TraceLocalizationWord.identity input.sourceObject) :=
  TraceLocalizationWordRelation.ofCancellation
    (TraceLocalizationWordReduction.forwardInverseCell input)

/-- Inverse-forward cancellation generates a word relation. -/
def TraceLocalizationWordRelation.inverseForward
    (input : TraceLocalizationInput) :
    TraceLocalizationWordRelation
      (TraceLocalizationWord.inverseThenForward input)
      (TraceLocalizationWord.identity input.targetObject) :=
  TraceLocalizationWordRelation.ofCancellation
    (TraceLocalizationWordReduction.inverseForwardCell input)

/-- A word relation can be placed after a fixed prefix word. -/
def TraceLocalizationWordRelation.withPrefix
    {first second third : TraceCorQObject}
    {left right : TraceLocalizationWord second third}
    (prefixWord : TraceLocalizationWord first second)
    (relation : TraceLocalizationWordRelation left right) :
    TraceLocalizationWordRelation
      (TraceLocalizationWord.comp prefixWord left)
      (TraceLocalizationWord.comp prefixWord right) :=
  TraceLocalizationWordRelation.prefixStep prefixWord relation

/-- A word relation can be placed before a fixed suffix word. -/
def TraceLocalizationWordRelation.withSuffix
    {first second third : TraceCorQObject}
    {left right : TraceLocalizationWord first second}
    (relation : TraceLocalizationWordRelation left right)
    (suffix : TraceLocalizationWord second third) :
    TraceLocalizationWordRelation
      (TraceLocalizationWord.comp left suffix)
      (TraceLocalizationWord.comp right suffix) :=
  TraceLocalizationWordRelation.suffix relation suffix

/-- Prefix context closure is the prefix-step constructor. -/
theorem TraceLocalizationWordRelation.withPrefix_eq_prefixStep
    {first second third : TraceCorQObject}
    {left right : TraceLocalizationWord second third}
    (prefixWord : TraceLocalizationWord first second)
    (relation : TraceLocalizationWordRelation left right) :
    TraceLocalizationWordRelation.withPrefix prefixWord relation =
      TraceLocalizationWordRelation.prefixStep prefixWord relation :=
  rfl

/-- Suffix context closure is the suffix constructor. -/
theorem TraceLocalizationWordRelation.withSuffix_eq_suffix
    {first second third : TraceCorQObject}
    {left right : TraceLocalizationWord first second}
    (relation : TraceLocalizationWordRelation left right)
    (suffix : TraceLocalizationWord second third) :
    TraceLocalizationWordRelation.withSuffix relation suffix =
      TraceLocalizationWordRelation.suffix relation suffix :=
  rfl

/-- The named forward-inverse relation is generated by the corresponding cancellation cell. -/
theorem TraceLocalizationWordRelation.forwardInverse_eq_ofCancellation
    (input : TraceLocalizationInput) :
    TraceLocalizationWordRelation.forwardInverse input =
      TraceLocalizationWordRelation.ofCancellation
        (TraceLocalizationWordReduction.forwardInverseCell input) :=
  rfl

/-- Forward-inverse cancellation relates a two-atom word to a zero-atom identity. -/
theorem TraceLocalizationWordRelation.forwardInverse_atomCounts
    (input : TraceLocalizationInput) :
    (TraceLocalizationWord.forwardThenInverse input).atomCount =
        (0 + 1) + (0 + 1) ∧
      (TraceLocalizationWord.identity input.sourceObject).atomCount =
        0 :=
  And.intro
    (TraceLocalizationWord.forwardThenInverse_atomCount input)
    rfl

/-- The named inverse-forward relation is generated by the corresponding cancellation cell. -/
theorem TraceLocalizationWordRelation.inverseForward_eq_ofCancellation
    (input : TraceLocalizationInput) :
    TraceLocalizationWordRelation.inverseForward input =
      TraceLocalizationWordRelation.ofCancellation
        (TraceLocalizationWordReduction.inverseForwardCell input) :=
  rfl

/-- Inverse-forward cancellation relates a two-atom word to a zero-atom identity. -/
theorem TraceLocalizationWordRelation.inverseForward_atomCounts
    (input : TraceLocalizationInput) :
    (TraceLocalizationWord.inverseThenForward input).atomCount =
        (0 + 1) + (0 + 1) ∧
      (TraceLocalizationWord.identity input.targetObject).atomCount =
        0 :=
  And.intro
    (TraceLocalizationWord.inverseThenForward_atomCount input)
    rfl

end AnalyticMotives
end LFunctions
end Boundary
