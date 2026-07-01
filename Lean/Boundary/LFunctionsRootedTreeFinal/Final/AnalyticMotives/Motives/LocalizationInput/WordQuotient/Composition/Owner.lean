import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Owner

/-!
# Composition of formal localized word classes

This file descends concatenation of formal localization words to quotient
classes.  Compatibility is supplied by the prefix and suffix closure
constructors of the generated word relation.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Composition of formal localized word classes. -/
def TraceLocalizationWordClass.comp
    {first second third : TraceCorQObject}
    (left : TraceLocalizationWordClass first second)
    (right : TraceLocalizationWordClass second third) :
    TraceLocalizationWordClass first third :=
  Quotient.liftOn₂
    left
    right
    (fun leftWord rightWord =>
      TraceLocalizationWordClass.ofWord
        (TraceLocalizationWord.comp leftWord rightWord))
    (fun left₁ right₁ left₂ right₂ leftRelation rightRelation =>
      match leftRelation with
      | Nonempty.intro leftWitness =>
          match rightRelation with
          | Nonempty.intro rightWitness =>
              TraceLocalizationWordClass.sound
                (TraceLocalizationWordRelation.trans
                  (TraceLocalizationWordRelation.withSuffix
                    leftWitness
                    right₁)
                  (TraceLocalizationWordRelation.withPrefix
                    left₂
                    rightWitness)))

/-- Composition of represented word classes is represented by word concatenation. -/
theorem TraceLocalizationWordClass.comp_ofWord
    {first second third : TraceCorQObject}
    (left : TraceLocalizationWord first second)
    (right : TraceLocalizationWord second third) :
    TraceLocalizationWordClass.comp
        (TraceLocalizationWordClass.ofWord left)
        (TraceLocalizationWordClass.ofWord right) =
      TraceLocalizationWordClass.ofWord
        (TraceLocalizationWord.comp left right) :=
  rfl

/-- Right identity for formal localized word-class composition. -/
theorem TraceLocalizationWordClass.comp_identity_right
    {source target : TraceCorQObject}
    (wordClass : TraceLocalizationWordClass source target) :
    TraceLocalizationWordClass.comp
        wordClass
        (TraceLocalizationWordClass.identity target) =
      wordClass :=
  Quotient.inductionOn
    wordClass
    (fun word =>
      rfl)

/-- Left identity for formal localized word-class composition. -/
theorem TraceLocalizationWordClass.comp_identity_left
    {source target : TraceCorQObject}
    (wordClass : TraceLocalizationWordClass source target) :
    TraceLocalizationWordClass.comp
        (TraceLocalizationWordClass.identity source)
        wordClass =
      wordClass :=
  Quotient.inductionOn
    wordClass
    (fun word =>
      congrArg
        (fun reducedWord =>
          TraceLocalizationWordClass.ofWord reducedWord)
        (TraceLocalizationWord.comp_identity_left word))

/-- Associativity for formal localized word-class composition. -/
theorem TraceLocalizationWordClass.comp_assoc
    {first second third fourth : TraceCorQObject}
    (left : TraceLocalizationWordClass first second)
    (middle : TraceLocalizationWordClass second third)
    (right : TraceLocalizationWordClass third fourth) :
    TraceLocalizationWordClass.comp
        (TraceLocalizationWordClass.comp left middle)
        right =
      TraceLocalizationWordClass.comp
        left
        (TraceLocalizationWordClass.comp middle right) :=
  Quotient.inductionOn
    left
    (fun leftWord =>
      Quotient.inductionOn
        middle
        (fun middleWord =>
          Quotient.inductionOn
            right
            (fun rightWord =>
              congrArg
                (fun word =>
                  TraceLocalizationWordClass.ofWord word)
                (TraceLocalizationWord.comp_assoc
                  leftWord
                  middleWord
                  rightWord))))

/-- Forward input followed by its formal inverse composes to identity. -/
theorem TraceLocalizationWordClass.comp_forward_inverse_eq_identity
    (input : TraceLocalizationInput) :
    TraceLocalizationWordClass.comp
        (TraceLocalizationWordClass.ofInputForward input)
        (TraceLocalizationWordClass.ofInputInverse input) =
      TraceLocalizationWordClass.identity input.sourceObject :=
  TraceLocalizationWordClass.forward_inverse_eq_identity input

/-- Formal inverse followed by forward input composes to identity. -/
theorem TraceLocalizationWordClass.comp_inverse_forward_eq_identity
    (input : TraceLocalizationInput) :
    TraceLocalizationWordClass.comp
        (TraceLocalizationWordClass.ofInputInverse input)
        (TraceLocalizationWordClass.ofInputForward input) =
      TraceLocalizationWordClass.identity input.targetObject :=
  TraceLocalizationWordClass.inverse_forward_eq_identity input

end AnalyticMotives
end LFunctions
end Boundary
