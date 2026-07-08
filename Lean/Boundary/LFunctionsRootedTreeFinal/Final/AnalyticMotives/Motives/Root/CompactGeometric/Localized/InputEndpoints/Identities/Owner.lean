import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.Identities.Owner

/-!
# Motive-root identity morphisms at localization-input endpoints

This file exposes source and target endpoint identity facts for localization
inputs through the motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root wrapper: source endpoint identity has the identity trace hom. -/
theorem TraceAnalyticMotive.localizationInput_sourceGenerator_id_traceHom
    (input : TraceLocalizationInput) :
    (𝟙 input.sourceGenerator :
        input.sourceGenerator ⟶ input.sourceGenerator).traceHom =
      𝟙 input.sourceObject :=
  TraceLocalizationInput.sourceGenerator_id_traceHom
    input

/-- Motive-root wrapper: target endpoint identity has the identity trace hom. -/
theorem TraceAnalyticMotive.localizationInput_targetGenerator_id_traceHom
    (input : TraceLocalizationInput) :
    (𝟙 input.targetGenerator :
        input.targetGenerator ⟶ input.targetGenerator).traceHom =
      𝟙 input.targetObject :=
  TraceLocalizationInput.targetGenerator_id_traceHom
    input

/-- Motive-root wrapper: source endpoint identity induces identity source presheaf map. -/
theorem TraceAnalyticMotive.localizationInput_sourceGenerator_id_representableMap
    (input : TraceLocalizationInput) :
    (𝟙 input.sourceGenerator :
        input.sourceGenerator ⟶ input.sourceGenerator).representableMap =
      𝟙 input.sourcePresheaf :=
  TraceLocalizationInput.sourceGenerator_id_representableMap
    input

/-- Motive-root wrapper: target endpoint identity induces identity target presheaf map. -/
theorem TraceAnalyticMotive.localizationInput_targetGenerator_id_representableMap
    (input : TraceLocalizationInput) :
    (𝟙 input.targetGenerator :
        input.targetGenerator ⟶ input.targetGenerator).representableMap =
      𝟙 input.targetPresheaf :=
  TraceLocalizationInput.targetGenerator_id_representableMap
    input

/-- Motive-root wrapper: source localized identity is the source trace identity class. -/
theorem TraceAnalyticMotive.localizationInput_sourceGenerator_localizedIdentity_eq_wordClass
    (input : TraceLocalizationInput) :
    input.sourceGenerator.localizedIdentity =
      TraceLocalizationWordClass.identity input.sourceObject :=
  TraceLocalizationInput.sourceGenerator_localizedIdentity_eq_wordClass
    input

/-- Motive-root wrapper: target localized identity is the target trace identity class. -/
theorem TraceAnalyticMotive.localizationInput_targetGenerator_localizedIdentity_eq_wordClass
    (input : TraceLocalizationInput) :
    input.targetGenerator.localizedIdentity =
      TraceLocalizationWordClass.identity input.targetObject :=
  TraceLocalizationInput.targetGenerator_localizedIdentity_eq_wordClass
    input

/-- Motive-root wrapper: source localized identity is represented by the identity word. -/
theorem TraceAnalyticMotive.localizationInput_sourceGenerator_localizedIdentity_eq_ofWord
    (input : TraceLocalizationInput) :
    input.sourceGenerator.localizedIdentity =
      TraceLocalizationWordClass.ofWord
        (TraceLocalizationWord.identity input.sourceObject) :=
  TraceLocalizationInput.sourceGenerator_localizedIdentity_eq_ofWord
    input

/-- Motive-root wrapper: target localized identity is represented by the identity word. -/
theorem TraceAnalyticMotive.localizationInput_targetGenerator_localizedIdentity_eq_ofWord
    (input : TraceLocalizationInput) :
    input.targetGenerator.localizedIdentity =
      TraceLocalizationWordClass.ofWord
        (TraceLocalizationWord.identity input.targetObject) :=
  TraceLocalizationInput.targetGenerator_localizedIdentity_eq_ofWord
    input

/-- Motive-root wrapper: source identity representative has no localization atoms. -/
theorem TraceAnalyticMotive.localizationInput_sourceGenerator_localizedIdentity_representative_atomCount
    (input : TraceLocalizationInput) :
    (TraceLocalizationWord.identity input.sourceObject).atomCount =
      0 :=
  TraceLocalizationInput.sourceGenerator_localizedIdentity_representative_atomCount
    input

/-- Motive-root wrapper: target identity representative has no localization atoms. -/
theorem TraceAnalyticMotive.localizationInput_targetGenerator_localizedIdentity_representative_atomCount
    (input : TraceLocalizationInput) :
    (TraceLocalizationWord.identity input.targetObject).atomCount =
      0 :=
  TraceLocalizationInput.targetGenerator_localizedIdentity_representative_atomCount
    input

end AnalyticMotives
end LFunctions
end Boundary
