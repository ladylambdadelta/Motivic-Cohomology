import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Localized.InputEndpoints.Identities.Owner

/-!
# Public identity morphisms at localization-input endpoints

This file exposes source and target endpoint identity facts for localization
inputs through the public root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: source endpoint identity has the identity trace hom. -/
theorem AnalyticMotivesRoot.localizationInput_sourceGenerator_id_traceHom
    (input : TraceLocalizationInput) :
    (𝟙 input.sourceGenerator :
        input.sourceGenerator ⟶ input.sourceGenerator).traceHom =
      𝟙 input.sourceObject :=
  TraceAnalyticMotive.localizationInput_sourceGenerator_id_traceHom
    input

/-- Public wrapper: target endpoint identity has the identity trace hom. -/
theorem AnalyticMotivesRoot.localizationInput_targetGenerator_id_traceHom
    (input : TraceLocalizationInput) :
    (𝟙 input.targetGenerator :
        input.targetGenerator ⟶ input.targetGenerator).traceHom =
      𝟙 input.targetObject :=
  TraceAnalyticMotive.localizationInput_targetGenerator_id_traceHom
    input

/-- Public wrapper: source endpoint identity induces identity source presheaf map. -/
theorem AnalyticMotivesRoot.localizationInput_sourceGenerator_id_representableMap
    (input : TraceLocalizationInput) :
    (𝟙 input.sourceGenerator :
        input.sourceGenerator ⟶ input.sourceGenerator).representableMap =
      𝟙 input.sourcePresheaf :=
  TraceAnalyticMotive.localizationInput_sourceGenerator_id_representableMap
    input

/-- Public wrapper: target endpoint identity induces identity target presheaf map. -/
theorem AnalyticMotivesRoot.localizationInput_targetGenerator_id_representableMap
    (input : TraceLocalizationInput) :
    (𝟙 input.targetGenerator :
        input.targetGenerator ⟶ input.targetGenerator).representableMap =
      𝟙 input.targetPresheaf :=
  TraceAnalyticMotive.localizationInput_targetGenerator_id_representableMap
    input

/-- Public wrapper: source localized identity is the source trace identity class. -/
theorem AnalyticMotivesRoot.localizationInput_sourceGenerator_localizedIdentity_eq_wordClass
    (input : TraceLocalizationInput) :
    input.sourceGenerator.localizedIdentity =
      TraceLocalizationWordClass.identity input.sourceObject :=
  TraceAnalyticMotive.localizationInput_sourceGenerator_localizedIdentity_eq_wordClass
    input

/-- Public wrapper: target localized identity is the target trace identity class. -/
theorem AnalyticMotivesRoot.localizationInput_targetGenerator_localizedIdentity_eq_wordClass
    (input : TraceLocalizationInput) :
    input.targetGenerator.localizedIdentity =
      TraceLocalizationWordClass.identity input.targetObject :=
  TraceAnalyticMotive.localizationInput_targetGenerator_localizedIdentity_eq_wordClass
    input

/-- Public wrapper: source localized identity is represented by the identity word. -/
theorem AnalyticMotivesRoot.localizationInput_sourceGenerator_localizedIdentity_eq_ofWord
    (input : TraceLocalizationInput) :
    input.sourceGenerator.localizedIdentity =
      TraceLocalizationWordClass.ofWord
        (TraceLocalizationWord.identity input.sourceObject) :=
  TraceAnalyticMotive.localizationInput_sourceGenerator_localizedIdentity_eq_ofWord
    input

/-- Public wrapper: target localized identity is represented by the identity word. -/
theorem AnalyticMotivesRoot.localizationInput_targetGenerator_localizedIdentity_eq_ofWord
    (input : TraceLocalizationInput) :
    input.targetGenerator.localizedIdentity =
      TraceLocalizationWordClass.ofWord
        (TraceLocalizationWord.identity input.targetObject) :=
  TraceAnalyticMotive.localizationInput_targetGenerator_localizedIdentity_eq_ofWord
    input

/-- Public wrapper: source identity representative has no localization atoms. -/
theorem AnalyticMotivesRoot.localizationInput_sourceGenerator_localizedIdentity_representative_atomCount
    (input : TraceLocalizationInput) :
    (TraceLocalizationWord.identity input.sourceObject).atomCount =
      0 :=
  TraceAnalyticMotive.localizationInput_sourceGenerator_localizedIdentity_representative_atomCount
    input

/-- Public wrapper: target identity representative has no localization atoms. -/
theorem AnalyticMotivesRoot.localizationInput_targetGenerator_localizedIdentity_representative_atomCount
    (input : TraceLocalizationInput) :
    (TraceLocalizationWord.identity input.targetObject).atomCount =
      0 :=
  TraceAnalyticMotive.localizationInput_targetGenerator_localizedIdentity_representative_atomCount
    input

end AnalyticMotives
end LFunctions
end Boundary
