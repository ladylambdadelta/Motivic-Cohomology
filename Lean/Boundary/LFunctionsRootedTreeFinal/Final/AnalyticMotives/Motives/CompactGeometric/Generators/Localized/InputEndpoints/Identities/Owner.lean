import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Category.Owner

/-!
# Identity morphisms at localization-input endpoints

This file specializes compact-generator identity facts to the source and target
generators attached to a concrete localization input.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The identity on the source endpoint has the identity trace hom. -/
theorem TraceLocalizationInput.sourceGenerator_id_traceHom
    (input : TraceLocalizationInput) :
    (𝟙 input.sourceGenerator :
        input.sourceGenerator ⟶ input.sourceGenerator).traceHom =
      𝟙 input.sourceObject :=
  TraceAnalyticGeometricGenerator.id_traceHom
    input.sourceGenerator

/-- The identity on the target endpoint has the identity trace hom. -/
theorem TraceLocalizationInput.targetGenerator_id_traceHom
    (input : TraceLocalizationInput) :
    (𝟙 input.targetGenerator :
        input.targetGenerator ⟶ input.targetGenerator).traceHom =
      𝟙 input.targetObject :=
  TraceAnalyticGeometricGenerator.id_traceHom
    input.targetGenerator

/-- The identity on the source endpoint induces the identity source presheaf map. -/
theorem TraceLocalizationInput.sourceGenerator_id_representableMap
    (input : TraceLocalizationInput) :
    (𝟙 input.sourceGenerator :
        input.sourceGenerator ⟶ input.sourceGenerator).representableMap =
      𝟙 input.sourcePresheaf :=
  TraceAnalyticGeometricGenerator.id_representableMap
    input.sourceGenerator

/-- The identity on the target endpoint induces the identity target presheaf map. -/
theorem TraceLocalizationInput.targetGenerator_id_representableMap
    (input : TraceLocalizationInput) :
    (𝟙 input.targetGenerator :
        input.targetGenerator ⟶ input.targetGenerator).representableMap =
      𝟙 input.targetPresheaf :=
  TraceAnalyticGeometricGenerator.id_representableMap
    input.targetGenerator

/-- The identity localized word on the source endpoint is the source trace identity class. -/
theorem TraceLocalizationInput.sourceGenerator_localizedIdentity_eq_wordClass
    (input : TraceLocalizationInput) :
    input.sourceGenerator.localizedIdentity =
      TraceLocalizationWordClass.identity input.sourceObject :=
  TraceAnalyticGeometricGenerator.localizedIdentity_eq_wordClass
    input.sourceGenerator

/-- The identity localized word on the target endpoint is the target trace identity class. -/
theorem TraceLocalizationInput.targetGenerator_localizedIdentity_eq_wordClass
    (input : TraceLocalizationInput) :
    input.targetGenerator.localizedIdentity =
      TraceLocalizationWordClass.identity input.targetObject :=
  TraceAnalyticGeometricGenerator.localizedIdentity_eq_wordClass
    input.targetGenerator

/-- The source endpoint identity is represented by the identity localization word. -/
theorem TraceLocalizationInput.sourceGenerator_localizedIdentity_eq_ofWord
    (input : TraceLocalizationInput) :
    input.sourceGenerator.localizedIdentity =
      TraceLocalizationWordClass.ofWord
        (TraceLocalizationWord.identity input.sourceObject) :=
  TraceAnalyticGeometricGenerator.localizedIdentity_eq_ofWord
    input.sourceGenerator

/-- The target endpoint identity is represented by the identity localization word. -/
theorem TraceLocalizationInput.targetGenerator_localizedIdentity_eq_ofWord
    (input : TraceLocalizationInput) :
    input.targetGenerator.localizedIdentity =
      TraceLocalizationWordClass.ofWord
        (TraceLocalizationWord.identity input.targetObject) :=
  TraceAnalyticGeometricGenerator.localizedIdentity_eq_ofWord
    input.targetGenerator

/-- The source endpoint identity representative has no localization atoms. -/
theorem TraceLocalizationInput.sourceGenerator_localizedIdentity_representative_atomCount
    (input : TraceLocalizationInput) :
    (TraceLocalizationWord.identity input.sourceObject).atomCount =
      0 :=
  TraceAnalyticGeometricGenerator.localizedIdentity_representative_atomCount
    input.sourceGenerator

/-- The target endpoint identity representative has no localization atoms. -/
theorem TraceLocalizationInput.targetGenerator_localizedIdentity_representative_atomCount
    (input : TraceLocalizationInput) :
    (TraceLocalizationWord.identity input.targetObject).atomCount =
      0 :=
  TraceAnalyticGeometricGenerator.localizedIdentity_representative_atomCount
    input.targetGenerator

end AnalyticMotives
end LFunctions
end Boundary
