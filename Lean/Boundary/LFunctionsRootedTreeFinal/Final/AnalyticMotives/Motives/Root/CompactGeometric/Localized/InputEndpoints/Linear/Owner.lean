import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.Linear.Owner

/-!
# Motive-root linear interpretation of localized input endpoints

This file exposes the rational-linear trace interpretation of localization
input compact-generator morphisms through the motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root wrapper: zero over a localization input is zero on trace homs. -/
theorem TraceAnalyticMotive.localizationInput_generatorHom_zero_traceHom
    (input : TraceLocalizationInput) :
    (0 : input.sourceGenerator ⟶ input.targetGenerator).traceHom =
      (0 : input.sourceObject ⟶ input.targetObject) :=
  TraceLocalizationInput.generatorHom_zero_traceHom
    input

/-- Motive-root wrapper: scalar multiplication of an input interpretation is trace scalar multiplication. -/
theorem TraceAnalyticMotive.localizationInput_generatorHom_smul_traceHom
    (input : TraceLocalizationInput)
    (coefficient : Rat) :
    (coefficient • input.generatorHom).traceHom =
      coefficient • input.traceHom :=
  TraceLocalizationInput.generatorHom_smul_traceHom
    input
    coefficient

/-- Motive-root wrapper: negation of an input interpretation is trace-hom negation. -/
theorem TraceAnalyticMotive.localizationInput_generatorHom_traceNeg_traceHom
    (input : TraceLocalizationInput) :
    (TraceCorQHom.neg input.generatorHom).traceHom =
      TraceCorQHom.neg input.traceHom :=
  TraceLocalizationInput.generatorHom_traceNeg_traceHom
    input

/-- Motive-root wrapper: self-subtraction of an input interpretation gives zero. -/
theorem TraceAnalyticMotive.localizationInput_generatorHom_traceSub_self
    (input : TraceLocalizationInput) :
    TraceCorQHom.sub input.generatorHom input.generatorHom =
      TraceCorQHom.zero input.sourceObject input.targetObject :=
  TraceLocalizationInput.generatorHom_traceSub_self
    input

/-- Motive-root wrapper: scalar multiplication distributes over input self-subtraction. -/
theorem TraceAnalyticMotive.localizationInput_generatorHom_traceSmul_sub_self
    (input : TraceLocalizationInput)
    (coefficient : Rat) :
    TraceCorQHom.smul
      coefficient
      (TraceCorQHom.sub input.generatorHom input.generatorHom) =
      TraceCorQHom.sub
        (TraceCorQHom.smul coefficient input.generatorHom)
        (TraceCorQHom.smul coefficient input.generatorHom) :=
  TraceLocalizationInput.generatorHom_traceSmul_sub_self
    input
    coefficient

end AnalyticMotives
end LFunctions
end Boundary
