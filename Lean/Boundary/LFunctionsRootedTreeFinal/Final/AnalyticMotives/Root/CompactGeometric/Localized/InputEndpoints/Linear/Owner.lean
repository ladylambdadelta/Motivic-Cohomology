import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Localized.InputEndpoints.Linear.Owner

/-!
# Public linear interpretation of localized input endpoints

This file exposes the rational-linear trace interpretation of localization
input compact-generator morphisms through the public root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: zero over a localization input is zero on trace homs. -/
theorem AnalyticMotivesRoot.localizationInput_generatorHom_zero_traceHom
    (input : TraceLocalizationInput) :
    (0 : input.sourceGenerator ⟶ input.targetGenerator).traceHom =
      (0 : input.sourceObject ⟶ input.targetObject) :=
  TraceAnalyticMotive.localizationInput_generatorHom_zero_traceHom
    input

/-- Public wrapper: scalar multiplication of an input interpretation is trace scalar multiplication. -/
theorem AnalyticMotivesRoot.localizationInput_generatorHom_smul_traceHom
    (input : TraceLocalizationInput)
    (coefficient : Rat) :
    (coefficient • input.generatorHom).traceHom =
      coefficient • input.traceHom :=
  TraceAnalyticMotive.localizationInput_generatorHom_smul_traceHom
    input
    coefficient

/-- Public wrapper: negation of an input interpretation is trace-hom negation. -/
theorem AnalyticMotivesRoot.localizationInput_generatorHom_traceNeg_traceHom
    (input : TraceLocalizationInput) :
    (TraceCorQHom.neg input.generatorHom).traceHom =
      TraceCorQHom.neg input.traceHom :=
  TraceAnalyticMotive.localizationInput_generatorHom_traceNeg_traceHom
    input

/-- Public wrapper: self-subtraction of an input interpretation gives zero. -/
theorem AnalyticMotivesRoot.localizationInput_generatorHom_traceSub_self
    (input : TraceLocalizationInput) :
    TraceCorQHom.sub input.generatorHom input.generatorHom =
      TraceCorQHom.zero input.sourceObject input.targetObject :=
  TraceAnalyticMotive.localizationInput_generatorHom_traceSub_self
    input

/-- Public wrapper: scalar multiplication distributes over input self-subtraction. -/
theorem AnalyticMotivesRoot.localizationInput_generatorHom_traceSmul_sub_self
    (input : TraceLocalizationInput)
    (coefficient : Rat) :
    TraceCorQHom.smul
      coefficient
      (TraceCorQHom.sub input.generatorHom input.generatorHom) =
      TraceCorQHom.sub
        (TraceCorQHom.smul coefficient input.generatorHom)
        (TraceCorQHom.smul coefficient input.generatorHom) :=
  TraceAnalyticMotive.localizationInput_generatorHom_traceSmul_sub_self
    input
    coefficient

end AnalyticMotives
end LFunctions
end Boundary
