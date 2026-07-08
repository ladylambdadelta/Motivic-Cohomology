import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Linear.Owner

/-!
# Linear interpretation of localized input endpoints

This file records the rational-linear trace interpretation of the
compact-generator morphism attached to a localization input.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The zero compact interpretation over a localization input is the zero trace hom. -/
theorem TraceLocalizationInput.generatorHom_zero_traceHom
    (input : TraceLocalizationInput) :
    (0 : input.sourceGenerator ⟶ input.targetGenerator).traceHom =
      (0 : input.sourceObject ⟶ input.targetObject) :=
  TraceAnalyticGeometricGenerator.zero_traceHom

/-- Scalar multiplication of an input's compact interpretation is scalar trace multiplication. -/
theorem TraceLocalizationInput.generatorHom_smul_traceHom
    (input : TraceLocalizationInput)
    (coefficient : Rat) :
    (coefficient • input.generatorHom).traceHom =
      coefficient • input.traceHom :=
  Eq.trans
    (TraceAnalyticGeometricGenerator.smul_traceHom
      coefficient
      input.generatorHom)
    (congrArg
      (fun traceHom =>
        coefficient • traceHom)
      (TraceLocalizationInput.generatorHom_traceHom input))

/-- Negation of an input's compact interpretation is trace-hom negation. -/
theorem TraceLocalizationInput.generatorHom_traceNeg_traceHom
    (input : TraceLocalizationInput) :
    (TraceCorQHom.neg input.generatorHom).traceHom =
      TraceCorQHom.neg input.traceHom :=
  Eq.trans
    (TraceAnalyticGeometricGenerator.traceNeg_traceHom
      input.generatorHom)
    (congrArg
      TraceCorQHom.neg
      (TraceLocalizationInput.generatorHom_traceHom input))

/-- Subtracting an input's compact interpretation from itself gives zero. -/
theorem TraceLocalizationInput.generatorHom_traceSub_self
    (input : TraceLocalizationInput) :
    TraceCorQHom.sub input.generatorHom input.generatorHom =
      TraceCorQHom.zero input.sourceObject input.targetObject :=
  TraceAnalyticGeometricGenerator.traceSub_self_traceHom
    input.generatorHom

/-- Scalar multiplication distributes over self-subtraction of an input interpretation. -/
theorem TraceLocalizationInput.generatorHom_traceSmul_sub_self
    (input : TraceLocalizationInput)
    (coefficient : Rat) :
    TraceCorQHom.smul
      coefficient
      (TraceCorQHom.sub input.generatorHom input.generatorHom) =
      TraceCorQHom.sub
        (TraceCorQHom.smul coefficient input.generatorHom)
        (TraceCorQHom.smul coefficient input.generatorHom) :=
  TraceAnalyticGeometricGenerator.traceSmul_sub
    coefficient
    input.generatorHom
    input.generatorHom

end AnalyticMotives
end LFunctions
end Boundary
