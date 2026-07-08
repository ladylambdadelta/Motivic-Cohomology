import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Complexes.LocalizationInput.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Monotone.Complexes.Owner

/-!
# Common bounds for localization-input source and target complexes

This file places the bounded source and target complexes of a localization
input under one shared numeric bound.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The common bound for the source and target complexes of a localization input. -/
def TraceLocalizationInput.additiveComplexCommonWeightBound
    (input : TraceLocalizationInput) :
    Nat :=
  Nat.max
    input.additiveSourceObjectWeightBound
    input.additiveTargetObjectWeightBound

/-- The source bound of a localization input is below its common complex bound. -/
theorem TraceLocalizationInput.additiveSourceObjectWeightBound_le_common
    (input : TraceLocalizationInput) :
    input.additiveSourceObjectWeightBound ≤
      input.additiveComplexCommonWeightBound :=
  Nat.le_max_left
    input.additiveSourceObjectWeightBound
    input.additiveTargetObjectWeightBound

/-- The target bound of a localization input is below its common complex bound. -/
theorem TraceLocalizationInput.additiveTargetObjectWeightBound_le_common
    (input : TraceLocalizationInput) :
    input.additiveTargetObjectWeightBound ≤
      input.additiveComplexCommonWeightBound :=
  Nat.le_max_right
    input.additiveSourceObjectWeightBound
    input.additiveTargetObjectWeightBound

/-- The source complex of a localization input, regarded under the common bound. -/
def TraceLocalizationInput.commonBoundedAdditiveSourceComplex
    (input : TraceLocalizationInput) :
    TraceAnalyticAdditiveCochainComplex.WeightBoundedBy
      input.additiveComplexCommonWeightBound :=
  input.boundedAdditiveSourceComplex.rebound
    input.additiveSourceObjectWeightBound_le_common

/-- The target complex of a localization input, regarded under the common bound. -/
def TraceLocalizationInput.commonBoundedAdditiveTargetComplex
    (input : TraceLocalizationInput) :
    TraceAnalyticAdditiveCochainComplex.WeightBoundedBy
      input.additiveComplexCommonWeightBound :=
  input.boundedAdditiveTargetComplex.rebound
    input.additiveTargetObjectWeightBound_le_common

/-- Rebounding the source complex to the common bound preserves the underlying complex. -/
theorem TraceLocalizationInput.commonBoundedAdditiveSourceComplex_complex
    (input : TraceLocalizationInput) :
    input.commonBoundedAdditiveSourceComplex.complex =
      input.additiveSourceComplex :=
  rfl

/-- Rebounding the target complex to the common bound preserves the underlying complex. -/
theorem TraceLocalizationInput.commonBoundedAdditiveTargetComplex_complex
    (input : TraceLocalizationInput) :
    input.commonBoundedAdditiveTargetComplex.complex =
      input.additiveTargetComplex :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
