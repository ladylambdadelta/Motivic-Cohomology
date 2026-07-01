import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.Owner

/-!
# Cancellation laws for localized input arrows

This file records the cancellation laws for the named forward and inverse
arrows attached to each localization input.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A localization input's forward arrow followed by its inverse is identity. -/
theorem TraceLocalizationInput.localizedForward_comp_inverse
    (input : TraceLocalizationInput) :
    TraceLocalizationWordClass.comp
        input.localizedForwardArrow
        input.localizedInverseArrow =
      TraceLocalizationWordClass.identity input.sourceObject :=
  TraceLocalizationWordClass.comp_forward_inverse_eq_identity input

/-- A localization input's inverse arrow followed by its forward arrow is identity. -/
theorem TraceLocalizationInput.localizedInverse_comp_forward
    (input : TraceLocalizationInput) :
    TraceLocalizationWordClass.comp
        input.localizedInverseArrow
        input.localizedForwardArrow =
      TraceLocalizationWordClass.identity input.targetObject :=
  TraceLocalizationWordClass.comp_inverse_forward_eq_identity input

/-- The named localized isomorphism hom-inverse law is the forward-inverse cancellation law. -/
theorem TraceLocalizationInput.localizedIso_hom_inv_eq_forward_comp_inverse
    (input : TraceLocalizationInput) :
    TraceLocalizationWordClass.comp
        (TraceLocalizationInput.localizedIso input).hom
        (TraceLocalizationInput.localizedIso input).inv =
      TraceLocalizationWordClass.comp
        input.localizedForwardArrow
        input.localizedInverseArrow :=
  rfl

/-- The named localized isomorphism inverse-hom law is the inverse-forward cancellation law. -/
theorem TraceLocalizationInput.localizedIso_inv_hom_eq_inverse_comp_forward
    (input : TraceLocalizationInput) :
    TraceLocalizationWordClass.comp
        (TraceLocalizationInput.localizedIso input).inv
        (TraceLocalizationInput.localizedIso input).hom =
      TraceLocalizationWordClass.comp
        input.localizedInverseArrow
        input.localizedForwardArrow :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
