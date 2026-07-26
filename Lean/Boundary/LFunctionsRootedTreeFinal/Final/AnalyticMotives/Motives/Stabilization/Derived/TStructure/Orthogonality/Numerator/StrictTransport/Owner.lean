import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Orthogonality.Numerator.StrictSupport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Orthogonality.Fractions.Owner

/-!
# Strict-transport reduction for numerator orthogonality

This file owns the reduction from a transported strict-support representative
to vanishing of the localized numerator.
-/

noncomputable section

open CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDerivedMotiveCategory

/-- The localized image of a strict lower-to-upper map is zero. -/
theorem localization_map_eq_zero_of_truncLE_zero_to_truncGE_one
    (sourceReplacement targetReplacement :
      TraceAnalyticAbelianCochainComplex)
    [sourceReplacement.IsStrictlySupported
      (TraceAnalyticMotivicTStructure.truncLEEmbedding 0)]
    [targetReplacement.IsStrictlySupported
      (TraceAnalyticMotivicTStructure.truncGEEmbedding 1)]
    (strictHom : sourceReplacement ⟶ targetReplacement) :
    TraceAnalyticDerivedMotiveCategory.localizationFunctor.map strictHom =
      0 :=
  Eq.trans
    (congrArg
      (fun hom =>
        TraceAnalyticDerivedMotiveCategory.localizationFunctor.map hom)
      (TraceAnalyticDerivedMotiveCategory
        .truncLE_zero_to_truncGE_one_hom_eq_zero
          sourceReplacement
          targetReplacement
          strictHom))
    (TraceAnalyticDerivedMotiveCategory.localizationFunctor.map_zero
      sourceReplacement
      targetReplacement)

/-- A transported strict-support representative makes the localized numerator
zero. -/
theorem leftFraction_numerator_maps_to_zero_of_strict_transport
    (sourceComplex targetComplex : TraceAnalyticAbelianCochainComplex)
    (fraction :
      TraceAnalyticDerivedMotiveCategory
        .DerivedLeftFraction sourceComplex targetComplex)
    (sourceReplacement targetReplacement :
      TraceAnalyticAbelianCochainComplex)
    [sourceReplacement.IsStrictlySupported
      (TraceAnalyticMotivicTStructure.truncLEEmbedding 0)]
    [targetReplacement.IsStrictlySupported
      (TraceAnalyticMotivicTStructure.truncGEEmbedding 1)]
    (sourceIso :
      TraceAnalyticDerivedMotiveCategory.objectOf sourceComplex ≅
        TraceAnalyticDerivedMotiveCategory.objectOf sourceReplacement)
    (targetIso :
      TraceAnalyticDerivedMotiveCategory.objectOf targetReplacement ≅
        TraceAnalyticDerivedMotiveCategory.objectOf fraction.Y')
    (strictHom : sourceReplacement ⟶ targetReplacement)
    (transport :
      TraceAnalyticDerivedMotiveCategory.localizationFunctor.map
          fraction.f =
        sourceIso.hom ≫
          TraceAnalyticDerivedMotiveCategory.localizationFunctor.map
            strictHom ≫
          targetIso.hom) :
    TraceAnalyticDerivedMotiveCategory.localizationFunctor.map
        fraction.f =
      0 :=
  let strictMapZero :
      TraceAnalyticDerivedMotiveCategory.localizationFunctor.map strictHom =
        0 :=
    TraceAnalyticDerivedMotiveCategory
      .localization_map_eq_zero_of_truncLE_zero_to_truncGE_one
        sourceReplacement
        targetReplacement
        strictHom
  let transportedZero :
      sourceIso.hom ≫
          TraceAnalyticDerivedMotiveCategory.localizationFunctor.map
            strictHom ≫
        targetIso.hom =
      0 :=
    Eq.trans
      (congrArg
        (fun strictMap =>
          sourceIso.hom ≫ strictMap ≫ targetIso.hom)
        strictMapZero)
      (Eq.trans
        (congrArg
          (fun leftMap => leftMap ≫ targetIso.hom)
          (comp_zero sourceIso.hom))
        (zero_comp targetIso.hom))
  Eq.trans transport transportedZero

end TraceAnalyticDerivedMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary
