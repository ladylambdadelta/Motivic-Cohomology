import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.Contractible.IdentityCone.IsIso.Maps.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.ConeObject.Owner

/-!
# Identity-cone maps for the normalized cone-comparison cone object

This file specializes the general isomorphism-cone-to-identity-cone maps to
the normalized cone-to-upper cochain map.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- The map from the concrete mapping cone of the normalized cone-to-upper
cochain map to the identity cone on the upper truncation, assuming the
cone-to-upper map is an isomorphism. -/
def additiveNormalizedConeComparisonMappingConeToIdentityConeMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    CochainComplex.mappingCone
        (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
          cut
          complex) ⟶
      CochainComplex.mappingCone
        (𝟙 (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex)) :=
  TraceAnalyticAdditiveHomotopyCategory.mappingConeIsoToIdentityConeMap
    (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
      cut
      complex)

/-- The map from the identity cone on the upper truncation back to the concrete
mapping cone of the normalized cone-to-upper cochain map, assuming the
cone-to-upper map is an isomorphism. -/
def additiveNormalizedIdentityConeToConeComparisonMappingConeMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    CochainComplex.mappingCone
        (𝟙 (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex)) ⟶
      CochainComplex.mappingCone
        (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
          cut
          complex) :=
  TraceAnalyticAdditiveHomotopyCategory.identityConeToMappingConeIsoMap
    (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
      cut
      complex)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
