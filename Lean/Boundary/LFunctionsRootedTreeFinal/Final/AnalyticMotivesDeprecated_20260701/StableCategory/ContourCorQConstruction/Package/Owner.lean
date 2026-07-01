import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.StableCategory.ContourCorQConstruction.Compact.Owner

/-!
# Constructed stable analytic motive package

This owner assembles the constructed effective, stabilized, and compact layers
without introducing an abstract stable-infinity target interface.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The constructed stable analytic motive package. -/
structure ConstructedStableAnalyticMotivePackage where
  effectiveLayer : ConstructedEffectiveAnalyticMotive
  stabilizedLayer : ConstructedStabilizedAnalyticMotive
  compactLayer : ConstructedCompactAnalyticMotive
  stabilized_effective_eq :
    stabilizedLayer.effective = effectiveLayer
  compact_stabilized_eq :
    compactLayer.stabilized = stabilizedLayer

namespace ConstructedStableAnalyticMotivePackage

/-- The effective layer of the constructed stable package. -/
def effective (P : ConstructedStableAnalyticMotivePackage) :
    ConstructedEffectiveAnalyticMotive :=
  P.effectiveLayer

/-- The stabilized layer of the constructed stable package. -/
def stabilized (P : ConstructedStableAnalyticMotivePackage) :
    ConstructedStabilizedAnalyticMotive :=
  P.stabilizedLayer

/-- The compact layer of the constructed stable package. -/
def compact (P : ConstructedStableAnalyticMotivePackage) :
    ConstructedCompactAnalyticMotive :=
  P.compactLayer

/-- The constructed Tate-stabilized presheaf of the package. -/
def stabilizedPresheaf (P : ConstructedStableAnalyticMotivePackage) :
    ConstructedTateStabilizedAnalyticPresheaf :=
  P.stabilizedLayer.stabilizedPresheaf

/-- The constructed compact-geometric motive of the package. -/
def compactGeometric (P : ConstructedStableAnalyticMotivePackage) :
    ConstructedCompactGeometricAnalyticMotive :=
  P.compactLayer.compactGeometric

/-- The stabilized layer has the package effective layer. -/
theorem stabilized_effective_compatibility
    (P : ConstructedStableAnalyticMotivePackage) :
    P.stabilizedLayer.effective = P.effectiveLayer :=
  P.stabilized_effective_eq

/-- The compact layer has the package stabilized layer. -/
theorem compact_stabilized_compatibility
    (P : ConstructedStableAnalyticMotivePackage) :
    P.compactLayer.stabilized = P.stabilizedLayer :=
  P.compact_stabilized_eq

end ConstructedStableAnalyticMotivePackage

end AnalyticMotives
end LFunctions
end Boundary
