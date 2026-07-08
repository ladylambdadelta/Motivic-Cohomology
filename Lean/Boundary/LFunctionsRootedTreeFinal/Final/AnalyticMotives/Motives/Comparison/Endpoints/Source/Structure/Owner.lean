import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableHomotopyCategory.Owner

/-!
# Endpoint triangulated structure of the comparison source

This file exposes the shift, pretriangulated, triangulated, and distinguished
triangle structures of the stable analytic comparison source at endpoint names.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Endpoint source shift structure. -/
def TraceAnalyticMotiveComparison.sourceHasShiftStructure :
    HasShift TraceAnalyticDMgmComparisonSource ℤ :=
  TraceAnalyticDMgmComparisonSource.hasShiftStructure

/-- Endpoint source shift structure is the source owner shift structure. -/
theorem TraceAnalyticMotiveComparison.sourceHasShiftStructure_eq_source :
    TraceAnalyticMotiveComparison.sourceHasShiftStructure =
      TraceAnalyticDMgmComparisonSource.hasShiftStructure :=
  rfl

/-- Endpoint source shift structure is the stable homotopy comparison shift
structure. -/
theorem TraceAnalyticMotiveComparison.sourceHasShiftStructure_eq_stableHomotopy :
    TraceAnalyticMotiveComparison.sourceHasShiftStructure =
      TraceAnalyticStableHomotopyComparisonSource.hasShiftStructure :=
  rfl

/-- Endpoint source shift structure is the stable analytic shift structure. -/
theorem TraceAnalyticMotiveComparison.sourceHasShiftStructure_eq_stable :
    TraceAnalyticMotiveComparison.sourceHasShiftStructure =
      TraceAnalyticStableMotiveCategory.hasShiftStructure :=
  TraceAnalyticDMgmComparisonSource.hasShiftStructure_eq_stable

/-- Stable-homotopy endpoint source shift structure. -/
def TraceAnalyticMotiveComparison.stableHomotopySourceHasShiftStructure :
    HasShift TraceAnalyticStableHomotopyComparisonSource ℤ :=
  TraceAnalyticStableHomotopyComparisonSource.hasShiftStructure

/-- Stable-homotopy endpoint shift structure is the stable homotopy comparison
shift structure. -/
theorem TraceAnalyticMotiveComparison.stableHomotopySourceHasShiftStructure_eq_stableHomotopy :
    TraceAnalyticMotiveComparison.stableHomotopySourceHasShiftStructure =
      TraceAnalyticStableHomotopyComparisonSource.hasShiftStructure :=
  rfl

/-- Endpoint source pretriangulated structure. -/
def TraceAnalyticMotiveComparison.sourcePretriangulatedStructure :
    Pretriangulated TraceAnalyticDMgmComparisonSource :=
  TraceAnalyticDMgmComparisonSource.pretriangulatedStructure

/-- Endpoint source pretriangulated structure is the source owner structure. -/
theorem TraceAnalyticMotiveComparison.sourcePretriangulatedStructure_eq_source :
    TraceAnalyticMotiveComparison.sourcePretriangulatedStructure =
      TraceAnalyticDMgmComparisonSource.pretriangulatedStructure :=
  rfl

/-- Endpoint source pretriangulated structure is the stable homotopy
comparison pretriangulated structure. -/
theorem TraceAnalyticMotiveComparison.sourcePretriangulatedStructure_eq_stableHomotopy :
    TraceAnalyticMotiveComparison.sourcePretriangulatedStructure =
      TraceAnalyticStableHomotopyComparisonSource.pretriangulatedStructure :=
  rfl

/-- Endpoint source pretriangulated structure is the stable analytic
pretriangulated structure. -/
theorem TraceAnalyticMotiveComparison.sourcePretriangulatedStructure_eq_stable :
    TraceAnalyticMotiveComparison.sourcePretriangulatedStructure =
      TraceAnalyticStableMotiveCategory.pretriangulatedStructure :=
  TraceAnalyticDMgmComparisonSource.pretriangulatedStructure_eq_stable

/-- Stable-homotopy endpoint source pretriangulated structure. -/
def TraceAnalyticMotiveComparison.stableHomotopySourcePretriangulatedStructure :
    Pretriangulated TraceAnalyticStableHomotopyComparisonSource :=
  TraceAnalyticStableHomotopyComparisonSource.pretriangulatedStructure

/-- Stable-homotopy endpoint pretriangulated structure is the stable homotopy
comparison pretriangulated structure. -/
theorem TraceAnalyticMotiveComparison.stableHomotopySourcePretriangulatedStructure_eq_stableHomotopy :
    TraceAnalyticMotiveComparison.stableHomotopySourcePretriangulatedStructure =
      TraceAnalyticStableHomotopyComparisonSource.pretriangulatedStructure :=
  rfl

/-- Endpoint source triangulated structure. -/
def TraceAnalyticMotiveComparison.sourceTriangulatedStructure :
    IsTriangulated TraceAnalyticDMgmComparisonSource :=
  TraceAnalyticDMgmComparisonSource.triangulatedStructure

/-- Endpoint source triangulated structure is the source owner structure. -/
theorem TraceAnalyticMotiveComparison.sourceTriangulatedStructure_eq_source :
    TraceAnalyticMotiveComparison.sourceTriangulatedStructure =
      TraceAnalyticDMgmComparisonSource.triangulatedStructure :=
  rfl

/-- Endpoint source triangulated structure is the stable homotopy comparison
triangulated structure. -/
theorem TraceAnalyticMotiveComparison.sourceTriangulatedStructure_eq_stableHomotopy :
    TraceAnalyticMotiveComparison.sourceTriangulatedStructure =
      TraceAnalyticStableHomotopyComparisonSource.triangulatedStructure :=
  rfl

/-- Endpoint source triangulated structure is the stable analytic triangulated
structure. -/
theorem TraceAnalyticMotiveComparison.sourceTriangulatedStructure_eq_stable :
    TraceAnalyticMotiveComparison.sourceTriangulatedStructure =
      TraceAnalyticStableMotiveCategory.triangulatedStructure :=
  TraceAnalyticDMgmComparisonSource.triangulatedStructure_eq_stable

/-- Stable-homotopy endpoint source triangulated structure. -/
def TraceAnalyticMotiveComparison.stableHomotopySourceTriangulatedStructure :
    IsTriangulated TraceAnalyticStableHomotopyComparisonSource :=
  TraceAnalyticStableHomotopyComparisonSource.triangulatedStructure

/-- Stable-homotopy endpoint triangulated structure is the stable homotopy
comparison triangulated structure. -/
theorem TraceAnalyticMotiveComparison.stableHomotopySourceTriangulatedStructure_eq_stableHomotopy :
    TraceAnalyticMotiveComparison.stableHomotopySourceTriangulatedStructure =
      TraceAnalyticStableHomotopyComparisonSource.triangulatedStructure :=
  rfl

/-- Endpoint source distinguished triangles. -/
def TraceAnalyticMotiveComparison.sourceDistinguishedTriangles :
    Set (Pretriangulated.Triangle TraceAnalyticDMgmComparisonSource) :=
  TraceAnalyticDMgmComparisonSource.distinguishedTriangles

/-- Endpoint source distinguished triangles are the source owner distinguished
triangles. -/
theorem TraceAnalyticMotiveComparison.sourceDistinguishedTriangles_eq_source :
    TraceAnalyticMotiveComparison.sourceDistinguishedTriangles =
      TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  rfl

/-- Endpoint source distinguished triangles are the stable homotopy comparison
distinguished triangles. -/
theorem TraceAnalyticMotiveComparison.sourceDistinguishedTriangles_eq_stableHomotopy :
    TraceAnalyticMotiveComparison.sourceDistinguishedTriangles =
      TraceAnalyticStableHomotopyComparisonSource.distinguishedTriangles :=
  rfl

/-- Endpoint source distinguished triangles are the stable analytic
distinguished triangles. -/
theorem TraceAnalyticMotiveComparison.sourceDistinguishedTriangles_eq_stable' :
    TraceAnalyticMotiveComparison.sourceDistinguishedTriangles =
      TraceAnalyticStableMotiveCategory.distinguishedTriangles :=
  TraceAnalyticDMgmComparisonSource.distinguishedTriangles_eq_stable'

/-- Stable-homotopy endpoint source distinguished triangles. -/
def TraceAnalyticMotiveComparison.stableHomotopySourceDistinguishedTriangles :
    Set (Pretriangulated.Triangle
      TraceAnalyticStableHomotopyComparisonSource) :=
  TraceAnalyticStableHomotopyComparisonSource.distinguishedTriangles

/-- Stable-homotopy endpoint distinguished triangles are the stable homotopy
comparison distinguished triangles. -/
theorem TraceAnalyticMotiveComparison.stableHomotopySourceDistinguishedTriangles_eq_stableHomotopy :
    TraceAnalyticMotiveComparison.stableHomotopySourceDistinguishedTriangles =
      TraceAnalyticStableHomotopyComparisonSource.distinguishedTriangles :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
