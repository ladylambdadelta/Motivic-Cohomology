import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Stabilization.BoundedCones.Owner

/-!
# Motive-root stabilization facade

This file exposes the stable additive-envelope homotopy category and its
Mathlib-backed triangulated structure at the motive-root layer.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Motive-root facade: the additive analytic homotopy category has a pretriangulated
structure. -/
def TraceAnalyticMotive.rootStabilization_pretriangulatedStructure :
    Pretriangulated TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticAdditiveHomotopyCategory.pretriangulatedStructure

/-- Motive-root facade: the additive analytic homotopy category is triangulated. -/
def TraceAnalyticMotive.rootStabilization_triangulatedStructure :
    IsTriangulated TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticAdditiveHomotopyCategory.triangulatedStructure

/-- Motive-root facade: the localized stable analytic motive category has shifts. -/
def TraceAnalyticMotive.rootStableMotive_hasShiftStructure :
    HasShift TraceAnalyticStableMotiveCategory ℤ :=
  TraceAnalyticStableMotiveCategory.hasShiftStructure

/-- Motive-root facade: the localized stable analytic motive category is pretriangulated. -/
def TraceAnalyticMotive.rootStableMotive_pretriangulatedStructure :
    Pretriangulated TraceAnalyticStableMotiveCategory :=
  TraceAnalyticStableMotiveCategory.pretriangulatedStructure

/-- Motive-root facade: the localized stable analytic motive category is triangulated. -/
def TraceAnalyticMotive.rootStableMotive_triangulatedStructure :
    IsTriangulated TraceAnalyticStableMotiveCategory :=
  TraceAnalyticStableMotiveCategory.triangulatedStructure

/-- Motive-root facade: distinguished triangles are Mathlib's distinguished triangles. -/
theorem TraceAnalyticMotive.rootStabilization_distinguishedTriangles_eq :
    TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles =
      Pretriangulated.distTriang TraceAnalyticAdditiveHomotopyCategory :=
  rfl

/-- Motive-root facade: stable distinguished triangles are Mathlib's distinguished
triangles on the localized stable category. -/
theorem TraceAnalyticMotive.rootStableMotive_distinguishedTriangles_eq :
    TraceAnalyticStableMotiveCategory.distinguishedTriangles =
      Pretriangulated.distTriang TraceAnalyticStableMotiveCategory :=
  TraceAnalyticStableMotiveCategory.distinguishedTriangles_eq

/-- Motive-root facade: additive analytic mapping-cone triangles are distinguished. -/
theorem TraceAnalyticMotive.rootStabilization_mappingCone_triangle_distinguished
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target) :
    CochainComplex.mappingCone.triangleh hom ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceAnalyticAdditiveHomotopyCategory.mappingCone_triangle_distinguished
    hom

end AnalyticMotives
end LFunctions
end Boundary
