import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.Owner

/-!
# Triangulated additive analytic homotopy category

Mathlib's homotopy category of cochain complexes is triangulated when the base
category is preadditive with a zero object and binary biproducts.  Those
requirements are supplied here by the concrete analytic additive envelope.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

/-- Distinguished triangles in the additive analytic homotopy category. -/
def TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :
    Set (Triangle TraceAnalyticAdditiveHomotopyCategory) :=
  distTriang TraceAnalyticAdditiveHomotopyCategory

/-- The additive analytic homotopy category carries Mathlib's pretriangulated structure. -/
def TraceAnalyticAdditiveHomotopyCategory.pretriangulatedStructure :
    Pretriangulated TraceAnalyticAdditiveHomotopyCategory :=
  inferInstance

/-- The additive analytic homotopy category carries Mathlib's triangulated structure. -/
def TraceAnalyticAdditiveHomotopyCategory.triangulatedStructure :
    IsTriangulated TraceAnalyticAdditiveHomotopyCategory :=
  inferInstance

/-- Mapping-cone triangles are distinguished in the additive analytic homotopy category. -/
theorem TraceAnalyticAdditiveHomotopyCategory.mappingCone_triangle_distinguished
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target) :
    CochainComplex.mappingCone.triangleh hom ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  HomotopyCategory.mappingCone_triangleh_distinguished hom

end AnalyticMotives
end LFunctions
end Boundary
