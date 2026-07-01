import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Adapters.RHContour.Objects.ToContourAdmissibleBulk.Owner

/-!
# RH contour object adapter

This file is the adapter surface for the completed-zeta explicit-formula
contour geometry imported from the RH lane.  It records what is already
available as concrete RH contour data and keeps that data separate from the
general analytic-motive object universe.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The RH contour adapter object already constructed from imported RH data. -/
abbrev RHContourAdapterObject :=
  RHContourAdmissibleBulk

namespace RHContourAdapterObject

/-- The packet carried by an RH contour adapter object. -/
def packet (X : RHContourAdapterObject) :
    ZetaAdmissibleFunction :=
  RHContourAdmissibleBulk.packet X

/-- The rectangle boundary at an RH contour height. -/
def boundaryAt (X : RHContourAdapterObject) (T : X.Stage) : Set ℂ :=
  RHContourAdmissibleBulk.boundary X T

/-- The singular support at an RH contour height. -/
def singularSupportAt (X : RHContourAdapterObject) (T : X.Stage) : Set ℂ :=
  RHContourAdmissibleBulk.singularSupport X T

end RHContourAdapterObject

end AnalyticMotives
end LFunctions
end Boundary
