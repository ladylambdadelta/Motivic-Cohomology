import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceTransport.Objects.Owner

/-!
# Q-linear trace-category objects

This file owns the objects of the pre-motivic Q-linear trace category.

The intended objects are certified residue-channel trace presentations.  This
keeps the lane on the higher-computadic trace calculus rather than a separate
geometric-object category.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Objects of the raw Q-linear trace category. -/
abbrev TraceCorQObject :=
  TraceTransportObject

end AnalyticMotives
end LFunctions
end Boundary
