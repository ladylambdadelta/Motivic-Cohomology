import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceTransport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Objects.Owner

/-!
# Q-linear trace-correspondence generators

This file owns the morphism generators for trace correspondences over `Q`.

Generators are certified trace transports between residue-channel
presentations.  The analytic content is carried by the rewrite trace and its
certificates.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A generator for Q-linear trace correspondences is a raw trace transport. -/
abbrev TraceCorQGenerator :=
  TraceTransport

end AnalyticMotives
end LFunctions
end Boundary
