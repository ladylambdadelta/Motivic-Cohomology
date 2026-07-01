import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Owner

/-!
# Trace-transport objects

This file owns the object side of trace transports.

Trace transports compare residue-channel presentations by an analytic
rewriting trace.  They are the bridge from concrete calculus to categorical
morphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Objects for raw trace transport are certified residue-channel presentations. -/
abbrev TraceTransportObject :=
  CertifiedResidueChannelPresentation

end AnalyticMotives
end LFunctions
end Boundary
