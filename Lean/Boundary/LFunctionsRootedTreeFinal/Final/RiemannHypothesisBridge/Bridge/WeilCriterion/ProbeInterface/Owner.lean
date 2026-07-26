import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ProbeInterface.ZetaAdmissibleFunction.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ProbeInterface.ZetaSchwartzFunction.Owner

/-!
# Boundary probe interface

This file owns the ambient probe carrier used by the Weil criterion layer.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The probe carrier used by the hard branch. -/
abbrev ZetaProbe := ZetaAdmissibleFunction

/-- The rapid-decay probe carrier used by prime-tail owners. -/
abbrev ZetaRapidDecayProbe := ZetaSchwartzFunction

end
end LFunctions
end Boundary
