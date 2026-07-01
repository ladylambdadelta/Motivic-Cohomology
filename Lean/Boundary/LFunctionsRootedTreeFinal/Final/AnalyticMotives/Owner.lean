import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceExpression.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceTransport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Examples.Owner

/-!
# Analytic motives

This is the fresh analytic-motives lane.

The intended construction is a three-presentation proof:

1. synthetic trace computad: expressions, rewrite rules, paths, coherences,
   and residue-channel presentations;
2. analytic realization: contour integrals, residues, channels, schedules,
   decay, and Fubini theorems interpret the computad;
3. algebraic realization: finite correspondences, Gysin/localization,
   push-pull, base change, projection formula, and trace interpret the same
   computad;
4. Q-linear trace-correspondence and motive construction after the realization
   soundness chains exist.

This root file intentionally contains no fake mathematical declarations.  The
synthetic layer records the computation; the realization layers prove what the
computation means.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

end AnalyticMotives
end LFunctions
end Boundary
