import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Generators.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Relations.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Coherence.Owner

/-!
# Relations for Q-linear trace correspondences

This file owns the relations imposed on generated trace correspondences.

The relations should come from analytic rewrite relations and higher
coherences: Stokes cancellation, residue-channel compatibility, refinement
invariance, schedule exchange, weight drop, and Fubini coherence.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
A generator for a relation on Q-linear trace correspondences.

It consists of the higher coherence cell that justifies the relation and the
formal Q-linear trace-correspondence support on which that coherence acts.
-/
abbrev TraceCorQRelationGenerator :=
  TraceCoherenceCell × TraceCorQFormalSum

/-- The higher coherence cell supporting a trace-correspondence relation. -/
def TraceCorQRelationGenerator.cell
    (relation : TraceCorQRelationGenerator) :
    TraceCoherenceCell :=
  relation.1

/-- The formal Q-linear support of a trace-correspondence relation. -/
def TraceCorQRelationGenerator.support
    (relation : TraceCorQRelationGenerator) :
    TraceCorQFormalSum :=
  relation.2

/-- Build a relation generator from a coherence cell and its formal support. -/
def TraceCorQRelationGenerator.ofCellSupport
    (cell : TraceCoherenceCell) (support : TraceCorQFormalSum) :
    TraceCorQRelationGenerator :=
  (cell, support)

end AnalyticMotives
end LFunctions
end Boundary
