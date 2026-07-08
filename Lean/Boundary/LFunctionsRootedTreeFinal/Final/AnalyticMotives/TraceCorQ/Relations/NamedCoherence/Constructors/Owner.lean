import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Relations.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Coherence.Certificates.Owner

/-!
# Named coherence relation-generator constructors

This file owns the concrete Q-linear trace-correspondence relation generators
coming from the named higher coherence cells of the trace computad.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A relation generator certified by a Fubini coherence cell. -/
def TraceCorQRelationGenerator.fubini
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQRelationGenerator :=
  TraceCorQRelationGenerator.ofCellSupport
    (TraceCoherenceCell.fubini source target)
    support

/-- A relation generator certified by a schedule-exchange coherence cell. -/
def TraceCorQRelationGenerator.scheduleExchange
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQRelationGenerator :=
  TraceCorQRelationGenerator.ofCellSupport
    (TraceCoherenceCell.scheduleExchange source target)
    support

/-- A relation generator certified by a residue-channel coherence cell. -/
def TraceCorQRelationGenerator.residueChannel
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQRelationGenerator :=
  TraceCorQRelationGenerator.ofCellSupport
    (TraceCoherenceCell.residueChannel source target)
    support

/-- A relation generator certified by a Stokes-residue coherence cell. -/
def TraceCorQRelationGenerator.stokesResidue
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQRelationGenerator :=
  TraceCorQRelationGenerator.ofCellSupport
    (TraceCoherenceCell.stokesResidue source target)
    support

/-- A relation generator certified by a refinement coherence cell. -/
def TraceCorQRelationGenerator.refinement
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQRelationGenerator :=
  TraceCorQRelationGenerator.ofCellSupport
    (TraceCoherenceCell.refinement source target)
    support

/-- A relation generator certified by an associativity coherence cell. -/
def TraceCorQRelationGenerator.associativity
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQRelationGenerator :=
  TraceCorQRelationGenerator.ofCellSupport
    (TraceCoherenceCell.associativity source target)
    support

/-- A relation generator certified by a left-identity coherence cell. -/
def TraceCorQRelationGenerator.leftIdentity
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQRelationGenerator :=
  TraceCorQRelationGenerator.ofCellSupport
    (TraceCoherenceCell.leftIdentity source target)
    support

/-- A relation generator certified by a right-identity coherence cell. -/
def TraceCorQRelationGenerator.rightIdentity
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQRelationGenerator :=
  TraceCorQRelationGenerator.ofCellSupport
    (TraceCoherenceCell.rightIdentity source target)
    support

end AnalyticMotives
end LFunctions
end Boundary
