import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Paths.Owner

/-!
# Higher rewrite coherence

This file owns higher coherence data: commuting squares and higher cells between
different rewrite paths.  Analytically, these coherences are proved by Fubini,
change of variables, compatibility of residue ledgers, and stability of channel
decompositions under refinement.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The concrete kind of a higher coherence cell between rewrite paths. -/
inductive TraceCoherenceKind where
  | associativity
  | leftIdentity
  | rightIdentity
  | fubini
  | scheduleExchange
  | stokesResidue
  | residueChannel
  | refinement
  deriving DecidableEq, Repr

/--
A raw higher coherence cell in the trace computad.

The source and target are rewrite paths.  Later certificate files prove the
analytic soundness of each named cell.
-/
abbrev TraceCoherenceCell :=
  TraceCoherenceKind × TraceRewritePath × TraceRewritePath

/-- The kind of a higher coherence cell. -/
def TraceCoherenceCell.kind (cell : TraceCoherenceCell) :
    TraceCoherenceKind :=
  cell.1

/-- The source rewrite path of a higher coherence cell. -/
def TraceCoherenceCell.source (cell : TraceCoherenceCell) :
    TraceRewritePath :=
  cell.2.1

/-- The target rewrite path of a higher coherence cell. -/
def TraceCoherenceCell.target (cell : TraceCoherenceCell) :
    TraceRewritePath :=
  cell.2.2

/-- A Fubini coherence cell between two rewrite schedules. -/
def TraceCoherenceCell.fubini
    (source target : TraceRewritePath) : TraceCoherenceCell :=
  (TraceCoherenceKind.fubini, source, target)

/-- A schedule-exchange coherence cell. -/
def TraceCoherenceCell.scheduleExchange
    (source target : TraceRewritePath) : TraceCoherenceCell :=
  (TraceCoherenceKind.scheduleExchange, source, target)

/-- A residue-channel compatibility coherence cell. -/
def TraceCoherenceCell.residueChannel
    (source target : TraceRewritePath) : TraceCoherenceCell :=
  (TraceCoherenceKind.residueChannel, source, target)

/-- An associativity coherence cell between two parenthesizations of a rewrite path. -/
def TraceCoherenceCell.associativity
    (source target : TraceRewritePath) : TraceCoherenceCell :=
  (TraceCoherenceKind.associativity, source, target)

/-- A left-identity coherence cell between two rewrite paths. -/
def TraceCoherenceCell.leftIdentity
    (source target : TraceRewritePath) : TraceCoherenceCell :=
  (TraceCoherenceKind.leftIdentity, source, target)

/-- A right-identity coherence cell between two rewrite paths. -/
def TraceCoherenceCell.rightIdentity
    (source target : TraceRewritePath) : TraceCoherenceCell :=
  (TraceCoherenceKind.rightIdentity, source, target)

end AnalyticMotives
end LFunctions
end Boundary
