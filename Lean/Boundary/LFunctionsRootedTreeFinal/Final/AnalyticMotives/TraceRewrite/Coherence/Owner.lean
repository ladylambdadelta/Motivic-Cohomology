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

/-- A Stokes-residue compatibility coherence cell. -/
def TraceCoherenceCell.stokesResidue
    (source target : TraceRewritePath) : TraceCoherenceCell :=
  (TraceCoherenceKind.stokesResidue, source, target)

/-- A refinement compatibility coherence cell. -/
def TraceCoherenceCell.refinement
    (source target : TraceRewritePath) : TraceCoherenceCell :=
  (TraceCoherenceKind.refinement, source, target)

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

/-- A Fubini coherence cell has Fubini kind. -/
theorem TraceCoherenceCell.fubini_kind
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.fubini source target).kind =
      TraceCoherenceKind.fubini :=
  rfl

/-- A Fubini coherence cell has the supplied source path. -/
theorem TraceCoherenceCell.fubini_source
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.fubini source target).source =
      source :=
  rfl

/-- A Fubini coherence cell has the supplied target path. -/
theorem TraceCoherenceCell.fubini_target
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.fubini source target).target =
      target :=
  rfl

/-- A schedule-exchange coherence cell has schedule-exchange kind. -/
theorem TraceCoherenceCell.scheduleExchange_kind
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.scheduleExchange source target).kind =
      TraceCoherenceKind.scheduleExchange :=
  rfl

/-- A schedule-exchange coherence cell has the supplied source path. -/
theorem TraceCoherenceCell.scheduleExchange_source
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.scheduleExchange source target).source =
      source :=
  rfl

/-- A schedule-exchange coherence cell has the supplied target path. -/
theorem TraceCoherenceCell.scheduleExchange_target
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.scheduleExchange source target).target =
      target :=
  rfl

/-- A residue-channel coherence cell has residue-channel kind. -/
theorem TraceCoherenceCell.residueChannel_kind
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.residueChannel source target).kind =
      TraceCoherenceKind.residueChannel :=
  rfl

/-- A residue-channel coherence cell has the supplied source path. -/
theorem TraceCoherenceCell.residueChannel_source
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.residueChannel source target).source =
      source :=
  rfl

/-- A residue-channel coherence cell has the supplied target path. -/
theorem TraceCoherenceCell.residueChannel_target
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.residueChannel source target).target =
      target :=
  rfl

/-- A Stokes-residue coherence cell has Stokes-residue kind. -/
theorem TraceCoherenceCell.stokesResidue_kind
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.stokesResidue source target).kind =
      TraceCoherenceKind.stokesResidue :=
  rfl

/-- A Stokes-residue coherence cell has the supplied source path. -/
theorem TraceCoherenceCell.stokesResidue_source
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.stokesResidue source target).source =
      source :=
  rfl

/-- A Stokes-residue coherence cell has the supplied target path. -/
theorem TraceCoherenceCell.stokesResidue_target
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.stokesResidue source target).target =
      target :=
  rfl

/-- A refinement coherence cell has refinement kind. -/
theorem TraceCoherenceCell.refinement_kind
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.refinement source target).kind =
      TraceCoherenceKind.refinement :=
  rfl

/-- A refinement coherence cell has the supplied source path. -/
theorem TraceCoherenceCell.refinement_source
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.refinement source target).source =
      source :=
  rfl

/-- A refinement coherence cell has the supplied target path. -/
theorem TraceCoherenceCell.refinement_target
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.refinement source target).target =
      target :=
  rfl

/-- An associativity coherence cell has associativity kind. -/
theorem TraceCoherenceCell.associativity_kind
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.associativity source target).kind =
      TraceCoherenceKind.associativity :=
  rfl

/-- An associativity coherence cell has the supplied source path. -/
theorem TraceCoherenceCell.associativity_source
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.associativity source target).source =
      source :=
  rfl

/-- An associativity coherence cell has the supplied target path. -/
theorem TraceCoherenceCell.associativity_target
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.associativity source target).target =
      target :=
  rfl

/-- A left-identity coherence cell has left-identity kind. -/
theorem TraceCoherenceCell.leftIdentity_kind
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.leftIdentity source target).kind =
      TraceCoherenceKind.leftIdentity :=
  rfl

/-- A left-identity coherence cell has the supplied source path. -/
theorem TraceCoherenceCell.leftIdentity_source
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.leftIdentity source target).source =
      source :=
  rfl

/-- A left-identity coherence cell has the supplied target path. -/
theorem TraceCoherenceCell.leftIdentity_target
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.leftIdentity source target).target =
      target :=
  rfl

/-- A right-identity coherence cell has right-identity kind. -/
theorem TraceCoherenceCell.rightIdentity_kind
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.rightIdentity source target).kind =
      TraceCoherenceKind.rightIdentity :=
  rfl

/-- A right-identity coherence cell has the supplied source path. -/
theorem TraceCoherenceCell.rightIdentity_source
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.rightIdentity source target).source =
      source :=
  rfl

/-- A right-identity coherence cell has the supplied target path. -/
theorem TraceCoherenceCell.rightIdentity_target
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.rightIdentity source target).target =
      target :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
