import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Coherence.Owner

/-!
# Rewrite relations

This file owns the concrete relations imposed between generated analytic
rewrites.  At the raw trace-computad level, a relation is a named higher
coherence cell between two finite rewrite paths.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A raw analytic rewrite relation is a higher coherence cell between paths. -/
abbrev TraceRewriteRelation :=
  TraceCoherenceCell

/-- The kind of a raw rewrite relation. -/
def TraceRewriteRelation.kind
    (relation : TraceRewriteRelation) :
    TraceCoherenceKind :=
  TraceCoherenceCell.kind relation

/-- The source path of a raw rewrite relation. -/
def TraceRewriteRelation.source
    (relation : TraceRewriteRelation) :
    TraceRewritePath :=
  TraceCoherenceCell.source relation

/-- The target path of a raw rewrite relation. -/
def TraceRewriteRelation.target
    (relation : TraceRewriteRelation) :
    TraceRewritePath :=
  TraceCoherenceCell.target relation

/-- A Fubini rewrite relation between two rewrite paths. -/
def TraceRewriteRelation.fubini
    (source target : TraceRewritePath) :
    TraceRewriteRelation :=
  TraceCoherenceCell.fubini source target

/-- A schedule-exchange rewrite relation between two rewrite paths. -/
def TraceRewriteRelation.scheduleExchange
    (source target : TraceRewritePath) :
    TraceRewriteRelation :=
  TraceCoherenceCell.scheduleExchange source target

/-- A residue-channel rewrite relation between two rewrite paths. -/
def TraceRewriteRelation.residueChannel
    (source target : TraceRewritePath) :
    TraceRewriteRelation :=
  TraceCoherenceCell.residueChannel source target

/-- A Stokes-residue rewrite relation between two rewrite paths. -/
def TraceRewriteRelation.stokesResidue
    (source target : TraceRewritePath) :
    TraceRewriteRelation :=
  TraceCoherenceCell.stokesResidue source target

/-- A refinement rewrite relation between two rewrite paths. -/
def TraceRewriteRelation.refinement
    (source target : TraceRewritePath) :
    TraceRewriteRelation :=
  TraceCoherenceCell.refinement source target

/-- An associativity rewrite relation between two rewrite paths. -/
def TraceRewriteRelation.associativity
    (source target : TraceRewritePath) :
    TraceRewriteRelation :=
  TraceCoherenceCell.associativity source target

/-- A left-identity rewrite relation between two rewrite paths. -/
def TraceRewriteRelation.leftIdentity
    (source target : TraceRewritePath) :
    TraceRewriteRelation :=
  TraceCoherenceCell.leftIdentity source target

/-- A right-identity rewrite relation between two rewrite paths. -/
def TraceRewriteRelation.rightIdentity
    (source target : TraceRewritePath) :
    TraceRewriteRelation :=
  TraceCoherenceCell.rightIdentity source target

/-- A Fubini rewrite relation has Fubini kind. -/
theorem TraceRewriteRelation.fubini_kind
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.fubini source target).kind =
      TraceCoherenceKind.fubini :=
  TraceCoherenceCell.fubini_kind
    source
    target

/-- A Fubini rewrite relation has the supplied source path. -/
theorem TraceRewriteRelation.fubini_source
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.fubini source target).source =
      source :=
  TraceCoherenceCell.fubini_source
    source
    target

/-- A Fubini rewrite relation has the supplied target path. -/
theorem TraceRewriteRelation.fubini_target
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.fubini source target).target =
      target :=
  TraceCoherenceCell.fubini_target
    source
    target

/-- A schedule-exchange rewrite relation has schedule-exchange kind. -/
theorem TraceRewriteRelation.scheduleExchange_kind
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.scheduleExchange source target).kind =
      TraceCoherenceKind.scheduleExchange :=
  TraceCoherenceCell.scheduleExchange_kind
    source
    target

/-- A schedule-exchange rewrite relation has the supplied source path. -/
theorem TraceRewriteRelation.scheduleExchange_source
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.scheduleExchange source target).source =
      source :=
  TraceCoherenceCell.scheduleExchange_source
    source
    target

/-- A schedule-exchange rewrite relation has the supplied target path. -/
theorem TraceRewriteRelation.scheduleExchange_target
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.scheduleExchange source target).target =
      target :=
  TraceCoherenceCell.scheduleExchange_target
    source
    target

/-- A residue-channel rewrite relation has residue-channel kind. -/
theorem TraceRewriteRelation.residueChannel_kind
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.residueChannel source target).kind =
      TraceCoherenceKind.residueChannel :=
  TraceCoherenceCell.residueChannel_kind
    source
    target

/-- A residue-channel rewrite relation has the supplied source path. -/
theorem TraceRewriteRelation.residueChannel_source
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.residueChannel source target).source =
      source :=
  TraceCoherenceCell.residueChannel_source
    source
    target

/-- A residue-channel rewrite relation has the supplied target path. -/
theorem TraceRewriteRelation.residueChannel_target
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.residueChannel source target).target =
      target :=
  TraceCoherenceCell.residueChannel_target
    source
    target

/-- A Stokes-residue rewrite relation has Stokes-residue kind. -/
theorem TraceRewriteRelation.stokesResidue_kind
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.stokesResidue source target).kind =
      TraceCoherenceKind.stokesResidue :=
  TraceCoherenceCell.stokesResidue_kind
    source
    target

/-- A Stokes-residue rewrite relation has the supplied source path. -/
theorem TraceRewriteRelation.stokesResidue_source
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.stokesResidue source target).source =
      source :=
  TraceCoherenceCell.stokesResidue_source
    source
    target

/-- A Stokes-residue rewrite relation has the supplied target path. -/
theorem TraceRewriteRelation.stokesResidue_target
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.stokesResidue source target).target =
      target :=
  TraceCoherenceCell.stokesResidue_target
    source
    target

/-- A refinement rewrite relation has refinement kind. -/
theorem TraceRewriteRelation.refinement_kind
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.refinement source target).kind =
      TraceCoherenceKind.refinement :=
  TraceCoherenceCell.refinement_kind
    source
    target

/-- A refinement rewrite relation has the supplied source path. -/
theorem TraceRewriteRelation.refinement_source
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.refinement source target).source =
      source :=
  TraceCoherenceCell.refinement_source
    source
    target

/-- A refinement rewrite relation has the supplied target path. -/
theorem TraceRewriteRelation.refinement_target
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.refinement source target).target =
      target :=
  TraceCoherenceCell.refinement_target
    source
    target

/-- An associativity rewrite relation has associativity kind. -/
theorem TraceRewriteRelation.associativity_kind
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.associativity source target).kind =
      TraceCoherenceKind.associativity :=
  TraceCoherenceCell.associativity_kind
    source
    target

/-- An associativity rewrite relation has the supplied source path. -/
theorem TraceRewriteRelation.associativity_source
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.associativity source target).source =
      source :=
  TraceCoherenceCell.associativity_source
    source
    target

/-- An associativity rewrite relation has the supplied target path. -/
theorem TraceRewriteRelation.associativity_target
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.associativity source target).target =
      target :=
  TraceCoherenceCell.associativity_target
    source
    target

/-- A left-identity rewrite relation has left-identity kind. -/
theorem TraceRewriteRelation.leftIdentity_kind
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.leftIdentity source target).kind =
      TraceCoherenceKind.leftIdentity :=
  TraceCoherenceCell.leftIdentity_kind
    source
    target

/-- A left-identity rewrite relation has the supplied source path. -/
theorem TraceRewriteRelation.leftIdentity_source
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.leftIdentity source target).source =
      source :=
  TraceCoherenceCell.leftIdentity_source
    source
    target

/-- A left-identity rewrite relation has the supplied target path. -/
theorem TraceRewriteRelation.leftIdentity_target
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.leftIdentity source target).target =
      target :=
  TraceCoherenceCell.leftIdentity_target
    source
    target

/-- A right-identity rewrite relation has right-identity kind. -/
theorem TraceRewriteRelation.rightIdentity_kind
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.rightIdentity source target).kind =
      TraceCoherenceKind.rightIdentity :=
  TraceCoherenceCell.rightIdentity_kind
    source
    target

/-- A right-identity rewrite relation has the supplied source path. -/
theorem TraceRewriteRelation.rightIdentity_source
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.rightIdentity source target).source =
      source :=
  TraceCoherenceCell.rightIdentity_source
    source
    target

/-- A right-identity rewrite relation has the supplied target path. -/
theorem TraceRewriteRelation.rightIdentity_target
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.rightIdentity source target).target =
      target :=
  TraceCoherenceCell.rightIdentity_target
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
