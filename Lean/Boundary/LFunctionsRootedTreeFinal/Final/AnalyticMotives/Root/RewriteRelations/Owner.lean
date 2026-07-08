import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Relations.Owner

/-!
# Top-root rewrite relations

This file exposes the concrete named higher relations between analytic trace
rewrite paths under the top-level `AnalyticMotivesRoot` namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A top-root Fubini rewrite relation has Fubini kind. -/
theorem AnalyticMotivesRoot.fubiniRewriteRelation_kind
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.fubini source target).kind =
      TraceCoherenceKind.fubini :=
  TraceRewriteRelation.fubini_kind
    source
    target

/-- A top-root Fubini rewrite relation has the supplied source path. -/
theorem AnalyticMotivesRoot.fubiniRewriteRelation_source
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.fubini source target).source =
      source :=
  TraceRewriteRelation.fubini_source
    source
    target

/-- A top-root Fubini rewrite relation has the supplied target path. -/
theorem AnalyticMotivesRoot.fubiniRewriteRelation_target
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.fubini source target).target =
      target :=
  TraceRewriteRelation.fubini_target
    source
    target

/-- A top-root schedule-exchange rewrite relation has schedule-exchange kind. -/
theorem AnalyticMotivesRoot.scheduleExchangeRewriteRelation_kind
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.scheduleExchange source target).kind =
      TraceCoherenceKind.scheduleExchange :=
  TraceRewriteRelation.scheduleExchange_kind
    source
    target

/-- A top-root schedule-exchange rewrite relation has the supplied source path. -/
theorem AnalyticMotivesRoot.scheduleExchangeRewriteRelation_source
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.scheduleExchange source target).source =
      source :=
  TraceRewriteRelation.scheduleExchange_source
    source
    target

/-- A top-root schedule-exchange rewrite relation has the supplied target path. -/
theorem AnalyticMotivesRoot.scheduleExchangeRewriteRelation_target
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.scheduleExchange source target).target =
      target :=
  TraceRewriteRelation.scheduleExchange_target
    source
    target

/-- A top-root residue-channel rewrite relation has residue-channel kind. -/
theorem AnalyticMotivesRoot.residueChannelRewriteRelation_kind
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.residueChannel source target).kind =
      TraceCoherenceKind.residueChannel :=
  TraceRewriteRelation.residueChannel_kind
    source
    target

/-- A top-root residue-channel rewrite relation has the supplied source path. -/
theorem AnalyticMotivesRoot.residueChannelRewriteRelation_source
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.residueChannel source target).source =
      source :=
  TraceRewriteRelation.residueChannel_source
    source
    target

/-- A top-root residue-channel rewrite relation has the supplied target path. -/
theorem AnalyticMotivesRoot.residueChannelRewriteRelation_target
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.residueChannel source target).target =
      target :=
  TraceRewriteRelation.residueChannel_target
    source
    target

/-- A top-root Stokes-residue rewrite relation has Stokes-residue kind. -/
theorem AnalyticMotivesRoot.stokesResidueRewriteRelation_kind
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.stokesResidue source target).kind =
      TraceCoherenceKind.stokesResidue :=
  TraceRewriteRelation.stokesResidue_kind
    source
    target

/-- A top-root Stokes-residue rewrite relation has the supplied source path. -/
theorem AnalyticMotivesRoot.stokesResidueRewriteRelation_source
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.stokesResidue source target).source =
      source :=
  TraceRewriteRelation.stokesResidue_source
    source
    target

/-- A top-root Stokes-residue rewrite relation has the supplied target path. -/
theorem AnalyticMotivesRoot.stokesResidueRewriteRelation_target
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.stokesResidue source target).target =
      target :=
  TraceRewriteRelation.stokesResidue_target
    source
    target

/-- A top-root refinement rewrite relation has refinement kind. -/
theorem AnalyticMotivesRoot.refinementRewriteRelation_kind
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.refinement source target).kind =
      TraceCoherenceKind.refinement :=
  TraceRewriteRelation.refinement_kind
    source
    target

/-- A top-root refinement rewrite relation has the supplied source path. -/
theorem AnalyticMotivesRoot.refinementRewriteRelation_source
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.refinement source target).source =
      source :=
  TraceRewriteRelation.refinement_source
    source
    target

/-- A top-root refinement rewrite relation has the supplied target path. -/
theorem AnalyticMotivesRoot.refinementRewriteRelation_target
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.refinement source target).target =
      target :=
  TraceRewriteRelation.refinement_target
    source
    target

/-- A top-root associativity rewrite relation has associativity kind. -/
theorem AnalyticMotivesRoot.associativityRewriteRelation_kind
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.associativity source target).kind =
      TraceCoherenceKind.associativity :=
  TraceRewriteRelation.associativity_kind
    source
    target

/-- A top-root associativity rewrite relation has the supplied source path. -/
theorem AnalyticMotivesRoot.associativityRewriteRelation_source
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.associativity source target).source =
      source :=
  TraceRewriteRelation.associativity_source
    source
    target

/-- A top-root associativity rewrite relation has the supplied target path. -/
theorem AnalyticMotivesRoot.associativityRewriteRelation_target
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.associativity source target).target =
      target :=
  TraceRewriteRelation.associativity_target
    source
    target

/-- A top-root left-identity rewrite relation has left-identity kind. -/
theorem AnalyticMotivesRoot.leftIdentityRewriteRelation_kind
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.leftIdentity source target).kind =
      TraceCoherenceKind.leftIdentity :=
  TraceRewriteRelation.leftIdentity_kind
    source
    target

/-- A top-root left-identity rewrite relation has the supplied source path. -/
theorem AnalyticMotivesRoot.leftIdentityRewriteRelation_source
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.leftIdentity source target).source =
      source :=
  TraceRewriteRelation.leftIdentity_source
    source
    target

/-- A top-root left-identity rewrite relation has the supplied target path. -/
theorem AnalyticMotivesRoot.leftIdentityRewriteRelation_target
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.leftIdentity source target).target =
      target :=
  TraceRewriteRelation.leftIdentity_target
    source
    target

/-- A top-root right-identity rewrite relation has right-identity kind. -/
theorem AnalyticMotivesRoot.rightIdentityRewriteRelation_kind
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.rightIdentity source target).kind =
      TraceCoherenceKind.rightIdentity :=
  TraceRewriteRelation.rightIdentity_kind
    source
    target

/-- A top-root right-identity rewrite relation has the supplied source path. -/
theorem AnalyticMotivesRoot.rightIdentityRewriteRelation_source
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.rightIdentity source target).source =
      source :=
  TraceRewriteRelation.rightIdentity_source
    source
    target

/-- A top-root right-identity rewrite relation has the supplied target path. -/
theorem AnalyticMotivesRoot.rightIdentityRewriteRelation_target
    (source target : TraceRewritePath) :
    (TraceRewriteRelation.rightIdentity source target).target =
      target :=
  TraceRewriteRelation.rightIdentity_target
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
