import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Algebraic.Soundness.Coherence.Owner

/-!
# Top-root algebraic coherence soundness

This file exposes concrete higher-coherence data preserved by the algebraic
realization at the public analytic-motives root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Algebraic coherence interpretation preserves the coherence kind. -/
theorem AnalyticMotivesRoot.algebraicSoundness_coherence_kind
    (cell : TraceCoherenceCell) :
    cell.kind =
      TraceCoherenceCell.kind cell :=
  TraceAlgebraicSoundness.coherence_kind
    cell

/-- Algebraic coherence interpretation preserves the source rewrite path. -/
theorem AnalyticMotivesRoot.algebraicSoundness_coherence_source
    (cell : TraceCoherenceCell) :
    cell.source =
      TraceCoherenceCell.source cell :=
  TraceAlgebraicSoundness.coherence_source
    cell

/-- Algebraic coherence interpretation preserves the target rewrite path. -/
theorem AnalyticMotivesRoot.algebraicSoundness_coherence_target
    (cell : TraceCoherenceCell) :
    cell.target =
      TraceCoherenceCell.target cell :=
  TraceAlgebraicSoundness.coherence_target
    cell

/-- Algebraic Fubini coherence has Fubini kind. -/
theorem AnalyticMotivesRoot.algebraicSoundness_fubiniCoherence_kind
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.fubini source target).kind =
      TraceCoherenceKind.fubini :=
  TraceAlgebraicSoundness.fubiniCoherence_kind
    source
    target

/-- Algebraic residue-channel coherence has residue-channel kind. -/
theorem AnalyticMotivesRoot.algebraicSoundness_residueChannelCoherence_kind
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.residueChannel source target).kind =
      TraceCoherenceKind.residueChannel :=
  TraceAlgebraicSoundness.residueChannelCoherence_kind
    source
    target

/-- Algebraic associativity coherence has associativity kind. -/
theorem AnalyticMotivesRoot.algebraicSoundness_associativityCoherence_kind
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.associativity source target).kind =
      TraceCoherenceKind.associativity :=
  TraceAlgebraicSoundness.associativityCoherence_kind
    source
    target

/-- Algebraic left-identity coherence has left-identity kind. -/
theorem AnalyticMotivesRoot.algebraicSoundness_leftIdentityCoherence_kind
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.leftIdentity source target).kind =
      TraceCoherenceKind.leftIdentity :=
  TraceAlgebraicSoundness.leftIdentityCoherence_kind
    source
    target

/-- Algebraic right-identity coherence has right-identity kind. -/
theorem AnalyticMotivesRoot.algebraicSoundness_rightIdentityCoherence_kind
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.rightIdentity source target).kind =
      TraceCoherenceKind.rightIdentity :=
  TraceAlgebraicSoundness.rightIdentityCoherence_kind
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
