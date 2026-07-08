import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Algebraic.Soundness.Paths.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Coherence.Owner

/-!
# Algebraic soundness of higher coherences

This file owns the algebraic interpretation of higher computadic cells.

The current coherence layer records the concrete higher-cell data consumed by
the algebraic realization.  Downstream comparison files can identify these cells
with base change, projection formula, localization triangles, Gysin
functoriality, and correspondence associativity.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Algebraic coherence interpretation preserves the coherence kind. -/
theorem TraceAlgebraicSoundness.coherence_kind
    (cell : TraceCoherenceCell) :
    cell.kind =
      TraceCoherenceCell.kind cell :=
  rfl

/-- Algebraic coherence interpretation preserves the source rewrite path. -/
theorem TraceAlgebraicSoundness.coherence_source
    (cell : TraceCoherenceCell) :
    cell.source =
      TraceCoherenceCell.source cell :=
  rfl

/-- Algebraic coherence interpretation preserves the target rewrite path. -/
theorem TraceAlgebraicSoundness.coherence_target
    (cell : TraceCoherenceCell) :
    cell.target =
      TraceCoherenceCell.target cell :=
  rfl

/-- Algebraic Fubini coherence has Fubini kind. -/
theorem TraceAlgebraicSoundness.fubiniCoherence_kind
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.fubini source target).kind =
      TraceCoherenceKind.fubini :=
  TraceCoherenceCell.fubini_kind
    source
    target

/-- Algebraic residue-channel coherence has residue-channel kind. -/
theorem TraceAlgebraicSoundness.residueChannelCoherence_kind
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.residueChannel source target).kind =
      TraceCoherenceKind.residueChannel :=
  TraceCoherenceCell.residueChannel_kind
    source
    target

/-- Algebraic associativity coherence has associativity kind. -/
theorem TraceAlgebraicSoundness.associativityCoherence_kind
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.associativity source target).kind =
      TraceCoherenceKind.associativity :=
  TraceCoherenceCell.associativity_kind
    source
    target

/-- Algebraic left-identity coherence has left-identity kind. -/
theorem TraceAlgebraicSoundness.leftIdentityCoherence_kind
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.leftIdentity source target).kind =
      TraceCoherenceKind.leftIdentity :=
  TraceCoherenceCell.leftIdentity_kind
    source
    target

/-- Algebraic right-identity coherence has right-identity kind. -/
theorem TraceAlgebraicSoundness.rightIdentityCoherence_kind
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.rightIdentity source target).kind =
      TraceCoherenceKind.rightIdentity :=
  TraceCoherenceCell.rightIdentity_kind
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
