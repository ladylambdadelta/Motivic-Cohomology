import TraceCalc.LayerB.RealObjects.Composition

/-!
# Real-objects formalization: replay interface contract

This file holds the signature-only replay interface that downstream consumers
may target before a concrete replay semantics is fixed. It is intentionally
kept outside the Layer B core theorem spine: the core composition results live
in `Composition.lean`, while the abstract replay contract remains a non-core
compatibility seam.
-/

universe u

namespace TraceCalc
namespace LayerB
namespace RealObjects
namespace RewriteCalculusSetup

/-- **Replay interface (signature only).** A replay assigns to each
certified trace a "replay value" of some carrier type. The exact target
carrier is left abstract here; a future implementation may instantiate it. -/
structure ReplayInterface (setup : RewriteCalculusSetup.{u}) where
  /-- Carrier of replay values, parametrized by source/target states. -/
  Value : setup.State → setup.State → Type u
  /-- Replay of the empty/identity certified trace yields a designated
  identity value. -/
  replayId : (X : setup.State) → Value X X
  /-- Replay of a composition is the composition of replays. This is only the
  signature shape; no proof-relevant semantics is imposed here. -/
  replayCompose :
    {X Y Z : setup.State} →
    Value X Y → Value Y Z → Value X Z

/-- **Replay-empty signature.** The identity certified trace's replay is the
identity replay value. -/
def ReplayInterface.IsCorrectOnIdentity {setup : RewriteCalculusSetup.{u}}
    (R : ReplayInterface setup)
    (replay : ∀ {X Y : setup.State}, setup.CertifiedTrace X Y → R.Value X Y) :
    Prop :=
  ∀ X : setup.State, replay (idCertifiedTrace X) = R.replayId X

/-- **Replay-compose signature.** A replay assignment respects composition. -/
def ReplayInterface.IsCorrectOnCompose {setup : RewriteCalculusSetup.{u}}
    (R : ReplayInterface setup)
    (replay : ∀ {X Y : setup.State}, setup.CertifiedTrace X Y → R.Value X Y) :
    Prop :=
  ∀ {X Y Z : setup.State}
    (T : setup.CertifiedTrace X Y) (T' : setup.CertifiedTrace Y Z),
    replay (T.compose T') = R.replayCompose (replay T) (replay T')

end RewriteCalculusSetup
end RealObjects
end LayerB
end TraceCalc