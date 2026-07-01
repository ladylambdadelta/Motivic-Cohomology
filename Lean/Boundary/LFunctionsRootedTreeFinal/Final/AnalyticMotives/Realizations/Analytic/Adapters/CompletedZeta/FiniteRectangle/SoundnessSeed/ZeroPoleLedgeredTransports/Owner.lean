import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleRelationLedger.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleTransports.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.LedgeredTransports.Owner

/-!
# Zero-pole ledger-supported transports

This file attaches the zero-pole relation ledger to the concrete residue and
channel transports.

The declarations here remain pre-quotient.  They do not assert that the two
transports compose.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The zero-pole residue transport equipped with the zero-pole relation ledger. -/
def completedZetaZeroPoleLedgeredResidueTransport :
    LedgeredTraceTransport :=
  LedgeredTraceTransport.ofTransportLedger
    completedZetaZeroPoleResidueTransport
    completedZetaZeroPoleTraceCorQRelationLedger

/-- The zero-pole ledgered residue transport has the expected raw transport. -/
theorem completedZetaZeroPoleLedgeredResidueTransport_transport :
    completedZetaZeroPoleLedgeredResidueTransport.transport =
      completedZetaZeroPoleResidueTransport :=
  rfl

/-- The zero-pole ledgered residue transport has the zero-pole relation ledger. -/
theorem completedZetaZeroPoleLedgeredResidueTransport_ledger :
    completedZetaZeroPoleLedgeredResidueTransport.ledger =
      completedZetaZeroPoleTraceCorQRelationLedger :=
  rfl

/-- The zero-pole ledgered residue transport starts at the residue presentation spine. -/
theorem completedZetaZeroPoleLedgeredResidueTransport_source :
    completedZetaZeroPoleLedgeredResidueTransport.source =
      completedZetaZeroPoleResiduePresentationSpine :=
  rfl

/-- The zero-pole ledgered residue transport targets the residue output spine. -/
theorem completedZetaZeroPoleLedgeredResidueTransport_target :
    completedZetaZeroPoleLedgeredResidueTransport.target =
      completedZetaZeroPoleResidueOutputSpine :=
  rfl

/-- The zero-pole ledgered residue transport carries the residue path. -/
theorem completedZetaZeroPoleLedgeredResidueTransport_path :
    completedZetaZeroPoleLedgeredResidueTransport.path =
      completedZetaZeroPoleResiduePath :=
  rfl

/-- The zero-pole channel transport equipped with the zero-pole relation ledger. -/
def completedZetaZeroPoleLedgeredChannelTransport :
    LedgeredTraceTransport :=
  LedgeredTraceTransport.ofTransportLedger
    completedZetaZeroPoleChannelTransport
    completedZetaZeroPoleTraceCorQRelationLedger

/-- The zero-pole ledgered channel transport has the expected raw transport. -/
theorem completedZetaZeroPoleLedgeredChannelTransport_transport :
    completedZetaZeroPoleLedgeredChannelTransport.transport =
      completedZetaZeroPoleChannelTransport :=
  rfl

/-- The zero-pole ledgered channel transport has the zero-pole relation ledger. -/
theorem completedZetaZeroPoleLedgeredChannelTransport_ledger :
    completedZetaZeroPoleLedgeredChannelTransport.ledger =
      completedZetaZeroPoleTraceCorQRelationLedger :=
  rfl

/-- The zero-pole ledgered channel transport starts at the channel presentation spine. -/
theorem completedZetaZeroPoleLedgeredChannelTransport_source :
    completedZetaZeroPoleLedgeredChannelTransport.source =
      completedZetaZeroPoleChannelPresentationSpine :=
  rfl

/-- The zero-pole ledgered channel transport targets the channel output spine. -/
theorem completedZetaZeroPoleLedgeredChannelTransport_target :
    completedZetaZeroPoleLedgeredChannelTransport.target =
      completedZetaZeroPoleChannelOutputSpine :=
  rfl

/-- The zero-pole ledgered channel transport carries the channel path. -/
theorem completedZetaZeroPoleLedgeredChannelTransport_path :
    completedZetaZeroPoleLedgeredChannelTransport.path =
      completedZetaZeroPoleChannelPath :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
