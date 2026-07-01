import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.Channels.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleTraceValue.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleGenerator.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleChannelDecomposition.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleChannelGenerator.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleBoundaryRefinement.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleVerticalTransport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleDecayInputs.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleTangentConvergence.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPolePresentationSpines.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleCertifiedPresentations.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleTransports.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleTraceCorQ.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleAnalyticChain.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleCoherence.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleRelations.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleRelationLedger.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleLedgeredTransports.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleQuotientInput.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleQuotientCandidate.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleRelationWitness.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Soundness.Generators.Owner

/-!
# Completed-zeta finite-rectangle soundness seed

This file is the owner home for the first concrete analytic soundness theorem
linking a synthetic rewrite generator to an imported finite-rectangle contour
identity.

The first selected seed is documented in `SeedMap/Owner.lean` and exposed as
concrete analytic trace-value equality in `ZeroPoleTraceValue/Owner.lean`.
The corresponding synthetic residue generator and its narrow soundness theorem
live in `ZeroPoleGenerator/Owner.lean`.

The next seed is a concrete scheduled channel-decomposition theorem in
`ZeroPoleChannelDecomposition/Owner.lean`, with its matching synthetic
generator in `ZeroPoleChannelGenerator/Owner.lean`.

The raw presentation spines for both seeds live in
`ZeroPolePresentationSpines/Owner.lean`.

The concrete certificates attached to those spines live in
`ZeroPoleCertifiedPresentations/Owner.lean`.

The corresponding one-step transports live in
`ZeroPoleTransports/Owner.lean`.

The same transports are exposed as raw `TraceCorQ` generators and singleton
Q-linear formal sums in `ZeroPoleTraceCorQ/Owner.lean`.

The analytic boundary-refinement bridge needed before honest composition lives
in `ZeroPoleBoundaryRefinement/Owner.lean`.

The scheduled vertical-orientation transport lives in
`ZeroPoleVerticalTransport/Owner.lean`.

The decay inputs consumed by that transport live in
`ZeroPoleDecayInputs/Owner.lean`.

The tangent-boundary convergence input and the resulting right-vertical
convergence theorem live in `ZeroPoleTangentConvergence/Owner.lean`.

The first named analytic trace chain lives in
`ZeroPoleAnalyticChain/Owner.lean`.

The first residue-channel coherence cell backed by that chain lives in
`ZeroPoleCoherence/Owner.lean`.

The first trace-correspondence relation generator backed by that coherence cell
lives in `ZeroPoleRelations/Owner.lean`.

The first finite relation ledger lives in
`ZeroPoleRelationLedger/Owner.lean`.

The first ledger-supported zero-pole transports live in
`ZeroPoleLedgeredTransports/Owner.lean`.

The first zero-pole pre-quotient input lives in
`ZeroPoleQuotientInput/Owner.lean`.

The first zero-pole raw quotient candidate lives in
`ZeroPoleQuotientCandidate/Owner.lean`.

The canonical zero-pole relation-generator witness lives in
`ZeroPoleRelationWitness/Owner.lean`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

end AnalyticMotives
end LFunctions
end Boundary
