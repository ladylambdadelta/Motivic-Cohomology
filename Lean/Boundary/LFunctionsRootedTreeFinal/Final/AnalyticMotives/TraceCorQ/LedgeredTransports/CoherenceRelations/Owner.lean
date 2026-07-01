import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.LedgeredTransports.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Relations.Owner

/-!
# Coherence relation generators for ledgered transports

This file turns the associativity and identity coherence cells for ledgered
transports into pre-quotient relation generators.

Each relation generator records a coherence cell and the formal Q-linear
support `left - right` of the two raw transports related by that cell.  No
quotient relation is imposed here.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The formal Q-linear support `left - right` for two ledgered transports. -/
def LedgeredTraceTransport.coherenceSupport
    (left right : LedgeredTraceTransport) :
    TraceCorQFormalSum :=
  TraceCorQFormalSum.add
    (TraceCorQFormalSum.singleton 1 left.transport)
    (TraceCorQFormalSum.singleton (-1 : Rat) right.transport)

/-- The left summand of a ledgered transport coherence support. -/
theorem LedgeredTraceTransport.coherenceSupport_left
    (left right : LedgeredTraceTransport) :
    LedgeredTraceTransport.coherenceSupport left right =
      TraceCorQFormalSum.add
        (TraceCorQFormalSum.singleton 1 left.transport)
        (TraceCorQFormalSum.singleton (-1 : Rat) right.transport) :=
  rfl

/-- The associativity relation generator for three ledgered transports. -/
def LedgeredTraceTransport.associativityRelationGenerator
    (first second third : LedgeredTraceTransport) :
    TraceCorQRelationGenerator :=
  TraceCorQRelationGenerator.ofCellSupport
    (LedgeredTraceTransport.compAssociativityCoherence
      first second third)
    (LedgeredTraceTransport.coherenceSupport
      ((first.comp second).comp third)
      (first.comp (second.comp third)))

/-- The associativity relation generator is supported by the associativity cell. -/
theorem LedgeredTraceTransport.associativityRelationGenerator_cell
    (first second third : LedgeredTraceTransport) :
    (LedgeredTraceTransport.associativityRelationGenerator
      first second third).cell =
      LedgeredTraceTransport.compAssociativityCoherence
        first second third :=
  rfl

/-- The associativity relation generator has the expected formal support. -/
theorem LedgeredTraceTransport.associativityRelationGenerator_support
    (first second third : LedgeredTraceTransport) :
    (LedgeredTraceTransport.associativityRelationGenerator
      first second third).support =
      LedgeredTraceTransport.coherenceSupport
        ((first.comp second).comp third)
        (first.comp (second.comp third)) :=
  rfl

/-- The left-identity relation generator for a ledgered transport. -/
def LedgeredTraceTransport.leftIdentityRelationGenerator
    (transport : LedgeredTraceTransport) :
    TraceCorQRelationGenerator :=
  TraceCorQRelationGenerator.ofCellSupport
    (LedgeredTraceTransport.leftIdentityCoherence transport)
    (LedgeredTraceTransport.coherenceSupport
      ((LedgeredTraceTransport.id transport.source).comp transport)
      transport)

/-- The left-identity relation generator is supported by the left-identity cell. -/
theorem LedgeredTraceTransport.leftIdentityRelationGenerator_cell
    (transport : LedgeredTraceTransport) :
    (LedgeredTraceTransport.leftIdentityRelationGenerator transport).cell =
      LedgeredTraceTransport.leftIdentityCoherence transport :=
  rfl

/-- The left-identity relation generator has the expected formal support. -/
theorem LedgeredTraceTransport.leftIdentityRelationGenerator_support
    (transport : LedgeredTraceTransport) :
    (LedgeredTraceTransport.leftIdentityRelationGenerator transport).support =
      LedgeredTraceTransport.coherenceSupport
        ((LedgeredTraceTransport.id transport.source).comp transport)
        transport :=
  rfl

/-- The right-identity relation generator for a ledgered transport. -/
def LedgeredTraceTransport.rightIdentityRelationGenerator
    (transport : LedgeredTraceTransport) :
    TraceCorQRelationGenerator :=
  TraceCorQRelationGenerator.ofCellSupport
    (LedgeredTraceTransport.rightIdentityCoherence transport)
    (LedgeredTraceTransport.coherenceSupport
      (transport.comp (LedgeredTraceTransport.id transport.target))
      transport)

/-- The right-identity relation generator is supported by the right-identity cell. -/
theorem LedgeredTraceTransport.rightIdentityRelationGenerator_cell
    (transport : LedgeredTraceTransport) :
    (LedgeredTraceTransport.rightIdentityRelationGenerator transport).cell =
      LedgeredTraceTransport.rightIdentityCoherence transport :=
  rfl

/-- The right-identity relation generator has the expected formal support. -/
theorem LedgeredTraceTransport.rightIdentityRelationGenerator_support
    (transport : LedgeredTraceTransport) :
    (LedgeredTraceTransport.rightIdentityRelationGenerator transport).support =
      LedgeredTraceTransport.coherenceSupport
        (transport.comp (LedgeredTraceTransport.id transport.target))
        transport :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
