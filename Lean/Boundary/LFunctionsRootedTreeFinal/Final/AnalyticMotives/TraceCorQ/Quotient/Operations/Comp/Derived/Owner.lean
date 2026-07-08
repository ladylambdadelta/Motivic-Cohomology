import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Comp.Laws.Derived.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Comp.AssociativitySupport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Comp.AssociativitySupport.Certificates.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Comp.IdentitySupport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Comp.IdentitySupport.Certificates.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Comp.Associativity.Owner

/-!
# Derived quotient composition operations

This aggregate owns quotient composition facts downstream from the primitive
quotient composition operation.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Derived composition aggregate: zero composed on the left is zero. -/
theorem TraceCorQQuotient.comp_derived_zero_comp
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      TraceCorQQuotient.zero
      candidateClass =
      TraceCorQQuotient.zero :=
  TraceCorQQuotient.zero_comp candidateClass

/-- Derived composition aggregate: zero composed on the right is zero. -/
theorem TraceCorQQuotient.comp_derived_comp_zero
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      candidateClass
      TraceCorQQuotient.zero =
      TraceCorQQuotient.zero :=
  TraceCorQQuotient.comp_zero candidateClass

/-- Derived composition aggregate: composition is left-distributive over addition. -/
theorem TraceCorQQuotient.comp_derived_add_comp
    (left right tail : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      (TraceCorQQuotient.add left right)
      tail =
      TraceCorQQuotient.add
        (TraceCorQQuotient.comp left tail)
        (TraceCorQQuotient.comp right tail) :=
  TraceCorQQuotient.add_comp left right tail

/-- Derived composition aggregate: composition is right-distributive over addition. -/
theorem TraceCorQQuotient.comp_derived_comp_add
    (left right tail : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      left
      (TraceCorQQuotient.add right tail) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.comp left right)
        (TraceCorQQuotient.comp left tail) :=
  TraceCorQQuotient.comp_add left right tail

/-- Derived composition aggregate: composition is left-distributive over subtraction. -/
theorem TraceCorQQuotient.comp_derived_sub_comp
    (left right tail : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      (TraceCorQQuotient.sub left right)
      tail =
      TraceCorQQuotient.sub
        (TraceCorQQuotient.comp left tail)
        (TraceCorQQuotient.comp right tail) :=
  TraceCorQQuotient.sub_comp left right tail

/-- Derived composition aggregate: composition is right-distributive over subtraction. -/
theorem TraceCorQQuotient.comp_derived_comp_sub
    (left right tail : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      left
      (TraceCorQQuotient.sub right tail) =
      TraceCorQQuotient.sub
        (TraceCorQQuotient.comp left right)
        (TraceCorQQuotient.comp left tail) :=
  TraceCorQQuotient.comp_sub left right tail

/-- Derived composition aggregate: quotient composition is associative. -/
theorem TraceCorQQuotient.comp_derived_assoc
    (left middle right : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      (TraceCorQQuotient.comp left middle)
      right =
      TraceCorQQuotient.comp
        left
        (TraceCorQQuotient.comp middle right) :=
  TraceCorQQuotient.comp_assoc left middle right

/-- Derived composition aggregate: weighted singleton left identity. -/
theorem TraceCorQGenerator.comp_derived_leftIdentityWeightedSingletonQuotient_eq
    (coefficient : Rat)
    (generator : TraceCorQGenerator) :
    TraceCorQQuotient.singleton
      coefficient
      (TraceCorQGenerator.comp
        (TraceCorQGenerator.id generator.source)
        generator) =
      TraceCorQQuotient.singleton
        coefficient
        generator :=
  TraceCorQGenerator.leftIdentityWeightedSingletonQuotient_eq
    coefficient
    generator

/-- Derived composition aggregate: weighted singleton right identity. -/
theorem TraceCorQGenerator.comp_derived_rightIdentityWeightedSingletonQuotient_eq
    (coefficient : Rat)
    (generator : TraceCorQGenerator) :
    TraceCorQQuotient.singleton
      coefficient
      (TraceCorQGenerator.comp
        generator
        (TraceCorQGenerator.id generator.target)) =
      TraceCorQQuotient.singleton
        coefficient
        generator :=
  TraceCorQGenerator.rightIdentityWeightedSingletonQuotient_eq
    coefficient
    generator

/-- Derived composition aggregate: weighted singleton associativity. -/
theorem TraceCorQQuotient.comp_derived_assoc_singleton
    (firstCoefficient secondCoefficient thirdCoefficient : Rat)
    (first second third : TraceCorQGenerator) :
    TraceCorQQuotient.comp
      (TraceCorQQuotient.comp
        (TraceCorQQuotient.singleton firstCoefficient first)
        (TraceCorQQuotient.singleton secondCoefficient second))
      (TraceCorQQuotient.singleton thirdCoefficient third) =
      TraceCorQQuotient.comp
        (TraceCorQQuotient.singleton firstCoefficient first)
        (TraceCorQQuotient.comp
          (TraceCorQQuotient.singleton secondCoefficient second)
          (TraceCorQQuotient.singleton thirdCoefficient third)) :=
  TraceCorQQuotient.comp_assoc_singleton
    firstCoefficient
    secondCoefficient
    thirdCoefficient
    first
    second
    third

/-- Derived composition aggregate: associativity support witnesses carry analytic certificates. -/
theorem LedgeredTraceTransport.comp_derived_associativitySupportWitness_certificateLedger
    (first second third : LedgeredTraceTransport) :
    (LedgeredTraceTransport.associativitySupportWitness
      first
      second
      third).certificateLedger =
      ResidueChannelCertificateLedger.append
        (LedgeredTraceTransport.associativityCertificateLedger
          first
          second
          third)
        ResidueChannelCertificateLedger.empty :=
  LedgeredTraceTransport.associativitySupportWitness_certificateLedger
    first
    second
    third

/-- Derived composition aggregate: left-identity support witnesses carry analytic certificates. -/
theorem LedgeredTraceTransport.comp_derived_leftIdentitySupportWitness_certificateLedger
    (transport : LedgeredTraceTransport) :
    (LedgeredTraceTransport.leftIdentitySupportWitness transport).certificateLedger =
      ResidueChannelCertificateLedger.append
        (LedgeredTraceTransport.leftIdentityCertificateLedger transport)
        ResidueChannelCertificateLedger.empty :=
  LedgeredTraceTransport.leftIdentitySupportWitness_certificateLedger
    transport

/-- Derived composition aggregate: right-identity support witnesses carry analytic certificates. -/
theorem LedgeredTraceTransport.comp_derived_rightIdentitySupportWitness_certificateLedger
    (transport : LedgeredTraceTransport) :
    (LedgeredTraceTransport.rightIdentitySupportWitness transport).certificateLedger =
      ResidueChannelCertificateLedger.append
        (LedgeredTraceTransport.rightIdentityCertificateLedger transport)
        ResidueChannelCertificateLedger.empty :=
  LedgeredTraceTransport.rightIdentitySupportWitness_certificateLedger
    transport

end AnalyticMotives
end LFunctions
end Boundary
