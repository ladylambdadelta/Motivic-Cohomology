import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Category.Associativity.Full.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Category.Certificates.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Category.NamedCoherence.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Category.Composition.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Category.Homs.Certificates.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Category.Homs.Classes.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Category.Homs.FormalSums.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Category.Homs.Instances.Algebra.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Category.Homs.Operations.Laws.Add.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Category.Homs.Operations.Laws.Sign.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Category.Homs.Operations.Laws.Smul.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Category.Homs.Operations.Add.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Category.Homs.Operations.Sign.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Category.Homs.Operations.Smul.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Category.Homs.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Category.Homs.RelationWitnesses.Add.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Category.Homs.RelationWitnesses.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Category.Homs.RelationWitnesses.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Category.Homs.RelationWitnesses.Smul.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Category.Homs.Terms.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Category.Identity.Full.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Category.Linearity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Category.Linearity.Cancellation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Category.Linearity.Distribution.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Category.Linearity.Normalization.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Category.Linearity.ScalarDistribution.Owner

/-!
# Top-root TraceCorQ category surface

This file exposes the typed category layer for Q-linear trace correspondences
under the top-level `AnalyticMotivesRoot` namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes typed trace-correspondence homs. -/
def AnalyticMotivesRoot.traceCorQCategoryHom
    (source target : TraceCorQObject) :=
  TraceCorQCategory.hom
    source
    target

/-- The top root exposes typed-term source endpoints. -/
theorem AnalyticMotivesRoot.traceCorQHomTerm_generator_source
    {source target : TraceCorQObject}
    (term : TraceCorQHomTerm source target) :
    term.generator.source =
      source :=
  TraceCorQHoms.term_generator_source
    term

/-- The top root exposes typed-term target endpoints. -/
theorem AnalyticMotivesRoot.traceCorQHomTerm_generator_target
    {source target : TraceCorQObject}
    (term : TraceCorQHomTerm source target) :
    term.generator.target =
      target :=
  TraceCorQHoms.term_generator_target
    term

/-- The top root exposes typed-term imported-rectangle counts as list lengths. -/
theorem AnalyticMotivesRoot.traceCorQHomTerm_importedRectangleCount_eq_length
    {source target : TraceCorQObject}
    (term : TraceCorQHomTerm source target) :
    term.importedRectangleCount =
      term.importedRectangles.length :=
  TraceCorQHoms.term_importedRectangleCount_eq_length
    term

/-- The top root exposes representative certificate-ledger splitting. -/
theorem AnalyticMotivesRoot.traceCorQHomRepresentative_certificateLedger_eq
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    representative.certificateLedger =
      ResidueChannelCertificateLedger.append
        representative.formalSum.certificateLedger
        representative.ledger.certificateLedger :=
  TraceCorQHoms.representative_certificateLedger_eq
    representative

/-- The top root exposes the zero typed hom representative. -/
theorem AnalyticMotivesRoot.traceCorQHom_zero_eq_ofFormalSum_zero
    (source target : TraceCorQObject) :
    TraceCorQHom.zero source target =
      TraceCorQHom.ofFormalSum
        (TraceCorQHomFormalSum.zero source target) :=
  TraceCorQHoms.zero_eq_ofFormalSum_zero
    source
    target

/-- The top root exposes singleton typed hom representatives. -/
theorem AnalyticMotivesRoot.traceCorQHom_singleton_eq_ofFormalSum_singleton
    (source target : TraceCorQObject)
    (coefficient : Rat)
    (generator : TraceCorQGenerator)
    (source_eq : generator.source = source)
    (target_eq : generator.target = target) :
    TraceCorQHom.singleton
      source
      target
      coefficient
      generator
      source_eq
      target_eq =
      TraceCorQHom.ofFormalSum
        (TraceCorQHomFormalSum.singleton
          source
          target
          coefficient
          generator
          source_eq
          target_eq) :=
  TraceCorQHoms.singleton_eq_ofFormalSum_singleton
    source
    target
    coefficient
    generator
    source_eq
    target_eq

/-- The top root exposes the fixed-endpoint additive group structure. -/
def AnalyticMotivesRoot.traceCorQHomAddCommGroup
    {source target : TraceCorQObject} :
    AddCommGroup (TraceCorQHom source target) :=
  TraceCorQHoms.addCommGroupStructure

/-- The top root exposes the fixed-endpoint rational module structure. -/
def AnalyticMotivesRoot.traceCorQHomRatModule
    {source target : TraceCorQObject} :
    Module Rat (TraceCorQHom source target) :=
  TraceCorQHoms.ratModuleStructure

/-- The top root exposes the canonical identity representative. -/
def AnalyticMotivesRoot.traceCorQHomRepresentativeId
    (object : TraceCorQObject) :
    TraceCorQHomRepresentative object object :=
  TraceCorQHomRepresentative.id
    object

/-- The top root exposes identity representatives as typed hom classes. -/
theorem AnalyticMotivesRoot.traceCorQHom_id_eq_ofRepresentative_id
    (object : TraceCorQObject) :
    TraceCorQHom.id object =
      TraceCorQHom.ofRepresentative
        (TraceCorQHomRepresentative.id object) :=
  TraceCorQHom.id_eq_ofRepresentative_id
    object

/-- The top root exposes the ambient class of typed identities. -/
theorem AnalyticMotivesRoot.traceCorQHom_ambient_id
    (object : TraceCorQObject) :
    TraceCorQHom.ambient
      (TraceCorQHom.id object) =
      TraceCorQQuotient.singleton
        1
        (TraceCorQGenerator.id object) :=
  TraceCorQHom.ambient_id
    object

/-- The top root exposes typed hom composition on representatives. -/
theorem AnalyticMotivesRoot.traceCorQHom_comp_ofRepresentative
    {source middle target : TraceCorQObject}
    (left : TraceCorQHomRepresentative source middle)
    (right : TraceCorQHomRepresentative middle target) :
    TraceCorQHom.comp
        (TraceCorQHom.ofRepresentative left)
        (TraceCorQHom.ofRepresentative right) =
      TraceCorQHom.ofRepresentative
        (TraceCorQHomRepresentative.comp left right) :=
  TraceCorQComposition.comp_ofRepresentative
    left
    right

/-- The top root exposes left identity for typed trace correspondences. -/
theorem AnalyticMotivesRoot.traceCorQHom_left_id
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceCorQHom.comp (TraceCorQHom.id source) hom =
      hom :=
  TraceCorQCategoryLaws.left_id
    hom

/-- The top root exposes right identity for typed trace correspondences. -/
theorem AnalyticMotivesRoot.traceCorQHom_right_id
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceCorQHom.comp hom (TraceCorQHom.id target) =
      hom :=
  TraceCorQCategoryLaws.right_id
    hom

/-- The top root exposes associativity for typed trace correspondences. -/
theorem AnalyticMotivesRoot.traceCorQHom_assoc
    {first second third fourth : TraceCorQObject}
    (left : TraceCorQHom first second)
    (middle : TraceCorQHom second third)
    (right : TraceCorQHom third fourth) :
    TraceCorQHom.comp (TraceCorQHom.comp left middle) right =
      TraceCorQHom.comp left (TraceCorQHom.comp middle right) :=
  TraceCorQCategoryLaws.assoc
    left
    middle
    right

/-- The top root exposes left additivity of composition. -/
theorem AnalyticMotivesRoot.traceCorQHom_add_comp
    {source middle target : TraceCorQObject}
    (left right : TraceCorQHom source middle)
    (tail : TraceCorQHom middle target) :
    TraceCorQHom.comp (TraceCorQHom.add left right) tail =
      TraceCorQHom.add
        (TraceCorQHom.comp left tail)
        (TraceCorQHom.comp right tail) :=
  TraceCorQCategoryLaws.add_comp
    left
    right
    tail

/-- The top root exposes right additivity of composition. -/
theorem AnalyticMotivesRoot.traceCorQHom_comp_add
    {source middle target : TraceCorQObject}
    (head : TraceCorQHom source middle)
    (left right : TraceCorQHom middle target) :
    TraceCorQHom.comp head (TraceCorQHom.add left right) =
      TraceCorQHom.add
        (TraceCorQHom.comp head left)
        (TraceCorQHom.comp head right) :=
  TraceCorQCategoryLaws.comp_add
    head
    left
    right

/-- The top root exposes the category structure. -/
def AnalyticMotivesRoot.traceCorQCategoryStructure :
    CategoryTheory.Category TraceCorQObject :=
  TraceCorQCategory.categoryStructure

/-- The top root exposes the preadditive structure. -/
def AnalyticMotivesRoot.traceCorQPreadditiveStructure :
    CategoryTheory.Preadditive TraceCorQObject :=
  TraceCorQCategory.preadditiveStructure

/-- The top root exposes the rational linear structure. -/
def AnalyticMotivesRoot.traceCorQLinearRatStructure :
    CategoryTheory.Linear Rat TraceCorQObject :=
  TraceCorQCategory.linearRatStructure

end AnalyticMotives
end LFunctions
end Boundary
