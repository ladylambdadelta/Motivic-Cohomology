import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.TateStabilization.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Payload.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Payload.LedgerRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Payload.LedgerRectangles.Lengths.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Morphisms.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Morphisms.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Morphisms.Payload.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Morphisms.Payload.LedgerRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Morphisms.Payload.LedgerRectangles.Lengths.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Category.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Functors.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Functors.Forgetful.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Functors.Forgetful.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Functors.Forgetful.Payload.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Functors.Forgetful.Payload.LedgerRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Functors.Forgetful.Payload.LedgerRectangles.Lengths.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Functors.Yoneda.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Functors.Yoneda.Embedding.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Functors.Presheaf.Embedding.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Linear.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.Composition.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.Functoriality.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.Linear.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Evaluation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Evaluation.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Evaluation.Payload.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Evaluation.Payload.LedgerRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Evaluation.Payload.LedgerRectangles.Lengths.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Evaluation.Pullback.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Evaluation.Pullback.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Evaluation.Pullback.Payload.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Evaluation.Pullback.Payload.LedgerRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Evaluation.Pullback.Payload.LedgerRectangles.Lengths.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Adapters.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Adapters.Owner

/-!
# Compact geometric analytic motives

This file owns the compact/geometric subcategory of analytic motives.

The current construction packages certified trace presentations as compact
generators, equips them with representable trace presheaves and localized-word
objects, and exposes their morphisms, evaluation maps, functorial embeddings,
and certificate-ledger payload accounting.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A compact geometric analytic generator has its representable trace presheaf. -/
theorem TraceAnalyticCompactGeometric.generator_presheaf
    (generator : TraceAnalyticGeometricGenerator) :
    generator.presheaf =
      TraceCorQPresheaf.representable generator.traceObject :=
  TraceAnalyticGeometricGenerator.presheaf_eq_representable
    generator

/-- A compact geometric analytic generator has its lifted representable object. -/
theorem TraceAnalyticCompactGeometric.generator_representableObject
    (generator : TraceAnalyticGeometricGenerator) :
    generator.representableObject =
      (TraceCorQRepresentablePresheaf.yoneda).obj generator.traceObject :=
  TraceAnalyticGeometricGenerator.representableObject_eq_yoneda
    generator

/-- A compact geometric analytic generator has its localized-word object. -/
theorem TraceAnalyticCompactGeometric.generator_localizedWordObject
    (generator : TraceAnalyticGeometricGenerator) :
    generator.localizedWordObject =
      TraceLocalizedWordObject.ofTraceObject generator.traceObject :=
  TraceAnalyticGeometricGenerator.localizedWordObject_eq_ofTraceObject
    generator

/-- The compact-generator presheaf functor evaluates to the generator's presheaf. -/
theorem TraceAnalyticCompactGeometric.presheafFunctor_obj
    (generator : TraceAnalyticGeometricGenerator) :
    TraceAnalyticGeometricGenerator.presheafFunctor.obj generator =
      generator.presheaf :=
  TraceAnalyticGeometricGenerator.presheafFunctor_obj
    generator

/-- The compact-generator representable functor evaluates to the lifted representable object. -/
theorem TraceAnalyticCompactGeometric.representableObjectFunctor_obj
    (generator : TraceAnalyticGeometricGenerator) :
    TraceAnalyticGeometricGenerator.representableObjectFunctor.obj generator =
      generator.representableObject :=
  TraceAnalyticGeometricGenerator.representableObjectFunctor_obj
    generator

/-- Compact-generator evaluation is evaluation at the underlying trace object. -/
theorem TraceAnalyticCompactGeometric.evaluation_eq_traceObject
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluation =
      TraceCorQPresheaf.evaluation generator.traceObject :=
  TraceAnalyticGeometricGenerator.evaluation_eq_traceObject
    generator

/-- Compact-generator evaluation is evaluation at the forgetful functor object. -/
theorem TraceAnalyticCompactGeometric.evaluation_eq_forgetful_obj
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluation =
      TraceCorQPresheaf.evaluation
        (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj generator) :=
  TraceAnalyticGeometricGenerator.evaluation_eq_forgetful_obj
    generator

/-- Compact-generator evaluation sends a presheaf to sections over the generator. -/
theorem TraceAnalyticCompactGeometric.evaluation_obj
    (generator : TraceAnalyticGeometricGenerator)
    (presheaf : TraceCorQPresheaf) :
    generator.evaluation.obj presheaf =
      generator.sections presheaf :=
  TraceAnalyticGeometricGenerator.evaluation_obj
    generator
    presheaf

/-- Compact-generator evaluation sends a presheaf morphism to its component. -/
theorem TraceAnalyticCompactGeometric.evaluation_map
    (generator : TraceAnalyticGeometricGenerator)
    {source target : TraceCorQPresheaf}
    (morphism : source ⟶ target) :
    generator.evaluation.map morphism =
      morphism.component generator.traceObject :=
  TraceAnalyticGeometricGenerator.evaluation_map
    generator
    morphism

/-- Compact-generator sections are sections over the underlying trace object. -/
theorem TraceAnalyticCompactGeometric.sections_eq_traceObject
    (generator : TraceAnalyticGeometricGenerator)
    (presheaf : TraceCorQPresheaf) :
    generator.sections presheaf =
      presheaf.sections generator.traceObject :=
  TraceAnalyticGeometricGenerator.sections_eq_traceObject
    generator
    presheaf

/-- Sections of a compact-generator representable are trace correspondences. -/
theorem TraceAnalyticCompactGeometric.representable_sections
    (source target : TraceAnalyticGeometricGenerator) :
    source.sections target.presheaf =
      ModuleCat.of Rat (source.traceObject ⟶ target.traceObject) :=
  TraceAnalyticGeometricGenerator.representable_sections
    source
    target

/-- Evaluating the compact presheaf functor gives trace homs. -/
theorem TraceAnalyticCompactGeometric.evaluation_presheafFunctor_obj
    (source target : TraceAnalyticGeometricGenerator) :
    source.evaluation.obj
        (TraceAnalyticGeometricGenerator.presheafFunctor.obj target) =
      ModuleCat.of Rat (source.traceObject ⟶ target.traceObject) :=
  TraceAnalyticGeometricGenerator.evaluation_presheafFunctor_obj
    source
    target

/-- Compact generator imported-rectangle counts are counted by their certificate ledger. -/
theorem TraceAnalyticCompactGeometric.generator_importedRectangleCount_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.importedRectangleCount =
      generator.certificateLedger.importedRectangleCount :=
  TraceAnalyticGeometricGenerator.importedRectangleCount_eq_certificateLedger
    generator

/-- Compact generator imported-rectangle counts are the lengths of their rectangle lists. -/
theorem TraceAnalyticCompactGeometric.generator_importedRectangleCount_eq_length
    (generator : TraceAnalyticGeometricGenerator) :
    generator.importedRectangleCount =
      generator.importedRectangles.length :=
  TraceAnalyticGeometricGenerator.importedRectangleCount_eq_length_importedRectangles
    generator

end AnalyticMotives
end LFunctions
end Boundary
