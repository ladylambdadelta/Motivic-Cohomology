import TraceCalc.ClassicalPeriods.GeometricLocalization

universe u v w x y z

namespace TraceCalc
namespace ClassicalPeriods

/-- Named generator-family data for the manuscript's `Corr` row.

This records a chosen family of correspondences together with the associated geometric comparison
data and the theorem target asserting that this family realizes the correspondence-functoriality
axiom. -/
structure CorrGeneratorFamilyData
    (ctx : ClassicalComparisonContext.{u, v})
    (realization : GeometricRealizationFunctorData ctx) where
  GeneratorIndex : Type w
  sourceIndex : GeneratorIndex → realization.ObjectIndex
  targetIndex : GeneratorIndex → realization.ObjectIndex
  sourceObject : GeneratorIndex → GeometricPeriodObject ctx
  targetObject : GeneratorIndex → GeometricPeriodObject ctx
  generatorCorrespondence :
    (gen : GeneratorIndex) →
      GeometricCorrespondence (sourceObject gen) (targetObject gen)
  sourceObjectData : GeneratorIndex → GeometricComparisonObjectData ctx
  targetObjectData : GeneratorIndex → GeometricComparisonObjectData ctx
  sourceObjectCompatibilityTarget :
    ∀ gen : GeneratorIndex,
      sourceObject gen = realization.geometricObject (sourceIndex gen)
  targetObjectCompatibilityTarget :
    ∀ gen : GeneratorIndex,
      targetObject gen = realization.geometricObject (targetIndex gen)
  sourceObjectDataCompatibilityTarget :
    ∀ gen : GeneratorIndex,
      sourceObjectData gen = realization.geometricComparisonObjectData (sourceIndex gen)
  targetObjectDataCompatibilityTarget :
    ∀ gen : GeneratorIndex,
      targetObjectData gen = realization.geometricComparisonObjectData (targetIndex gen)
  theoremTarget :
    ∀ gen : GeneratorIndex,
      (generatorCorrespondence gen).correspondenceTarget ∧
        (sourceObjectData gen).comparisonData.grothendieckComparisonTarget ∧
        (targetObjectData gen).comparisonData.grothendieckComparisonTarget

namespace CorrGeneratorFamilyData

@[simp] theorem sourceObject_eq_realizationObject
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (family : CorrGeneratorFamilyData ctx realization)
    (gen : family.GeneratorIndex) :
    family.sourceObject gen = realization.geometricObject (family.sourceIndex gen) :=
  family.sourceObjectCompatibilityTarget gen

@[simp] theorem targetObject_eq_realizationObject
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (family : CorrGeneratorFamilyData ctx realization)
    (gen : family.GeneratorIndex) :
    family.targetObject gen = realization.geometricObject (family.targetIndex gen) :=
  family.targetObjectCompatibilityTarget gen

@[simp] theorem sourceObjectData_eq_realizationData
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (family : CorrGeneratorFamilyData ctx realization)
    (gen : family.GeneratorIndex) :
    family.sourceObjectData gen = realization.geometricComparisonObjectData (family.sourceIndex gen) :=
  family.sourceObjectDataCompatibilityTarget gen

@[simp] theorem targetObjectData_eq_realizationData
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (family : CorrGeneratorFamilyData ctx realization)
    (gen : family.GeneratorIndex) :
    family.targetObjectData gen = realization.geometricComparisonObjectData (family.targetIndex gen) :=
  family.targetObjectDataCompatibilityTarget gen

theorem correspondenceTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (family : CorrGeneratorFamilyData ctx realization)
    (gen : family.GeneratorIndex) :
    (family.generatorCorrespondence gen).correspondenceTarget :=
  (family.theoremTarget gen).1

theorem sourceGrothendieckComparisonTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (family : CorrGeneratorFamilyData ctx realization)
    (gen : family.GeneratorIndex) :
    (family.sourceObjectData gen).comparisonData.grothendieckComparisonTarget :=
  (family.theoremTarget gen).2.1

theorem targetGrothendieckComparisonTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (family : CorrGeneratorFamilyData ctx realization)
    (gen : family.GeneratorIndex) :
    (family.targetObjectData gen).comparisonData.grothendieckComparisonTarget :=
  (family.theoremTarget gen).2.2

end CorrGeneratorFamilyData

/-- Named generator-family data for the manuscript's `Loc` row. -/
structure LocGeneratorFamilyData
    (ctx : ClassicalComparisonContext.{u, v})
    (realization : GeometricRealizationFunctorData ctx) where
  GeneratorIndex : Type w
  ambientIndex : GeneratorIndex → realization.ObjectIndex
  openIndex : GeneratorIndex → realization.ObjectIndex
  closedIndex : GeneratorIndex → realization.ObjectIndex
  ambientObject : GeneratorIndex → GeometricPeriodObject ctx
  openObject : GeneratorIndex → GeometricPeriodObject ctx
  closedObject : GeneratorIndex → GeometricPeriodObject ctx
  ambientData : GeneratorIndex → GeometricComparisonObjectData ctx
  openData : GeneratorIndex → GeometricComparisonObjectData ctx
  closedData : GeneratorIndex → GeometricComparisonObjectData ctx
  ambientObjectCompatibilityTarget :
    ∀ gen : GeneratorIndex,
      ambientObject gen = realization.geometricObject (ambientIndex gen)
  openObjectCompatibilityTarget :
    ∀ gen : GeneratorIndex,
      openObject gen = realization.geometricObject (openIndex gen)
  closedObjectCompatibilityTarget :
    ∀ gen : GeneratorIndex,
      closedObject gen = realization.geometricObject (closedIndex gen)
  ambientDataCompatibilityTarget :
    ∀ gen : GeneratorIndex,
      ambientData gen = realization.geometricComparisonObjectData (ambientIndex gen)
  openDataCompatibilityTarget :
    ∀ gen : GeneratorIndex,
      openData gen = realization.geometricComparisonObjectData (openIndex gen)
  closedDataCompatibilityTarget :
    ∀ gen : GeneratorIndex,
      closedData gen = realization.geometricComparisonObjectData (closedIndex gen)
  theoremTarget :
    ∀ gen : GeneratorIndex,
      (ambientData gen).comparisonData.periodCompatibilityTarget ∧
        (openData gen).comparisonData.periodCompatibilityTarget ∧
        (closedData gen).comparisonData.periodCompatibilityTarget

namespace LocGeneratorFamilyData

@[simp] theorem ambientObject_eq_realizationObject
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (family : LocGeneratorFamilyData ctx realization)
    (gen : family.GeneratorIndex) :
    family.ambientObject gen = realization.geometricObject (family.ambientIndex gen) :=
  family.ambientObjectCompatibilityTarget gen

@[simp] theorem openObject_eq_realizationObject
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (family : LocGeneratorFamilyData ctx realization)
    (gen : family.GeneratorIndex) :
    family.openObject gen = realization.geometricObject (family.openIndex gen) :=
  family.openObjectCompatibilityTarget gen

@[simp] theorem closedObject_eq_realizationObject
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (family : LocGeneratorFamilyData ctx realization)
    (gen : family.GeneratorIndex) :
    family.closedObject gen = realization.geometricObject (family.closedIndex gen) :=
  family.closedObjectCompatibilityTarget gen

@[simp] theorem ambientData_eq_realizationData
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (family : LocGeneratorFamilyData ctx realization)
    (gen : family.GeneratorIndex) :
    family.ambientData gen = realization.geometricComparisonObjectData (family.ambientIndex gen) :=
  family.ambientDataCompatibilityTarget gen

@[simp] theorem openData_eq_realizationData
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (family : LocGeneratorFamilyData ctx realization)
    (gen : family.GeneratorIndex) :
    family.openData gen = realization.geometricComparisonObjectData (family.openIndex gen) :=
  family.openDataCompatibilityTarget gen

@[simp] theorem closedData_eq_realizationData
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (family : LocGeneratorFamilyData ctx realization)
    (gen : family.GeneratorIndex) :
    family.closedData gen = realization.geometricComparisonObjectData (family.closedIndex gen) :=
  family.closedDataCompatibilityTarget gen

theorem ambientPeriodCompatibilityTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (family : LocGeneratorFamilyData ctx realization)
    (gen : family.GeneratorIndex) :
    (family.ambientData gen).comparisonData.periodCompatibilityTarget :=
  (family.theoremTarget gen).1

theorem openPeriodCompatibilityTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (family : LocGeneratorFamilyData ctx realization)
    (gen : family.GeneratorIndex) :
    (family.openData gen).comparisonData.periodCompatibilityTarget :=
  (family.theoremTarget gen).2.1

theorem closedPeriodCompatibilityTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (family : LocGeneratorFamilyData ctx realization)
    (gen : family.GeneratorIndex) :
    (family.closedData gen).comparisonData.periodCompatibilityTarget :=
  (family.theoremTarget gen).2.2

end LocGeneratorFamilyData

/-- Named generator-family data for the manuscript's `Nis` row. -/
structure NisGeneratorFamilyData
    (ctx : ClassicalComparisonContext.{u, v})
    (realization : GeometricRealizationFunctorData ctx) where
  GeneratorIndex : Type w
  baseIndex : GeneratorIndex → realization.ObjectIndex
  patchIndex : GeneratorIndex → realization.ObjectIndex
  overlapIndex : GeneratorIndex → realization.ObjectIndex
  baseObject : GeneratorIndex → GeometricPeriodObject ctx
  patchObject : GeneratorIndex → GeometricPeriodObject ctx
  overlapObject : GeneratorIndex → GeometricPeriodObject ctx
  baseData : GeneratorIndex → GeometricComparisonObjectData ctx
  patchData : GeneratorIndex → GeometricComparisonObjectData ctx
  overlapData : GeneratorIndex → GeometricComparisonObjectData ctx
  baseObjectCompatibilityTarget :
    ∀ gen : GeneratorIndex,
      baseObject gen = realization.geometricObject (baseIndex gen)
  patchObjectCompatibilityTarget :
    ∀ gen : GeneratorIndex,
      patchObject gen = realization.geometricObject (patchIndex gen)
  overlapObjectCompatibilityTarget :
    ∀ gen : GeneratorIndex,
      overlapObject gen = realization.geometricObject (overlapIndex gen)
  baseDataCompatibilityTarget :
    ∀ gen : GeneratorIndex,
      baseData gen = realization.geometricComparisonObjectData (baseIndex gen)
  patchDataCompatibilityTarget :
    ∀ gen : GeneratorIndex,
      patchData gen = realization.geometricComparisonObjectData (patchIndex gen)
  overlapDataCompatibilityTarget :
    ∀ gen : GeneratorIndex,
      overlapData gen = realization.geometricComparisonObjectData (overlapIndex gen)
  theoremTarget :
    ∀ gen : GeneratorIndex,
      (baseData gen).comparisonData.grothendieckComparisonTarget ∧
        (patchData gen).comparisonData.grothendieckComparisonTarget ∧
        (overlapData gen).comparisonData.grothendieckComparisonTarget

namespace NisGeneratorFamilyData

@[simp] theorem baseObject_eq_realizationObject
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (family : NisGeneratorFamilyData ctx realization)
    (gen : family.GeneratorIndex) :
    family.baseObject gen = realization.geometricObject (family.baseIndex gen) :=
  family.baseObjectCompatibilityTarget gen

@[simp] theorem patchObject_eq_realizationObject
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (family : NisGeneratorFamilyData ctx realization)
    (gen : family.GeneratorIndex) :
    family.patchObject gen = realization.geometricObject (family.patchIndex gen) :=
  family.patchObjectCompatibilityTarget gen

@[simp] theorem overlapObject_eq_realizationObject
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (family : NisGeneratorFamilyData ctx realization)
    (gen : family.GeneratorIndex) :
    family.overlapObject gen = realization.geometricObject (family.overlapIndex gen) :=
  family.overlapObjectCompatibilityTarget gen

@[simp] theorem baseData_eq_realizationData
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (family : NisGeneratorFamilyData ctx realization)
    (gen : family.GeneratorIndex) :
    family.baseData gen = realization.geometricComparisonObjectData (family.baseIndex gen) :=
  family.baseDataCompatibilityTarget gen

@[simp] theorem patchData_eq_realizationData
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (family : NisGeneratorFamilyData ctx realization)
    (gen : family.GeneratorIndex) :
    family.patchData gen = realization.geometricComparisonObjectData (family.patchIndex gen) :=
  family.patchDataCompatibilityTarget gen

@[simp] theorem overlapData_eq_realizationData
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (family : NisGeneratorFamilyData ctx realization)
    (gen : family.GeneratorIndex) :
    family.overlapData gen = realization.geometricComparisonObjectData (family.overlapIndex gen) :=
  family.overlapDataCompatibilityTarget gen

theorem baseGrothendieckComparisonTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (family : NisGeneratorFamilyData ctx realization)
    (gen : family.GeneratorIndex) :
    (family.baseData gen).comparisonData.grothendieckComparisonTarget :=
  (family.theoremTarget gen).1

theorem patchGrothendieckComparisonTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (family : NisGeneratorFamilyData ctx realization)
    (gen : family.GeneratorIndex) :
    (family.patchData gen).comparisonData.grothendieckComparisonTarget :=
  (family.theoremTarget gen).2.1

theorem overlapGrothendieckComparisonTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (family : NisGeneratorFamilyData ctx realization)
    (gen : family.GeneratorIndex) :
    (family.overlapData gen).comparisonData.grothendieckComparisonTarget :=
  (family.theoremTarget gen).2.2

end NisGeneratorFamilyData

/-- Named generator-family data for the manuscript's `A1` row. -/
structure A1GeneratorFamilyData
    (ctx : ClassicalComparisonContext.{u, v})
    (realization : GeometricRealizationFunctorData ctx) where
  GeneratorIndex : Type w
  baseIndex : GeneratorIndex → realization.ObjectIndex
  cylinderIndex : GeneratorIndex → realization.ObjectIndex
  baseObject : GeneratorIndex → GeometricPeriodObject ctx
  cylinderObject : GeneratorIndex → GeometricPeriodObject ctx
  baseData : GeneratorIndex → GeometricComparisonObjectData ctx
  cylinderData : GeneratorIndex → GeometricComparisonObjectData ctx
  baseObjectCompatibilityTarget :
    ∀ gen : GeneratorIndex,
      baseObject gen = realization.geometricObject (baseIndex gen)
  cylinderObjectCompatibilityTarget :
    ∀ gen : GeneratorIndex,
      cylinderObject gen = realization.geometricObject (cylinderIndex gen)
  baseDataCompatibilityTarget :
    ∀ gen : GeneratorIndex,
      baseData gen = realization.geometricComparisonObjectData (baseIndex gen)
  cylinderDataCompatibilityTarget :
    ∀ gen : GeneratorIndex,
      cylinderData gen = realization.geometricComparisonObjectData (cylinderIndex gen)
  theoremTarget :
    ∀ gen : GeneratorIndex,
      (baseData gen).comparisonData.grothendieckComparisonTarget ∧
        (cylinderData gen).comparisonData.grothendieckComparisonTarget ∧
        (baseData gen).comparisonData.periodCompatibilityTarget ∧
        (cylinderData gen).comparisonData.periodCompatibilityTarget

namespace A1GeneratorFamilyData

@[simp] theorem baseObject_eq_realizationObject
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (family : A1GeneratorFamilyData ctx realization)
    (gen : family.GeneratorIndex) :
    family.baseObject gen = realization.geometricObject (family.baseIndex gen) :=
  family.baseObjectCompatibilityTarget gen

@[simp] theorem cylinderObject_eq_realizationObject
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (family : A1GeneratorFamilyData ctx realization)
    (gen : family.GeneratorIndex) :
    family.cylinderObject gen = realization.geometricObject (family.cylinderIndex gen) :=
  family.cylinderObjectCompatibilityTarget gen

@[simp] theorem baseData_eq_realizationData
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (family : A1GeneratorFamilyData ctx realization)
    (gen : family.GeneratorIndex) :
    family.baseData gen = realization.geometricComparisonObjectData (family.baseIndex gen) :=
  family.baseDataCompatibilityTarget gen

@[simp] theorem cylinderData_eq_realizationData
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (family : A1GeneratorFamilyData ctx realization)
    (gen : family.GeneratorIndex) :
    family.cylinderData gen = realization.geometricComparisonObjectData (family.cylinderIndex gen) :=
  family.cylinderDataCompatibilityTarget gen

theorem baseGrothendieckComparisonTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (family : A1GeneratorFamilyData ctx realization)
    (gen : family.GeneratorIndex) :
    (family.baseData gen).comparisonData.grothendieckComparisonTarget :=
  (family.theoremTarget gen).1

theorem cylinderGrothendieckComparisonTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (family : A1GeneratorFamilyData ctx realization)
    (gen : family.GeneratorIndex) :
    (family.cylinderData gen).comparisonData.grothendieckComparisonTarget :=
  (family.theoremTarget gen).2.1

theorem basePeriodCompatibilityTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (family : A1GeneratorFamilyData ctx realization)
    (gen : family.GeneratorIndex) :
    (family.baseData gen).comparisonData.periodCompatibilityTarget :=
  (family.theoremTarget gen).2.2.1

theorem cylinderPeriodCompatibilityTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (family : A1GeneratorFamilyData ctx realization)
    (gen : family.GeneratorIndex) :
    (family.cylinderData gen).comparisonData.periodCompatibilityTarget :=
  (family.theoremTarget gen).2.2.2

end A1GeneratorFamilyData

/-- Named generator-family data for the manuscript's `Env` row. -/
structure EnvGeneratorFamilyData
    (ctx : ClassicalComparisonContext.{u, v})
    (realization : GeometricRealizationFunctorData ctx) where
  GeneratorIndex : Type w
  ambientIndex : GeneratorIndex → realization.ObjectIndex
  envelopeIndex : GeneratorIndex → realization.ObjectIndex
  ambientObject : GeneratorIndex → GeometricPeriodObject ctx
  envelopeObject : GeneratorIndex → GeometricPeriodObject ctx
  envelopeCorrespondence :
    (gen : GeneratorIndex) →
      GeometricCorrespondence (envelopeObject gen) (ambientObject gen)
  ambientData : GeneratorIndex → GeometricComparisonObjectData ctx
  envelopeData : GeneratorIndex → GeometricComparisonObjectData ctx
  ambientObjectCompatibilityTarget :
    ∀ gen : GeneratorIndex,
      ambientObject gen = realization.geometricObject (ambientIndex gen)
  envelopeObjectCompatibilityTarget :
    ∀ gen : GeneratorIndex,
      envelopeObject gen = realization.geometricObject (envelopeIndex gen)
  ambientDataCompatibilityTarget :
    ∀ gen : GeneratorIndex,
      ambientData gen = realization.geometricComparisonObjectData (ambientIndex gen)
  envelopeDataCompatibilityTarget :
    ∀ gen : GeneratorIndex,
      envelopeData gen = realization.geometricComparisonObjectData (envelopeIndex gen)
  theoremTarget :
    ∀ gen : GeneratorIndex,
      (envelopeCorrespondence gen).correspondenceTarget ∧
        (ambientData gen).comparisonData.grothendieckComparisonTarget ∧
        (envelopeData gen).comparisonData.grothendieckComparisonTarget ∧
        (ambientData gen).comparisonData.periodCompatibilityTarget ∧
        (envelopeData gen).comparisonData.periodCompatibilityTarget

namespace EnvGeneratorFamilyData

@[simp] theorem ambientObject_eq_realizationObject
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (family : EnvGeneratorFamilyData ctx realization)
    (gen : family.GeneratorIndex) :
    family.ambientObject gen = realization.geometricObject (family.ambientIndex gen) :=
  family.ambientObjectCompatibilityTarget gen

@[simp] theorem envelopeObject_eq_realizationObject
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (family : EnvGeneratorFamilyData ctx realization)
    (gen : family.GeneratorIndex) :
    family.envelopeObject gen = realization.geometricObject (family.envelopeIndex gen) :=
  family.envelopeObjectCompatibilityTarget gen

@[simp] theorem ambientData_eq_realizationData
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (family : EnvGeneratorFamilyData ctx realization)
    (gen : family.GeneratorIndex) :
    family.ambientData gen = realization.geometricComparisonObjectData (family.ambientIndex gen) :=
  family.ambientDataCompatibilityTarget gen

@[simp] theorem envelopeData_eq_realizationData
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (family : EnvGeneratorFamilyData ctx realization)
    (gen : family.GeneratorIndex) :
    family.envelopeData gen = realization.geometricComparisonObjectData (family.envelopeIndex gen) :=
  family.envelopeDataCompatibilityTarget gen

theorem envelopeCorrespondenceTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (family : EnvGeneratorFamilyData ctx realization)
    (gen : family.GeneratorIndex) :
    (family.envelopeCorrespondence gen).correspondenceTarget :=
  (family.theoremTarget gen).1

theorem ambientGrothendieckComparisonTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (family : EnvGeneratorFamilyData ctx realization)
    (gen : family.GeneratorIndex) :
    (family.ambientData gen).comparisonData.grothendieckComparisonTarget :=
  (family.theoremTarget gen).2.1

theorem envelopeGrothendieckComparisonTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (family : EnvGeneratorFamilyData ctx realization)
    (gen : family.GeneratorIndex) :
    (family.envelopeData gen).comparisonData.grothendieckComparisonTarget :=
  (family.theoremTarget gen).2.2.1

theorem ambientPeriodCompatibilityTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (family : EnvGeneratorFamilyData ctx realization)
    (gen : family.GeneratorIndex) :
    (family.ambientData gen).comparisonData.periodCompatibilityTarget :=
  (family.theoremTarget gen).2.2.2.1

theorem envelopePeriodCompatibilityTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (family : EnvGeneratorFamilyData ctx realization)
    (gen : family.GeneratorIndex) :
    (family.envelopeData gen).comparisonData.periodCompatibilityTarget :=
  (family.theoremTarget gen).2.2.2.2

end EnvGeneratorFamilyData

/-- Named generator-family package for the manuscript's `Corr / Loc / Nis / A1 / Env` rows.

This is the interface layer immediately above the localization/descent package: it records the
named families themselves, together with the corresponding theorem targets that package those
families into the existing localization layer. -/
structure GeometricGeneratorFamilyPackage
    (ctx : ClassicalComparisonContext.{u, v}) where
  realization : GeometricRealizationFunctorData ctx
  corrFamily : CorrGeneratorFamilyData ctx realization
  locFamily : LocGeneratorFamilyData ctx realization
  nisFamily : NisGeneratorFamilyData ctx realization
  a1Family : A1GeneratorFamilyData ctx realization
  envFamily : EnvGeneratorFamilyData ctx realization
  corrTarget : GeometricCorrespondenceFunctorialityTarget ctx realization
  locTarget : GeometricOpenClosedLocalizationTarget ctx realization
  nisTarget : GeometricNisnevichDescentTarget ctx realization
  a1Target : GeometricA1InvarianceTarget ctx realization
  envTarget : GeometricEnvelopeExactnessTarget ctx realization
  tateTarget : GeometricTateStabilizationTarget ctx realization
  generatorCoverageTarget : Prop
  realizationCompatibilityTarget : Prop
  motivicRecognitionInterfaceTarget : Prop

namespace GeometricGeneratorFamilyPackage

/-- Constructor for the named generator-family package. -/
def ofRows
    {ctx : ClassicalComparisonContext.{u, v}}
    (realization : GeometricRealizationFunctorData ctx)
    (corrFamily : CorrGeneratorFamilyData ctx realization)
    (locFamily : LocGeneratorFamilyData ctx realization)
    (nisFamily : NisGeneratorFamilyData ctx realization)
    (a1Family : A1GeneratorFamilyData ctx realization)
    (envFamily : EnvGeneratorFamilyData ctx realization)
    (corrTarget : GeometricCorrespondenceFunctorialityTarget ctx realization)
    (locTarget : GeometricOpenClosedLocalizationTarget ctx realization)
    (nisTarget : GeometricNisnevichDescentTarget ctx realization)
    (a1Target : GeometricA1InvarianceTarget ctx realization)
    (envTarget : GeometricEnvelopeExactnessTarget ctx realization)
    (tateTarget : GeometricTateStabilizationTarget ctx realization)
    (generatorCoverageTarget realizationCompatibilityTarget
      motivicRecognitionInterfaceTarget : Prop) :
    GeometricGeneratorFamilyPackage ctx where
  realization := realization
  corrFamily := corrFamily
  locFamily := locFamily
  nisFamily := nisFamily
  a1Family := a1Family
  envFamily := envFamily
  corrTarget := corrTarget
  locTarget := locTarget
  nisTarget := nisTarget
  a1Target := a1Target
  envTarget := envTarget
  tateTarget := tateTarget
  generatorCoverageTarget := generatorCoverageTarget
  realizationCompatibilityTarget := realizationCompatibilityTarget
  motivicRecognitionInterfaceTarget := motivicRecognitionInterfaceTarget

@[simp] theorem ofRows_realization
    {ctx : ClassicalComparisonContext.{u, v}}
    (realization : GeometricRealizationFunctorData ctx)
    (corrFamily : CorrGeneratorFamilyData ctx realization)
    (locFamily : LocGeneratorFamilyData ctx realization)
    (nisFamily : NisGeneratorFamilyData ctx realization)
    (a1Family : A1GeneratorFamilyData ctx realization)
    (envFamily : EnvGeneratorFamilyData ctx realization)
    (corrTarget : GeometricCorrespondenceFunctorialityTarget ctx realization)
    (locTarget : GeometricOpenClosedLocalizationTarget ctx realization)
    (nisTarget : GeometricNisnevichDescentTarget ctx realization)
    (a1Target : GeometricA1InvarianceTarget ctx realization)
    (envTarget : GeometricEnvelopeExactnessTarget ctx realization)
    (tateTarget : GeometricTateStabilizationTarget ctx realization)
    (generatorCoverageTarget realizationCompatibilityTarget
      motivicRecognitionInterfaceTarget : Prop) :
    (ofRows realization corrFamily locFamily nisFamily a1Family envFamily corrTarget locTarget
      nisTarget a1Target envTarget tateTarget generatorCoverageTarget realizationCompatibilityTarget
      motivicRecognitionInterfaceTarget).realization = realization := by
  rfl

@[simp] theorem ofRows_corrFamily
    {ctx : ClassicalComparisonContext.{u, v}}
    (realization : GeometricRealizationFunctorData ctx)
    (corrFamily : CorrGeneratorFamilyData ctx realization)
    (locFamily : LocGeneratorFamilyData ctx realization)
    (nisFamily : NisGeneratorFamilyData ctx realization)
    (a1Family : A1GeneratorFamilyData ctx realization)
    (envFamily : EnvGeneratorFamilyData ctx realization)
    (corrTarget : GeometricCorrespondenceFunctorialityTarget ctx realization)
    (locTarget : GeometricOpenClosedLocalizationTarget ctx realization)
    (nisTarget : GeometricNisnevichDescentTarget ctx realization)
    (a1Target : GeometricA1InvarianceTarget ctx realization)
    (envTarget : GeometricEnvelopeExactnessTarget ctx realization)
    (tateTarget : GeometricTateStabilizationTarget ctx realization)
    (generatorCoverageTarget realizationCompatibilityTarget
      motivicRecognitionInterfaceTarget : Prop) :
    (ofRows realization corrFamily locFamily nisFamily a1Family envFamily corrTarget locTarget
      nisTarget a1Target envTarget tateTarget generatorCoverageTarget realizationCompatibilityTarget
      motivicRecognitionInterfaceTarget).corrFamily = corrFamily := by
  rfl

@[simp] theorem ofRows_locFamily
    {ctx : ClassicalComparisonContext.{u, v}}
    (realization : GeometricRealizationFunctorData ctx)
    (corrFamily : CorrGeneratorFamilyData ctx realization)
    (locFamily : LocGeneratorFamilyData ctx realization)
    (nisFamily : NisGeneratorFamilyData ctx realization)
    (a1Family : A1GeneratorFamilyData ctx realization)
    (envFamily : EnvGeneratorFamilyData ctx realization)
    (corrTarget : GeometricCorrespondenceFunctorialityTarget ctx realization)
    (locTarget : GeometricOpenClosedLocalizationTarget ctx realization)
    (nisTarget : GeometricNisnevichDescentTarget ctx realization)
    (a1Target : GeometricA1InvarianceTarget ctx realization)
    (envTarget : GeometricEnvelopeExactnessTarget ctx realization)
    (tateTarget : GeometricTateStabilizationTarget ctx realization)
    (generatorCoverageTarget realizationCompatibilityTarget
      motivicRecognitionInterfaceTarget : Prop) :
    (ofRows realization corrFamily locFamily nisFamily a1Family envFamily corrTarget locTarget
      nisTarget a1Target envTarget tateTarget generatorCoverageTarget realizationCompatibilityTarget
      motivicRecognitionInterfaceTarget).locFamily = locFamily := by
  rfl

@[simp] theorem ofRows_nisFamily
    {ctx : ClassicalComparisonContext.{u, v}}
    (realization : GeometricRealizationFunctorData ctx)
    (corrFamily : CorrGeneratorFamilyData ctx realization)
    (locFamily : LocGeneratorFamilyData ctx realization)
    (nisFamily : NisGeneratorFamilyData ctx realization)
    (a1Family : A1GeneratorFamilyData ctx realization)
    (envFamily : EnvGeneratorFamilyData ctx realization)
    (corrTarget : GeometricCorrespondenceFunctorialityTarget ctx realization)
    (locTarget : GeometricOpenClosedLocalizationTarget ctx realization)
    (nisTarget : GeometricNisnevichDescentTarget ctx realization)
    (a1Target : GeometricA1InvarianceTarget ctx realization)
    (envTarget : GeometricEnvelopeExactnessTarget ctx realization)
    (tateTarget : GeometricTateStabilizationTarget ctx realization)
    (generatorCoverageTarget realizationCompatibilityTarget
      motivicRecognitionInterfaceTarget : Prop) :
    (ofRows realization corrFamily locFamily nisFamily a1Family envFamily corrTarget locTarget
      nisTarget a1Target envTarget tateTarget generatorCoverageTarget realizationCompatibilityTarget
      motivicRecognitionInterfaceTarget).nisFamily = nisFamily := by
  rfl

@[simp] theorem ofRows_a1Family
    {ctx : ClassicalComparisonContext.{u, v}}
    (realization : GeometricRealizationFunctorData ctx)
    (corrFamily : CorrGeneratorFamilyData ctx realization)
    (locFamily : LocGeneratorFamilyData ctx realization)
    (nisFamily : NisGeneratorFamilyData ctx realization)
    (a1Family : A1GeneratorFamilyData ctx realization)
    (envFamily : EnvGeneratorFamilyData ctx realization)
    (corrTarget : GeometricCorrespondenceFunctorialityTarget ctx realization)
    (locTarget : GeometricOpenClosedLocalizationTarget ctx realization)
    (nisTarget : GeometricNisnevichDescentTarget ctx realization)
    (a1Target : GeometricA1InvarianceTarget ctx realization)
    (envTarget : GeometricEnvelopeExactnessTarget ctx realization)
    (tateTarget : GeometricTateStabilizationTarget ctx realization)
    (generatorCoverageTarget realizationCompatibilityTarget
      motivicRecognitionInterfaceTarget : Prop) :
    (ofRows realization corrFamily locFamily nisFamily a1Family envFamily corrTarget locTarget
      nisTarget a1Target envTarget tateTarget generatorCoverageTarget realizationCompatibilityTarget
      motivicRecognitionInterfaceTarget).a1Family = a1Family := by
  rfl

@[simp] theorem ofRows_envFamily
    {ctx : ClassicalComparisonContext.{u, v}}
    (realization : GeometricRealizationFunctorData ctx)
    (corrFamily : CorrGeneratorFamilyData ctx realization)
    (locFamily : LocGeneratorFamilyData ctx realization)
    (nisFamily : NisGeneratorFamilyData ctx realization)
    (a1Family : A1GeneratorFamilyData ctx realization)
    (envFamily : EnvGeneratorFamilyData ctx realization)
    (corrTarget : GeometricCorrespondenceFunctorialityTarget ctx realization)
    (locTarget : GeometricOpenClosedLocalizationTarget ctx realization)
    (nisTarget : GeometricNisnevichDescentTarget ctx realization)
    (a1Target : GeometricA1InvarianceTarget ctx realization)
    (envTarget : GeometricEnvelopeExactnessTarget ctx realization)
    (tateTarget : GeometricTateStabilizationTarget ctx realization)
    (generatorCoverageTarget realizationCompatibilityTarget
      motivicRecognitionInterfaceTarget : Prop) :
    (ofRows realization corrFamily locFamily nisFamily a1Family envFamily corrTarget locTarget
      nisTarget a1Target envTarget tateTarget generatorCoverageTarget realizationCompatibilityTarget
      motivicRecognitionInterfaceTarget).envFamily = envFamily := by
  rfl

@[simp] theorem ofRows_corrTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (realization : GeometricRealizationFunctorData ctx)
    (corrFamily : CorrGeneratorFamilyData ctx realization)
    (locFamily : LocGeneratorFamilyData ctx realization)
    (nisFamily : NisGeneratorFamilyData ctx realization)
    (a1Family : A1GeneratorFamilyData ctx realization)
    (envFamily : EnvGeneratorFamilyData ctx realization)
    (corrTarget : GeometricCorrespondenceFunctorialityTarget ctx realization)
    (locTarget : GeometricOpenClosedLocalizationTarget ctx realization)
    (nisTarget : GeometricNisnevichDescentTarget ctx realization)
    (a1Target : GeometricA1InvarianceTarget ctx realization)
    (envTarget : GeometricEnvelopeExactnessTarget ctx realization)
    (tateTarget : GeometricTateStabilizationTarget ctx realization)
    (generatorCoverageTarget realizationCompatibilityTarget
      motivicRecognitionInterfaceTarget : Prop) :
    (ofRows realization corrFamily locFamily nisFamily a1Family envFamily corrTarget locTarget
      nisTarget a1Target envTarget tateTarget generatorCoverageTarget realizationCompatibilityTarget
      motivicRecognitionInterfaceTarget).corrTarget = corrTarget := by
  rfl

@[simp] theorem ofRows_locTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (realization : GeometricRealizationFunctorData ctx)
    (corrFamily : CorrGeneratorFamilyData ctx realization)
    (locFamily : LocGeneratorFamilyData ctx realization)
    (nisFamily : NisGeneratorFamilyData ctx realization)
    (a1Family : A1GeneratorFamilyData ctx realization)
    (envFamily : EnvGeneratorFamilyData ctx realization)
    (corrTarget : GeometricCorrespondenceFunctorialityTarget ctx realization)
    (locTarget : GeometricOpenClosedLocalizationTarget ctx realization)
    (nisTarget : GeometricNisnevichDescentTarget ctx realization)
    (a1Target : GeometricA1InvarianceTarget ctx realization)
    (envTarget : GeometricEnvelopeExactnessTarget ctx realization)
    (tateTarget : GeometricTateStabilizationTarget ctx realization)
    (generatorCoverageTarget realizationCompatibilityTarget
      motivicRecognitionInterfaceTarget : Prop) :
    (ofRows realization corrFamily locFamily nisFamily a1Family envFamily corrTarget locTarget
      nisTarget a1Target envTarget tateTarget generatorCoverageTarget realizationCompatibilityTarget
      motivicRecognitionInterfaceTarget).locTarget = locTarget := by
  rfl

@[simp] theorem ofRows_nisTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (realization : GeometricRealizationFunctorData ctx)
    (corrFamily : CorrGeneratorFamilyData ctx realization)
    (locFamily : LocGeneratorFamilyData ctx realization)
    (nisFamily : NisGeneratorFamilyData ctx realization)
    (a1Family : A1GeneratorFamilyData ctx realization)
    (envFamily : EnvGeneratorFamilyData ctx realization)
    (corrTarget : GeometricCorrespondenceFunctorialityTarget ctx realization)
    (locTarget : GeometricOpenClosedLocalizationTarget ctx realization)
    (nisTarget : GeometricNisnevichDescentTarget ctx realization)
    (a1Target : GeometricA1InvarianceTarget ctx realization)
    (envTarget : GeometricEnvelopeExactnessTarget ctx realization)
    (tateTarget : GeometricTateStabilizationTarget ctx realization)
    (generatorCoverageTarget realizationCompatibilityTarget
      motivicRecognitionInterfaceTarget : Prop) :
    (ofRows realization corrFamily locFamily nisFamily a1Family envFamily corrTarget locTarget
      nisTarget a1Target envTarget tateTarget generatorCoverageTarget realizationCompatibilityTarget
      motivicRecognitionInterfaceTarget).nisTarget = nisTarget := by
  rfl

@[simp] theorem ofRows_a1Target
    {ctx : ClassicalComparisonContext.{u, v}}
    (realization : GeometricRealizationFunctorData ctx)
    (corrFamily : CorrGeneratorFamilyData ctx realization)
    (locFamily : LocGeneratorFamilyData ctx realization)
    (nisFamily : NisGeneratorFamilyData ctx realization)
    (a1Family : A1GeneratorFamilyData ctx realization)
    (envFamily : EnvGeneratorFamilyData ctx realization)
    (corrTarget : GeometricCorrespondenceFunctorialityTarget ctx realization)
    (locTarget : GeometricOpenClosedLocalizationTarget ctx realization)
    (nisTarget : GeometricNisnevichDescentTarget ctx realization)
    (a1Target : GeometricA1InvarianceTarget ctx realization)
    (envTarget : GeometricEnvelopeExactnessTarget ctx realization)
    (tateTarget : GeometricTateStabilizationTarget ctx realization)
    (generatorCoverageTarget realizationCompatibilityTarget
      motivicRecognitionInterfaceTarget : Prop) :
    (ofRows realization corrFamily locFamily nisFamily a1Family envFamily corrTarget locTarget
      nisTarget a1Target envTarget tateTarget generatorCoverageTarget realizationCompatibilityTarget
      motivicRecognitionInterfaceTarget).a1Target = a1Target := by
  rfl

@[simp] theorem ofRows_envTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (realization : GeometricRealizationFunctorData ctx)
    (corrFamily : CorrGeneratorFamilyData ctx realization)
    (locFamily : LocGeneratorFamilyData ctx realization)
    (nisFamily : NisGeneratorFamilyData ctx realization)
    (a1Family : A1GeneratorFamilyData ctx realization)
    (envFamily : EnvGeneratorFamilyData ctx realization)
    (corrTarget : GeometricCorrespondenceFunctorialityTarget ctx realization)
    (locTarget : GeometricOpenClosedLocalizationTarget ctx realization)
    (nisTarget : GeometricNisnevichDescentTarget ctx realization)
    (a1Target : GeometricA1InvarianceTarget ctx realization)
    (envTarget : GeometricEnvelopeExactnessTarget ctx realization)
    (tateTarget : GeometricTateStabilizationTarget ctx realization)
    (generatorCoverageTarget realizationCompatibilityTarget
      motivicRecognitionInterfaceTarget : Prop) :
    (ofRows realization corrFamily locFamily nisFamily a1Family envFamily corrTarget locTarget
      nisTarget a1Target envTarget tateTarget generatorCoverageTarget realizationCompatibilityTarget
      motivicRecognitionInterfaceTarget).envTarget = envTarget := by
  rfl

@[simp] theorem ofRows_generatorCoverageTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (realization : GeometricRealizationFunctorData ctx)
    (corrFamily : CorrGeneratorFamilyData ctx realization)
    (locFamily : LocGeneratorFamilyData ctx realization)
    (nisFamily : NisGeneratorFamilyData ctx realization)
    (a1Family : A1GeneratorFamilyData ctx realization)
    (envFamily : EnvGeneratorFamilyData ctx realization)
    (corrTarget : GeometricCorrespondenceFunctorialityTarget ctx realization)
    (locTarget : GeometricOpenClosedLocalizationTarget ctx realization)
    (nisTarget : GeometricNisnevichDescentTarget ctx realization)
    (a1Target : GeometricA1InvarianceTarget ctx realization)
    (envTarget : GeometricEnvelopeExactnessTarget ctx realization)
    (tateTarget : GeometricTateStabilizationTarget ctx realization)
    (generatorCoverageTarget realizationCompatibilityTarget
      motivicRecognitionInterfaceTarget : Prop) :
    (ofRows realization corrFamily locFamily nisFamily a1Family envFamily corrTarget locTarget
      nisTarget a1Target envTarget tateTarget generatorCoverageTarget realizationCompatibilityTarget
      motivicRecognitionInterfaceTarget).generatorCoverageTarget = generatorCoverageTarget := by
  rfl

@[simp] theorem ofRows_realizationCompatibilityTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (realization : GeometricRealizationFunctorData ctx)
    (corrFamily : CorrGeneratorFamilyData ctx realization)
    (locFamily : LocGeneratorFamilyData ctx realization)
    (nisFamily : NisGeneratorFamilyData ctx realization)
    (a1Family : A1GeneratorFamilyData ctx realization)
    (envFamily : EnvGeneratorFamilyData ctx realization)
    (corrTarget : GeometricCorrespondenceFunctorialityTarget ctx realization)
    (locTarget : GeometricOpenClosedLocalizationTarget ctx realization)
    (nisTarget : GeometricNisnevichDescentTarget ctx realization)
    (a1Target : GeometricA1InvarianceTarget ctx realization)
    (envTarget : GeometricEnvelopeExactnessTarget ctx realization)
    (tateTarget : GeometricTateStabilizationTarget ctx realization)
    (generatorCoverageTarget realizationCompatibilityTarget
      motivicRecognitionInterfaceTarget : Prop) :
    (ofRows realization corrFamily locFamily nisFamily a1Family envFamily corrTarget locTarget
      nisTarget a1Target envTarget tateTarget generatorCoverageTarget realizationCompatibilityTarget
      motivicRecognitionInterfaceTarget).realizationCompatibilityTarget =
      realizationCompatibilityTarget := by
  rfl

@[simp] theorem ofRows_motivicRecognitionInterfaceTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (realization : GeometricRealizationFunctorData ctx)
    (corrFamily : CorrGeneratorFamilyData ctx realization)
    (locFamily : LocGeneratorFamilyData ctx realization)
    (nisFamily : NisGeneratorFamilyData ctx realization)
    (a1Family : A1GeneratorFamilyData ctx realization)
    (envFamily : EnvGeneratorFamilyData ctx realization)
    (corrTarget : GeometricCorrespondenceFunctorialityTarget ctx realization)
    (locTarget : GeometricOpenClosedLocalizationTarget ctx realization)
    (nisTarget : GeometricNisnevichDescentTarget ctx realization)
    (a1Target : GeometricA1InvarianceTarget ctx realization)
    (envTarget : GeometricEnvelopeExactnessTarget ctx realization)
    (tateTarget : GeometricTateStabilizationTarget ctx realization)
    (generatorCoverageTarget realizationCompatibilityTarget
      motivicRecognitionInterfaceTarget : Prop) :
    (ofRows realization corrFamily locFamily nisFamily a1Family envFamily corrTarget locTarget
      nisTarget a1Target envTarget tateTarget generatorCoverageTarget realizationCompatibilityTarget
      motivicRecognitionInterfaceTarget).motivicRecognitionInterfaceTarget =
      motivicRecognitionInterfaceTarget := by
  rfl

theorem ext
    {ctx : ClassicalComparisonContext.{u, v}}
    {P Q : GeometricGeneratorFamilyPackage ctx}
    (h : P = Q) :
    P = Q := h

/-- Forget the named generator families to the existing localization/descent theorem-target
package. -/
def toGeometricLocalizationPackage
    {ctx : ClassicalComparisonContext.{u, v}}
    (package : GeometricGeneratorFamilyPackage ctx) : GeometricLocalizationPackage ctx where
  realization := package.realization
  a1Invariance := package.a1Target
  nisnevichDescent := package.nisTarget
  openClosedLocalization := package.locTarget
  tateStabilization := package.tateTarget
  correspondenceFunctoriality := package.corrTarget
  envelopeExactness := package.envTarget
  realizationCompatibilityTarget :=
    package.generatorCoverageTarget ∧ package.realizationCompatibilityTarget
  motivicRecognitionInterfaceTarget := package.motivicRecognitionInterfaceTarget

/-- Named-generator-family bridge into the motivic-readiness interface. -/
def toClassicalMotivicRealizationReadiness
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (package : GeometricGeneratorFamilyPackage ctx)
    (tomography : GeometricRealizationTomographySoundness ctx structuredEq)
    (hrealization : package.realization = tomography.geometricRealizationFunctor) :
    ClassicalMotivicRealizationReadiness ctx structuredEq :=
  (package.toGeometricLocalizationPackage).toClassicalMotivicRealizationReadiness tomography hrealization

/-! ### Projection lemmas for the family-package forgetful chain. -/

@[simp] theorem toGeometricLocalizationPackage_realization
    {ctx : ClassicalComparisonContext.{u, v}}
    (package : GeometricGeneratorFamilyPackage ctx) :
    (package.toGeometricLocalizationPackage).realization = package.realization := rfl

@[simp] theorem toGeometricLocalizationPackage_a1Invariance
    {ctx : ClassicalComparisonContext.{u, v}}
    (package : GeometricGeneratorFamilyPackage ctx) :
    (package.toGeometricLocalizationPackage).a1Invariance = package.a1Target := rfl

@[simp] theorem toGeometricLocalizationPackage_nisnevichDescent
    {ctx : ClassicalComparisonContext.{u, v}}
    (package : GeometricGeneratorFamilyPackage ctx) :
    (package.toGeometricLocalizationPackage).nisnevichDescent = package.nisTarget := rfl

@[simp] theorem toGeometricLocalizationPackage_openClosedLocalization
    {ctx : ClassicalComparisonContext.{u, v}}
    (package : GeometricGeneratorFamilyPackage ctx) :
    (package.toGeometricLocalizationPackage).openClosedLocalization = package.locTarget := rfl

@[simp] theorem toGeometricLocalizationPackage_tateStabilization
  {ctx : ClassicalComparisonContext.{u, v}}
  (package : GeometricGeneratorFamilyPackage ctx) :
  (package.toGeometricLocalizationPackage).tateStabilization = package.tateTarget := rfl

@[simp] theorem toGeometricLocalizationPackage_correspondenceFunctoriality
    {ctx : ClassicalComparisonContext.{u, v}}
    (package : GeometricGeneratorFamilyPackage ctx) :
    (package.toGeometricLocalizationPackage).correspondenceFunctoriality = package.corrTarget := rfl

@[simp] theorem toGeometricLocalizationPackage_envelopeExactness
    {ctx : ClassicalComparisonContext.{u, v}}
    (package : GeometricGeneratorFamilyPackage ctx) :
    (package.toGeometricLocalizationPackage).envelopeExactness = package.envTarget := rfl

@[simp] theorem toGeometricLocalizationPackage_realizationCompatibilityTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (package : GeometricGeneratorFamilyPackage ctx) :
    (package.toGeometricLocalizationPackage).realizationCompatibilityTarget =
      (package.generatorCoverageTarget ∧ package.realizationCompatibilityTarget) := rfl

@[simp] theorem toGeometricLocalizationPackage_motivicRecognitionInterfaceTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (package : GeometricGeneratorFamilyPackage ctx) :
    (package.toGeometricLocalizationPackage).motivicRecognitionInterfaceTarget =
      package.motivicRecognitionInterfaceTarget := rfl

@[simp] theorem toClassicalMotivicRealizationReadiness_localizationPackage
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (package : GeometricGeneratorFamilyPackage ctx)
    (tomography : GeometricRealizationTomographySoundness ctx structuredEq)
    (hrealization : package.realization = tomography.geometricRealizationFunctor) :
    (package.toClassicalMotivicRealizationReadiness tomography hrealization).localizationPackage =
      package.toGeometricLocalizationPackage := rfl

@[simp] theorem toClassicalMotivicRealizationReadiness_tomographySoundness
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (package : GeometricGeneratorFamilyPackage ctx)
    (tomography : GeometricRealizationTomographySoundness ctx structuredEq)
    (hrealization : package.realization = tomography.geometricRealizationFunctor) :
    (package.toClassicalMotivicRealizationReadiness tomography hrealization).tomographySoundness =
      tomography := rfl

end GeometricGeneratorFamilyPackage

end ClassicalPeriods
end TraceCalc