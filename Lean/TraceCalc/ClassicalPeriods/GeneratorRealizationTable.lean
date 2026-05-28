import TraceCalc.ClassicalPeriods.GeometricGeneratorFamilies

universe u v w x y z

namespace TraceCalc
namespace ClassicalPeriods

/-- Typed realization assignment for the manuscript's `Corr` generator row. -/
structure CorrGeneratorRealizationAssignment
    (ctx : ClassicalComparisonContext.{u, v})
    (realization : GeometricRealizationFunctorData ctx) where
  family : CorrGeneratorFamilyData ctx realization
  sourceSlotName : String
  targetSlotName : String
  correspondenceSlotName : String
  bettiSlotName : String
  deRhamSlotName : String
  comparisonSlotName : String
  framedSlotName : String
  scalarSlotName : String
  sourceProjection : family.GeneratorIndex → GeometricPeriodObject ctx
  targetProjection : family.GeneratorIndex → GeometricPeriodObject ctx
  sourceBettiPlaceholder : family.GeneratorIndex → GeometricBettiRealizationData ctx
  targetBettiPlaceholder : family.GeneratorIndex → GeometricBettiRealizationData ctx
  sourceDeRhamPlaceholder : family.GeneratorIndex → GeometricDeRhamRealizationData ctx
  targetDeRhamPlaceholder : family.GeneratorIndex → GeometricDeRhamRealizationData ctx
  sourceComparisonDatum :
    (gen : family.GeneratorIndex) →
      GrothendieckComparisonData ctx (sourceBettiPlaceholder gen) (sourceDeRhamPlaceholder gen)
  targetComparisonDatum :
    (gen : family.GeneratorIndex) →
      GrothendieckComparisonData ctx (targetBettiPlaceholder gen) (targetDeRhamPlaceholder gen)
  sourceFramedPlaceholder :
    (gen : family.GeneratorIndex) → GeometricFramedObject (sourceProjection gen)
  targetFramedPlaceholder :
    (gen : family.GeneratorIndex) → GeometricFramedObject (targetProjection gen)
  sourceComparisonCompatibilityTarget :
    ∀ gen : family.GeneratorIndex,
      family.sourceObjectData gen =
        ⟨sourceBettiPlaceholder gen, sourceDeRhamPlaceholder gen, sourceComparisonDatum gen⟩
  targetComparisonCompatibilityTarget :
    ∀ gen : family.GeneratorIndex,
      family.targetObjectData gen =
        ⟨targetBettiPlaceholder gen, targetDeRhamPlaceholder gen, targetComparisonDatum gen⟩
  scalarExtractionTarget : Prop
  framedExtractionTarget : Prop
  theoremTarget :
    ∀ gen : family.GeneratorIndex,
      (sourceComparisonDatum gen).grothendieckComparisonTarget ∧
        (targetComparisonDatum gen).grothendieckComparisonTarget

namespace CorrGeneratorRealizationAssignment

@[simp] theorem sourceComparisonDatum_eq_familyData
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : CorrGeneratorRealizationAssignment ctx realization)
    (gen : assignment.family.GeneratorIndex) :
    assignment.family.sourceObjectData gen =
      ⟨assignment.sourceBettiPlaceholder gen, assignment.sourceDeRhamPlaceholder gen,
        assignment.sourceComparisonDatum gen⟩ :=
  assignment.sourceComparisonCompatibilityTarget gen

@[simp] theorem targetComparisonDatum_eq_familyData
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : CorrGeneratorRealizationAssignment ctx realization)
    (gen : assignment.family.GeneratorIndex) :
    assignment.family.targetObjectData gen =
      ⟨assignment.targetBettiPlaceholder gen, assignment.targetDeRhamPlaceholder gen,
        assignment.targetComparisonDatum gen⟩ :=
  assignment.targetComparisonCompatibilityTarget gen

theorem sourceGrothendieckComparisonTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : CorrGeneratorRealizationAssignment ctx realization)
    (gen : assignment.family.GeneratorIndex) :
    (assignment.sourceComparisonDatum gen).grothendieckComparisonTarget :=
  (assignment.theoremTarget gen).1

theorem targetGrothendieckComparisonTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : CorrGeneratorRealizationAssignment ctx realization)
    (gen : assignment.family.GeneratorIndex) :
    (assignment.targetComparisonDatum gen).grothendieckComparisonTarget :=
  (assignment.theoremTarget gen).2

theorem sourceSlot_target
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : CorrGeneratorRealizationAssignment ctx realization)
    (gen : assignment.family.GeneratorIndex) :
    (assignment.sourceComparisonDatum gen).grothendieckComparisonTarget :=
  assignment.sourceGrothendieckComparisonTarget gen

theorem targetSlot_target
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : CorrGeneratorRealizationAssignment ctx realization)
    (gen : assignment.family.GeneratorIndex) :
    (assignment.targetComparisonDatum gen).grothendieckComparisonTarget :=
  assignment.targetGrothendieckComparisonTarget gen

end CorrGeneratorRealizationAssignment

/-- Typed realization assignment for the manuscript's `Loc` generator row. -/
structure LocGeneratorRealizationAssignment
    (ctx : ClassicalComparisonContext.{u, v})
    (realization : GeometricRealizationFunctorData ctx) where
  family : LocGeneratorFamilyData ctx realization
  ambientSlotName : String
  openSlotName : String
  closedSlotName : String
  connectingMorphismSlotName : String
  bettiSlotName : String
  deRhamSlotName : String
  comparisonSlotName : String
  framedSlotName : String
  scalarSlotName : String
  ambientProjection : family.GeneratorIndex → GeometricPeriodObject ctx
  openProjection : family.GeneratorIndex → GeometricPeriodObject ctx
  closedProjection : family.GeneratorIndex → GeometricPeriodObject ctx
  ambientBettiPlaceholder : family.GeneratorIndex → GeometricBettiRealizationData ctx
  openBettiPlaceholder : family.GeneratorIndex → GeometricBettiRealizationData ctx
  closedBettiPlaceholder : family.GeneratorIndex → GeometricBettiRealizationData ctx
  ambientDeRhamPlaceholder : family.GeneratorIndex → GeometricDeRhamRealizationData ctx
  openDeRhamPlaceholder : family.GeneratorIndex → GeometricDeRhamRealizationData ctx
  closedDeRhamPlaceholder : family.GeneratorIndex → GeometricDeRhamRealizationData ctx
  ambientComparisonDatum :
    (gen : family.GeneratorIndex) →
      GrothendieckComparisonData ctx (ambientBettiPlaceholder gen) (ambientDeRhamPlaceholder gen)
  openComparisonDatum :
    (gen : family.GeneratorIndex) →
      GrothendieckComparisonData ctx (openBettiPlaceholder gen) (openDeRhamPlaceholder gen)
  closedComparisonDatum :
    (gen : family.GeneratorIndex) →
      GrothendieckComparisonData ctx (closedBettiPlaceholder gen) (closedDeRhamPlaceholder gen)
  ambientFramedPlaceholder :
    (gen : family.GeneratorIndex) → GeometricFramedObject (ambientProjection gen)
  openFramedPlaceholder :
    (gen : family.GeneratorIndex) → GeometricFramedObject (openProjection gen)
  closedFramedPlaceholder :
    (gen : family.GeneratorIndex) → GeometricFramedObject (closedProjection gen)
  ambientComparisonCompatibilityTarget :
    ∀ gen : family.GeneratorIndex,
      family.ambientData gen =
        ⟨ambientBettiPlaceholder gen, ambientDeRhamPlaceholder gen, ambientComparisonDatum gen⟩
  openComparisonCompatibilityTarget :
    ∀ gen : family.GeneratorIndex,
      family.openData gen =
        ⟨openBettiPlaceholder gen, openDeRhamPlaceholder gen, openComparisonDatum gen⟩
  closedComparisonCompatibilityTarget :
    ∀ gen : family.GeneratorIndex,
      family.closedData gen =
        ⟨closedBettiPlaceholder gen, closedDeRhamPlaceholder gen, closedComparisonDatum gen⟩
  scalarExtractionTarget : Prop
  framedExtractionTarget : Prop
  coneNaturalityData :
    LocalizationConeNaturalityData realization family.GeneratorIndex
      family.ambientIndex family.openIndex family.closedIndex
  theoremTarget :
    ∀ gen : family.GeneratorIndex,
      (ambientComparisonDatum gen).periodCompatibilityTarget ∧
        (openComparisonDatum gen).periodCompatibilityTarget ∧
        (closedComparisonDatum gen).periodCompatibilityTarget

namespace LocGeneratorRealizationAssignment

@[simp] theorem ambientComparisonDatum_eq_familyData
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : LocGeneratorRealizationAssignment ctx realization)
    (gen : assignment.family.GeneratorIndex) :
    assignment.family.ambientData gen =
      ⟨assignment.ambientBettiPlaceholder gen, assignment.ambientDeRhamPlaceholder gen,
        assignment.ambientComparisonDatum gen⟩ :=
  assignment.ambientComparisonCompatibilityTarget gen

@[simp] theorem openComparisonDatum_eq_familyData
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : LocGeneratorRealizationAssignment ctx realization)
    (gen : assignment.family.GeneratorIndex) :
    assignment.family.openData gen =
      ⟨assignment.openBettiPlaceholder gen, assignment.openDeRhamPlaceholder gen,
        assignment.openComparisonDatum gen⟩ :=
  assignment.openComparisonCompatibilityTarget gen

@[simp] theorem closedComparisonDatum_eq_familyData
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : LocGeneratorRealizationAssignment ctx realization)
    (gen : assignment.family.GeneratorIndex) :
    assignment.family.closedData gen =
      ⟨assignment.closedBettiPlaceholder gen, assignment.closedDeRhamPlaceholder gen,
        assignment.closedComparisonDatum gen⟩ :=
  assignment.closedComparisonCompatibilityTarget gen

theorem ambientPeriodCompatibilityTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : LocGeneratorRealizationAssignment ctx realization)
    (gen : assignment.family.GeneratorIndex) :
    (assignment.ambientComparisonDatum gen).periodCompatibilityTarget :=
  (assignment.theoremTarget gen).1

theorem openPeriodCompatibilityTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : LocGeneratorRealizationAssignment ctx realization)
    (gen : assignment.family.GeneratorIndex) :
    (assignment.openComparisonDatum gen).periodCompatibilityTarget :=
  (assignment.theoremTarget gen).2.1

theorem closedPeriodCompatibilityTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : LocGeneratorRealizationAssignment ctx realization)
    (gen : assignment.family.GeneratorIndex) :
    (assignment.closedComparisonDatum gen).periodCompatibilityTarget :=
  (assignment.theoremTarget gen).2.2

def triangleCompatibilityTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : LocGeneratorRealizationAssignment ctx realization) : Prop :=
  assignment.coneNaturalityData.triangleCompatibilityTarget

theorem connectingMorphismCompatibilityFromConeFunctoriality
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : LocGeneratorRealizationAssignment ctx realization) :
    assignment.coneNaturalityData.connectingMorphismCompatibilityTarget :=
  assignment.coneNaturalityData.connectingMorphismCompatibilityFromConeFunctoriality

theorem locConnectingPacket_comparison_naturality_from_replay
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : LocGeneratorRealizationAssignment ctx realization) :
    assignment.coneNaturalityData.connectingMorphismCompatibilityTarget :=
  assignment.coneNaturalityData.locConnectingPacket_comparison_naturality_from_replay

theorem triangleCompatibilityFromCertifiedReplay
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : LocGeneratorRealizationAssignment ctx realization) :
    assignment.triangleCompatibilityTarget :=
  assignment.coneNaturalityData.locTriangleCompatibility_from_certifiedReplay

theorem triangleCompatibilityFromConeFunctoriality
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : LocGeneratorRealizationAssignment ctx realization) :
    assignment.triangleCompatibilityTarget :=
  assignment.triangleCompatibilityFromCertifiedReplay

theorem ambientSlot_target
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : LocGeneratorRealizationAssignment ctx realization)
    (gen : assignment.family.GeneratorIndex) :
    (assignment.ambientComparisonDatum gen).periodCompatibilityTarget :=
  assignment.ambientPeriodCompatibilityTarget gen

theorem openSlot_target
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : LocGeneratorRealizationAssignment ctx realization)
    (gen : assignment.family.GeneratorIndex) :
    (assignment.openComparisonDatum gen).periodCompatibilityTarget :=
  assignment.openPeriodCompatibilityTarget gen

theorem closedSlot_target
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : LocGeneratorRealizationAssignment ctx realization)
    (gen : assignment.family.GeneratorIndex) :
    (assignment.closedComparisonDatum gen).periodCompatibilityTarget :=
  assignment.closedPeriodCompatibilityTarget gen

end LocGeneratorRealizationAssignment

/-- Typed realization assignment for the manuscript's `Nis` generator row. -/
structure NisGeneratorRealizationAssignment
    (ctx : ClassicalComparisonContext.{u, v})
    (realization : GeometricRealizationFunctorData ctx) where
  family : NisGeneratorFamilyData ctx realization
  baseSlotName : String
  patchSlotName : String
  overlapSlotName : String
  squareSlotName : String
  bettiSlotName : String
  deRhamSlotName : String
  comparisonSlotName : String
  framedSlotName : String
  scalarSlotName : String
  baseProjection : family.GeneratorIndex → GeometricPeriodObject ctx
  patchProjection : family.GeneratorIndex → GeometricPeriodObject ctx
  overlapProjection : family.GeneratorIndex → GeometricPeriodObject ctx
  baseBettiPlaceholder : family.GeneratorIndex → GeometricBettiRealizationData ctx
  patchBettiPlaceholder : family.GeneratorIndex → GeometricBettiRealizationData ctx
  overlapBettiPlaceholder : family.GeneratorIndex → GeometricBettiRealizationData ctx
  baseDeRhamPlaceholder : family.GeneratorIndex → GeometricDeRhamRealizationData ctx
  patchDeRhamPlaceholder : family.GeneratorIndex → GeometricDeRhamRealizationData ctx
  overlapDeRhamPlaceholder : family.GeneratorIndex → GeometricDeRhamRealizationData ctx
  baseComparisonDatum :
    (gen : family.GeneratorIndex) →
      GrothendieckComparisonData ctx (baseBettiPlaceholder gen) (baseDeRhamPlaceholder gen)
  patchComparisonDatum :
    (gen : family.GeneratorIndex) →
      GrothendieckComparisonData ctx (patchBettiPlaceholder gen) (patchDeRhamPlaceholder gen)
  overlapComparisonDatum :
    (gen : family.GeneratorIndex) →
      GrothendieckComparisonData ctx (overlapBettiPlaceholder gen) (overlapDeRhamPlaceholder gen)
  baseFramedPlaceholder :
    (gen : family.GeneratorIndex) → GeometricFramedObject (baseProjection gen)
  patchFramedPlaceholder :
    (gen : family.GeneratorIndex) → GeometricFramedObject (patchProjection gen)
  overlapFramedPlaceholder :
    (gen : family.GeneratorIndex) → GeometricFramedObject (overlapProjection gen)
  baseComparisonCompatibilityTarget :
    ∀ gen : family.GeneratorIndex,
      family.baseData gen =
        ⟨baseBettiPlaceholder gen, baseDeRhamPlaceholder gen, baseComparisonDatum gen⟩
  patchComparisonCompatibilityTarget :
    ∀ gen : family.GeneratorIndex,
      family.patchData gen =
        ⟨patchBettiPlaceholder gen, patchDeRhamPlaceholder gen, patchComparisonDatum gen⟩
  overlapComparisonCompatibilityTarget :
    ∀ gen : family.GeneratorIndex,
      family.overlapData gen =
        ⟨overlapBettiPlaceholder gen, overlapDeRhamPlaceholder gen, overlapComparisonDatum gen⟩
  scalarExtractionTarget : Prop
  framedExtractionTarget : Prop
  theoremTarget :
    ∀ gen : family.GeneratorIndex,
      (baseComparisonDatum gen).grothendieckComparisonTarget ∧
        (patchComparisonDatum gen).grothendieckComparisonTarget ∧
        (overlapComparisonDatum gen).grothendieckComparisonTarget
  descentSquareCompatibilityTarget : Prop
  traceNativePatchReplayData :
    CertifiedNisPatchReplayData ctx
      (∀ gen : family.GeneratorIndex,
        (baseComparisonDatum gen).grothendieckComparisonTarget ∧
          (patchComparisonDatum gen).grothendieckComparisonTarget ∧
          (overlapComparisonDatum gen).grothendieckComparisonTarget)
      descentSquareCompatibilityTarget

namespace NisGeneratorRealizationAssignment

@[simp] theorem baseComparisonDatum_eq_familyData
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : NisGeneratorRealizationAssignment ctx realization)
    (gen : assignment.family.GeneratorIndex) :
    assignment.family.baseData gen =
      ⟨assignment.baseBettiPlaceholder gen, assignment.baseDeRhamPlaceholder gen,
        assignment.baseComparisonDatum gen⟩ :=
  assignment.baseComparisonCompatibilityTarget gen

@[simp] theorem patchComparisonDatum_eq_familyData
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : NisGeneratorRealizationAssignment ctx realization)
    (gen : assignment.family.GeneratorIndex) :
    assignment.family.patchData gen =
      ⟨assignment.patchBettiPlaceholder gen, assignment.patchDeRhamPlaceholder gen,
        assignment.patchComparisonDatum gen⟩ :=
  assignment.patchComparisonCompatibilityTarget gen

@[simp] theorem overlapComparisonDatum_eq_familyData
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : NisGeneratorRealizationAssignment ctx realization)
    (gen : assignment.family.GeneratorIndex) :
    assignment.family.overlapData gen =
      ⟨assignment.overlapBettiPlaceholder gen, assignment.overlapDeRhamPlaceholder gen,
        assignment.overlapComparisonDatum gen⟩ :=
  assignment.overlapComparisonCompatibilityTarget gen

theorem baseGrothendieckComparisonTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : NisGeneratorRealizationAssignment ctx realization)
    (gen : assignment.family.GeneratorIndex) :
    (assignment.baseComparisonDatum gen).grothendieckComparisonTarget :=
  (assignment.theoremTarget gen).1

theorem patchGrothendieckComparisonTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : NisGeneratorRealizationAssignment ctx realization)
    (gen : assignment.family.GeneratorIndex) :
    (assignment.patchComparisonDatum gen).grothendieckComparisonTarget :=
  (assignment.theoremTarget gen).2.1

theorem overlapGrothendieckComparisonTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : NisGeneratorRealizationAssignment ctx realization)
    (gen : assignment.family.GeneratorIndex) :
    (assignment.overlapComparisonDatum gen).grothendieckComparisonTarget :=
  (assignment.theoremTarget gen).2.2

theorem baseSlot_target
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : NisGeneratorRealizationAssignment ctx realization)
    (gen : assignment.family.GeneratorIndex) :
    (assignment.baseComparisonDatum gen).grothendieckComparisonTarget :=
  assignment.baseGrothendieckComparisonTarget gen

theorem patchSlot_target
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : NisGeneratorRealizationAssignment ctx realization)
    (gen : assignment.family.GeneratorIndex) :
    (assignment.patchComparisonDatum gen).grothendieckComparisonTarget :=
  assignment.patchGrothendieckComparisonTarget gen

theorem overlapSlot_target
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : NisGeneratorRealizationAssignment ctx realization)
    (gen : assignment.family.GeneratorIndex) :
    (assignment.overlapComparisonDatum gen).grothendieckComparisonTarget :=
  assignment.overlapGrothendieckComparisonTarget gen

theorem nisOverlapAgreement_from_certifiedReplay
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : NisGeneratorRealizationAssignment ctx realization) :
    ∀ gen : assignment.family.GeneratorIndex,
      (assignment.baseComparisonDatum gen).grothendieckComparisonTarget ∧
        (assignment.patchComparisonDatum gen).grothendieckComparisonTarget ∧
        (assignment.overlapComparisonDatum gen).grothendieckComparisonTarget :=
  assignment.traceNativePatchReplayData.overlapAgreement_holds

theorem nisDescentSquareCompatibility_from_certifiedReplay
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : NisGeneratorRealizationAssignment ctx realization) :
    assignment.descentSquareCompatibilityTarget :=
  assignment.traceNativePatchReplayData.descentSquareCompatibility_holds

theorem nisDescentSquareCompatibilityShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : NisGeneratorRealizationAssignment ctx realization) :
    assignment.descentSquareCompatibilityTarget :=
  assignment.nisDescentSquareCompatibility_from_certifiedReplay

end NisGeneratorRealizationAssignment

/-- Typed realization assignment for the manuscript's `A1` generator row. -/
structure A1GeneratorRealizationAssignment
    (ctx : ClassicalComparisonContext.{u, v})
    (realization : GeometricRealizationFunctorData ctx) where
  family : A1GeneratorFamilyData ctx realization
  baseSlotName : String
  cylinderSlotName : String
  projectionZeroSlotName : String
  projectionOneSlotName : String
  bettiSlotName : String
  deRhamSlotName : String
  comparisonSlotName : String
  framedSlotName : String
  scalarSlotName : String
  baseProjection : family.GeneratorIndex → GeometricPeriodObject ctx
  cylinderProjection : family.GeneratorIndex → GeometricPeriodObject ctx
  baseBettiPlaceholder : family.GeneratorIndex → GeometricBettiRealizationData ctx
  cylinderBettiPlaceholder : family.GeneratorIndex → GeometricBettiRealizationData ctx
  baseDeRhamPlaceholder : family.GeneratorIndex → GeometricDeRhamRealizationData ctx
  cylinderDeRhamPlaceholder : family.GeneratorIndex → GeometricDeRhamRealizationData ctx
  baseComparisonDatum :
    (gen : family.GeneratorIndex) →
      GrothendieckComparisonData ctx (baseBettiPlaceholder gen) (baseDeRhamPlaceholder gen)
  cylinderComparisonDatum :
    (gen : family.GeneratorIndex) →
      GrothendieckComparisonData ctx (cylinderBettiPlaceholder gen) (cylinderDeRhamPlaceholder gen)
  baseFramedPlaceholder :
    (gen : family.GeneratorIndex) → GeometricFramedObject (baseProjection gen)
  cylinderFramedPlaceholder :
    (gen : family.GeneratorIndex) → GeometricFramedObject (cylinderProjection gen)
  baseComparisonCompatibilityTarget :
    ∀ gen : family.GeneratorIndex,
      family.baseData gen =
        ⟨baseBettiPlaceholder gen, baseDeRhamPlaceholder gen, baseComparisonDatum gen⟩
  cylinderComparisonCompatibilityTarget :
    ∀ gen : family.GeneratorIndex,
      family.cylinderData gen =
        ⟨cylinderBettiPlaceholder gen, cylinderDeRhamPlaceholder gen, cylinderComparisonDatum gen⟩
  scalarExtractionTarget : Prop
  framedExtractionTarget : Prop
  theoremTarget :
    ∀ gen : family.GeneratorIndex,
      (baseComparisonDatum gen).grothendieckComparisonTarget ∧
        (cylinderComparisonDatum gen).grothendieckComparisonTarget ∧
        (baseComparisonDatum gen).periodCompatibilityTarget ∧
        (cylinderComparisonDatum gen).periodCompatibilityTarget
  traceNativeHomotopyReplayData :
    CertifiedA1HomotopyReplayData ctx
      (∀ gen : family.GeneratorIndex,
        (baseComparisonDatum gen).grothendieckComparisonTarget ∧
          (cylinderComparisonDatum gen).grothendieckComparisonTarget ∧
          (baseComparisonDatum gen).periodCompatibilityTarget ∧
          (cylinderComparisonDatum gen).periodCompatibilityTarget)
      framedExtractionTarget

namespace A1GeneratorRealizationAssignment

@[simp] theorem baseComparisonDatum_eq_familyData
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : A1GeneratorRealizationAssignment ctx realization)
    (gen : assignment.family.GeneratorIndex) :
    assignment.family.baseData gen =
      ⟨assignment.baseBettiPlaceholder gen, assignment.baseDeRhamPlaceholder gen,
        assignment.baseComparisonDatum gen⟩ :=
  assignment.baseComparisonCompatibilityTarget gen

@[simp] theorem cylinderComparisonDatum_eq_familyData
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : A1GeneratorRealizationAssignment ctx realization)
    (gen : assignment.family.GeneratorIndex) :
    assignment.family.cylinderData gen =
      ⟨assignment.cylinderBettiPlaceholder gen, assignment.cylinderDeRhamPlaceholder gen,
        assignment.cylinderComparisonDatum gen⟩ :=
  assignment.cylinderComparisonCompatibilityTarget gen

theorem baseGrothendieckComparisonTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : A1GeneratorRealizationAssignment ctx realization)
    (gen : assignment.family.GeneratorIndex) :
    (assignment.baseComparisonDatum gen).grothendieckComparisonTarget :=
  (assignment.theoremTarget gen).1

theorem cylinderGrothendieckComparisonTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : A1GeneratorRealizationAssignment ctx realization)
    (gen : assignment.family.GeneratorIndex) :
    (assignment.cylinderComparisonDatum gen).grothendieckComparisonTarget :=
  (assignment.theoremTarget gen).2.1

theorem basePeriodCompatibilityTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : A1GeneratorRealizationAssignment ctx realization)
    (gen : assignment.family.GeneratorIndex) :
    (assignment.baseComparisonDatum gen).periodCompatibilityTarget :=
  (assignment.theoremTarget gen).2.2.1

theorem cylinderPeriodCompatibilityTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : A1GeneratorRealizationAssignment ctx realization)
    (gen : assignment.family.GeneratorIndex) :
    (assignment.cylinderComparisonDatum gen).periodCompatibilityTarget :=
  (assignment.theoremTarget gen).2.2.2

theorem baseSlot_grothendieckTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : A1GeneratorRealizationAssignment ctx realization)
    (gen : assignment.family.GeneratorIndex) :
    (assignment.baseComparisonDatum gen).grothendieckComparisonTarget :=
  assignment.baseGrothendieckComparisonTarget gen

theorem cylinderSlot_grothendieckTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : A1GeneratorRealizationAssignment ctx realization)
    (gen : assignment.family.GeneratorIndex) :
    (assignment.cylinderComparisonDatum gen).grothendieckComparisonTarget :=
  assignment.cylinderGrothendieckComparisonTarget gen

theorem baseSlot_periodTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : A1GeneratorRealizationAssignment ctx realization)
    (gen : assignment.family.GeneratorIndex) :
    (assignment.baseComparisonDatum gen).periodCompatibilityTarget :=
  assignment.basePeriodCompatibilityTarget gen

theorem cylinderSlot_periodTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : A1GeneratorRealizationAssignment ctx realization)
    (gen : assignment.family.GeneratorIndex) :
    (assignment.cylinderComparisonDatum gen).periodCompatibilityTarget :=
  assignment.cylinderPeriodCompatibilityTarget gen

theorem a1EndpointAgreement_from_certifiedReplay
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : A1GeneratorRealizationAssignment ctx realization) :
    ∀ gen : assignment.family.GeneratorIndex,
      (assignment.baseComparisonDatum gen).grothendieckComparisonTarget ∧
        (assignment.cylinderComparisonDatum gen).grothendieckComparisonTarget ∧
        (assignment.baseComparisonDatum gen).periodCompatibilityTarget ∧
        (assignment.cylinderComparisonDatum gen).periodCompatibilityTarget :=
  assignment.traceNativeHomotopyReplayData.endpointAgreement_holds

theorem a1HomotopyInvariance_from_certifiedReplay
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : A1GeneratorRealizationAssignment ctx realization) :
    assignment.framedExtractionTarget :=
  assignment.traceNativeHomotopyReplayData.homotopyInvariance_holds

theorem homotopyInvarianceShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : A1GeneratorRealizationAssignment ctx realization) :
    assignment.framedExtractionTarget :=
  assignment.a1HomotopyInvariance_from_certifiedReplay

end A1GeneratorRealizationAssignment

/-- Typed realization assignment for the manuscript's `Env` generator row. -/
structure EnvGeneratorRealizationAssignment
    (ctx : ClassicalComparisonContext.{u, v})
    (realization : GeometricRealizationFunctorData ctx) where
  family : EnvGeneratorFamilyData ctx realization
  ambientSlotName : String
  envelopeSlotName : String
  exactCompletionSlotName : String
  bettiSlotName : String
  deRhamSlotName : String
  comparisonSlotName : String
  framedSlotName : String
  scalarSlotName : String
  ambientProjection : family.GeneratorIndex → GeometricPeriodObject ctx
  envelopeProjection : family.GeneratorIndex → GeometricPeriodObject ctx
  ambientBettiPlaceholder : family.GeneratorIndex → GeometricBettiRealizationData ctx
  envelopeBettiPlaceholder : family.GeneratorIndex → GeometricBettiRealizationData ctx
  ambientDeRhamPlaceholder : family.GeneratorIndex → GeometricDeRhamRealizationData ctx
  envelopeDeRhamPlaceholder : family.GeneratorIndex → GeometricDeRhamRealizationData ctx
  ambientComparisonDatum :
    (gen : family.GeneratorIndex) →
      GrothendieckComparisonData ctx (ambientBettiPlaceholder gen) (ambientDeRhamPlaceholder gen)
  envelopeComparisonDatum :
    (gen : family.GeneratorIndex) →
      GrothendieckComparisonData ctx (envelopeBettiPlaceholder gen) (envelopeDeRhamPlaceholder gen)
  ambientFramedPlaceholder :
    (gen : family.GeneratorIndex) → GeometricFramedObject (ambientProjection gen)
  envelopeFramedPlaceholder :
    (gen : family.GeneratorIndex) → GeometricFramedObject (envelopeProjection gen)
  ambientComparisonCompatibilityTarget :
    ∀ gen : family.GeneratorIndex,
      family.ambientData gen =
        ⟨ambientBettiPlaceholder gen, ambientDeRhamPlaceholder gen, ambientComparisonDatum gen⟩
  envelopeComparisonCompatibilityTarget :
    ∀ gen : family.GeneratorIndex,
      family.envelopeData gen =
        ⟨envelopeBettiPlaceholder gen, envelopeDeRhamPlaceholder gen, envelopeComparisonDatum gen⟩
  scalarExtractionTarget : Prop
  framedExtractionTarget : Prop
  exactCompletionTarget : Prop
  theoremTarget :
    ∀ gen : family.GeneratorIndex,
      (ambientComparisonDatum gen).grothendieckComparisonTarget ∧
        (envelopeComparisonDatum gen).grothendieckComparisonTarget ∧
        (ambientComparisonDatum gen).periodCompatibilityTarget ∧
        (envelopeComparisonDatum gen).periodCompatibilityTarget
  traceNativeEnvReplayData :
    CertifiedEnvReplayData ctx
      (∀ gen : family.GeneratorIndex,
        (ambientComparisonDatum gen).grothendieckComparisonTarget ∧
          (envelopeComparisonDatum gen).grothendieckComparisonTarget ∧
          (ambientComparisonDatum gen).periodCompatibilityTarget ∧
          (envelopeComparisonDatum gen).periodCompatibilityTarget)
      exactCompletionTarget

namespace EnvGeneratorRealizationAssignment

@[simp] theorem ambientComparisonDatum_eq_familyData
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : EnvGeneratorRealizationAssignment ctx realization)
    (gen : assignment.family.GeneratorIndex) :
    assignment.family.ambientData gen =
      ⟨assignment.ambientBettiPlaceholder gen, assignment.ambientDeRhamPlaceholder gen,
        assignment.ambientComparisonDatum gen⟩ :=
  assignment.ambientComparisonCompatibilityTarget gen

@[simp] theorem envelopeComparisonDatum_eq_familyData
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : EnvGeneratorRealizationAssignment ctx realization)
    (gen : assignment.family.GeneratorIndex) :
    assignment.family.envelopeData gen =
      ⟨assignment.envelopeBettiPlaceholder gen, assignment.envelopeDeRhamPlaceholder gen,
        assignment.envelopeComparisonDatum gen⟩ :=
  assignment.envelopeComparisonCompatibilityTarget gen

theorem ambientGrothendieckComparisonTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : EnvGeneratorRealizationAssignment ctx realization)
    (gen : assignment.family.GeneratorIndex) :
    (assignment.ambientComparisonDatum gen).grothendieckComparisonTarget :=
  (assignment.theoremTarget gen).1

theorem envelopeGrothendieckComparisonTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : EnvGeneratorRealizationAssignment ctx realization)
    (gen : assignment.family.GeneratorIndex) :
    (assignment.envelopeComparisonDatum gen).grothendieckComparisonTarget :=
  (assignment.theoremTarget gen).2.1

theorem ambientPeriodCompatibilityTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : EnvGeneratorRealizationAssignment ctx realization)
    (gen : assignment.family.GeneratorIndex) :
    (assignment.ambientComparisonDatum gen).periodCompatibilityTarget :=
  (assignment.theoremTarget gen).2.2.1

theorem envelopePeriodCompatibilityTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : EnvGeneratorRealizationAssignment ctx realization)
    (gen : assignment.family.GeneratorIndex) :
    (assignment.envelopeComparisonDatum gen).periodCompatibilityTarget :=
  (assignment.theoremTarget gen).2.2.2

theorem ambientSlot_grothendieckTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : EnvGeneratorRealizationAssignment ctx realization)
    (gen : assignment.family.GeneratorIndex) :
    (assignment.ambientComparisonDatum gen).grothendieckComparisonTarget :=
  assignment.ambientGrothendieckComparisonTarget gen

theorem envelopeSlot_grothendieckTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : EnvGeneratorRealizationAssignment ctx realization)
    (gen : assignment.family.GeneratorIndex) :
    (assignment.envelopeComparisonDatum gen).grothendieckComparisonTarget :=
  assignment.envelopeGrothendieckComparisonTarget gen

theorem ambientSlot_periodTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : EnvGeneratorRealizationAssignment ctx realization)
    (gen : assignment.family.GeneratorIndex) :
    (assignment.ambientComparisonDatum gen).periodCompatibilityTarget :=
  assignment.ambientPeriodCompatibilityTarget gen

theorem envelopeSlot_periodTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : EnvGeneratorRealizationAssignment ctx realization)
    (gen : assignment.family.GeneratorIndex) :
    (assignment.envelopeComparisonDatum gen).periodCompatibilityTarget :=
  assignment.envelopePeriodCompatibilityTarget gen

theorem envComparisonAgreement_from_certifiedReplay
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : EnvGeneratorRealizationAssignment ctx realization) :
    ∀ gen : assignment.family.GeneratorIndex,
      (assignment.ambientComparisonDatum gen).grothendieckComparisonTarget ∧
        (assignment.envelopeComparisonDatum gen).grothendieckComparisonTarget ∧
        (assignment.ambientComparisonDatum gen).periodCompatibilityTarget ∧
        (assignment.envelopeComparisonDatum gen).periodCompatibilityTarget :=
  assignment.traceNativeEnvReplayData.comparisonAgreement_holds

def envReplayTransformer_from_certifiedReplay
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : EnvGeneratorRealizationAssignment ctx realization) :
    EnvReplayTransformerTarget :=
  assignment.traceNativeEnvReplayData.replayTransformerTarget

def envWhisker_from_certifiedReplay
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : EnvGeneratorRealizationAssignment ctx realization) :
    EnvReplayTransformerTarget :=
  EnvReplayTransformerTarget.envWhisker_from_certifiedReplay
    assignment.traceNativeEnvReplayData.replayTransformerTarget

def envCompose_from_certifiedReplay
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : EnvGeneratorRealizationAssignment ctx realization) :
    EnvReplayTransformerTarget :=
  EnvReplayTransformerTarget.envCompose_from_certifiedReplay
    assignment.traceNativeEnvReplayData.replayTransformerTarget

def envTensor_from_certifiedReplay
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : EnvGeneratorRealizationAssignment ctx realization) :
    EnvReplayTransformerTarget :=
  EnvReplayTransformerTarget.envTensor_from_certifiedReplay
    assignment.traceNativeEnvReplayData.replayTransformerTarget

def envShift_from_certifiedReplay
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : EnvGeneratorRealizationAssignment ctx realization) :
    EnvReplayTransformerTarget :=
  EnvReplayTransformerTarget.envShift_from_certifiedReplay
    assignment.traceNativeEnvReplayData.replayTransformerTarget

def envStructuralAdmin_from_certifiedReplay
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : EnvGeneratorRealizationAssignment ctx realization) :
    EnvReplayTransformerTarget :=
  EnvReplayTransformerTarget.envStructuralAdmin_from_certifiedReplay
    assignment.traceNativeEnvReplayData.replayTransformerTarget

theorem envFormalClosureSoundness_from_certifiedReplay
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : EnvGeneratorRealizationAssignment ctx realization) :
    assignment.exactCompletionTarget :=
  assignment.traceNativeEnvReplayData.formalClosure_holds

theorem exactCompletionShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (assignment : EnvGeneratorRealizationAssignment ctx realization) :
    assignment.exactCompletionTarget :=
  assignment.envFormalClosureSoundness_from_certifiedReplay

end EnvGeneratorRealizationAssignment

/-- Typed realization-assignment table for the manuscript's `Corr / Loc / Nis / A1 / Env` rows. -/
structure GeneratorRealizationAssignmentTable
    (ctx : ClassicalComparisonContext.{u, v}) where
  realization : GeometricRealizationFunctorData ctx
  corrAssignment : CorrGeneratorRealizationAssignment ctx realization
  locAssignment : LocGeneratorRealizationAssignment ctx realization
  nisAssignment : NisGeneratorRealizationAssignment ctx realization
  a1Assignment : A1GeneratorRealizationAssignment ctx realization
  envAssignment : EnvGeneratorRealizationAssignment ctx realization
  corrTarget : GeometricCorrespondenceFunctorialityTarget ctx realization
  locTarget : GeometricOpenClosedLocalizationTarget ctx realization
  nisTarget : GeometricNisnevichDescentTarget ctx realization
  a1Target : GeometricA1InvarianceTarget ctx realization
  envTarget : GeometricEnvelopeExactnessTarget ctx realization
  tateTarget : GeometricTateStabilizationTarget ctx realization
  generatorCoverageTarget : Prop
  assignmentCompatibilityTarget : Prop
  motivicRecognitionInterfaceTarget : Prop

namespace GeneratorRealizationAssignmentTable

/-- Constructor helper for the full generator-assignment table. -/
def ofAssignments
    {ctx : ClassicalComparisonContext.{u, v}}
    (realization : GeometricRealizationFunctorData ctx)
    (corrAssignment : CorrGeneratorRealizationAssignment ctx realization)
    (locAssignment : LocGeneratorRealizationAssignment ctx realization)
    (nisAssignment : NisGeneratorRealizationAssignment ctx realization)
    (a1Assignment : A1GeneratorRealizationAssignment ctx realization)
    (envAssignment : EnvGeneratorRealizationAssignment ctx realization)
    (corrTarget : GeometricCorrespondenceFunctorialityTarget ctx realization)
    (locTarget : GeometricOpenClosedLocalizationTarget ctx realization)
    (nisTarget : GeometricNisnevichDescentTarget ctx realization)
    (a1Target : GeometricA1InvarianceTarget ctx realization)
    (envTarget : GeometricEnvelopeExactnessTarget ctx realization)
    (tateTarget : GeometricTateStabilizationTarget ctx realization)
    (generatorCoverageTarget assignmentCompatibilityTarget motivicRecognitionInterfaceTarget : Prop) :
    GeneratorRealizationAssignmentTable ctx where
  realization := realization
  corrAssignment := corrAssignment
  locAssignment := locAssignment
  nisAssignment := nisAssignment
  a1Assignment := a1Assignment
  envAssignment := envAssignment
  corrTarget := corrTarget
  locTarget := locTarget
  nisTarget := nisTarget
  a1Target := a1Target
  envTarget := envTarget
  tateTarget := tateTarget
  generatorCoverageTarget := generatorCoverageTarget
  assignmentCompatibilityTarget := assignmentCompatibilityTarget
  motivicRecognitionInterfaceTarget := motivicRecognitionInterfaceTarget

@[simp] theorem ofAssignments_realization
    {ctx : ClassicalComparisonContext.{u, v}}
    (realization : GeometricRealizationFunctorData ctx)
    (corrAssignment : CorrGeneratorRealizationAssignment ctx realization)
    (locAssignment : LocGeneratorRealizationAssignment ctx realization)
    (nisAssignment : NisGeneratorRealizationAssignment ctx realization)
    (a1Assignment : A1GeneratorRealizationAssignment ctx realization)
    (envAssignment : EnvGeneratorRealizationAssignment ctx realization)
    (corrTarget : GeometricCorrespondenceFunctorialityTarget ctx realization)
    (locTarget : GeometricOpenClosedLocalizationTarget ctx realization)
    (nisTarget : GeometricNisnevichDescentTarget ctx realization)
    (a1Target : GeometricA1InvarianceTarget ctx realization)
    (envTarget : GeometricEnvelopeExactnessTarget ctx realization)
    (tateTarget : GeometricTateStabilizationTarget ctx realization)
    (generatorCoverageTarget assignmentCompatibilityTarget motivicRecognitionInterfaceTarget : Prop) :
    (ofAssignments realization corrAssignment locAssignment nisAssignment a1Assignment envAssignment
      corrTarget locTarget nisTarget a1Target envTarget tateTarget generatorCoverageTarget
      assignmentCompatibilityTarget motivicRecognitionInterfaceTarget).realization = realization := rfl

@[simp] theorem ofAssignments_corrAssignment
    {ctx : ClassicalComparisonContext.{u, v}}
    (realization : GeometricRealizationFunctorData ctx)
    (corrAssignment : CorrGeneratorRealizationAssignment ctx realization)
    (locAssignment : LocGeneratorRealizationAssignment ctx realization)
    (nisAssignment : NisGeneratorRealizationAssignment ctx realization)
    (a1Assignment : A1GeneratorRealizationAssignment ctx realization)
    (envAssignment : EnvGeneratorRealizationAssignment ctx realization)
    (corrTarget : GeometricCorrespondenceFunctorialityTarget ctx realization)
    (locTarget : GeometricOpenClosedLocalizationTarget ctx realization)
    (nisTarget : GeometricNisnevichDescentTarget ctx realization)
    (a1Target : GeometricA1InvarianceTarget ctx realization)
    (envTarget : GeometricEnvelopeExactnessTarget ctx realization)
    (tateTarget : GeometricTateStabilizationTarget ctx realization)
    (generatorCoverageTarget assignmentCompatibilityTarget motivicRecognitionInterfaceTarget : Prop) :
    (ofAssignments realization corrAssignment locAssignment nisAssignment a1Assignment envAssignment
      corrTarget locTarget nisTarget a1Target envTarget tateTarget generatorCoverageTarget
      assignmentCompatibilityTarget motivicRecognitionInterfaceTarget).corrAssignment = corrAssignment := rfl

@[simp] theorem ofAssignments_locAssignment
    {ctx : ClassicalComparisonContext.{u, v}}
    (realization : GeometricRealizationFunctorData ctx)
    (corrAssignment : CorrGeneratorRealizationAssignment ctx realization)
    (locAssignment : LocGeneratorRealizationAssignment ctx realization)
    (nisAssignment : NisGeneratorRealizationAssignment ctx realization)
    (a1Assignment : A1GeneratorRealizationAssignment ctx realization)
    (envAssignment : EnvGeneratorRealizationAssignment ctx realization)
    (corrTarget : GeometricCorrespondenceFunctorialityTarget ctx realization)
    (locTarget : GeometricOpenClosedLocalizationTarget ctx realization)
    (nisTarget : GeometricNisnevichDescentTarget ctx realization)
    (a1Target : GeometricA1InvarianceTarget ctx realization)
    (envTarget : GeometricEnvelopeExactnessTarget ctx realization)
    (tateTarget : GeometricTateStabilizationTarget ctx realization)
    (generatorCoverageTarget assignmentCompatibilityTarget motivicRecognitionInterfaceTarget : Prop) :
    (ofAssignments realization corrAssignment locAssignment nisAssignment a1Assignment envAssignment
      corrTarget locTarget nisTarget a1Target envTarget tateTarget generatorCoverageTarget
      assignmentCompatibilityTarget motivicRecognitionInterfaceTarget).locAssignment = locAssignment := rfl

@[simp] theorem ofAssignments_nisAssignment
    {ctx : ClassicalComparisonContext.{u, v}}
    (realization : GeometricRealizationFunctorData ctx)
    (corrAssignment : CorrGeneratorRealizationAssignment ctx realization)
    (locAssignment : LocGeneratorRealizationAssignment ctx realization)
    (nisAssignment : NisGeneratorRealizationAssignment ctx realization)
    (a1Assignment : A1GeneratorRealizationAssignment ctx realization)
    (envAssignment : EnvGeneratorRealizationAssignment ctx realization)
    (corrTarget : GeometricCorrespondenceFunctorialityTarget ctx realization)
    (locTarget : GeometricOpenClosedLocalizationTarget ctx realization)
    (nisTarget : GeometricNisnevichDescentTarget ctx realization)
    (a1Target : GeometricA1InvarianceTarget ctx realization)
    (envTarget : GeometricEnvelopeExactnessTarget ctx realization)
    (tateTarget : GeometricTateStabilizationTarget ctx realization)
    (generatorCoverageTarget assignmentCompatibilityTarget motivicRecognitionInterfaceTarget : Prop) :
    (ofAssignments realization corrAssignment locAssignment nisAssignment a1Assignment envAssignment
      corrTarget locTarget nisTarget a1Target envTarget tateTarget generatorCoverageTarget
      assignmentCompatibilityTarget motivicRecognitionInterfaceTarget).nisAssignment = nisAssignment := rfl

@[simp] theorem ofAssignments_a1Assignment
    {ctx : ClassicalComparisonContext.{u, v}}
    (realization : GeometricRealizationFunctorData ctx)
    (corrAssignment : CorrGeneratorRealizationAssignment ctx realization)
    (locAssignment : LocGeneratorRealizationAssignment ctx realization)
    (nisAssignment : NisGeneratorRealizationAssignment ctx realization)
    (a1Assignment : A1GeneratorRealizationAssignment ctx realization)
    (envAssignment : EnvGeneratorRealizationAssignment ctx realization)
    (corrTarget : GeometricCorrespondenceFunctorialityTarget ctx realization)
    (locTarget : GeometricOpenClosedLocalizationTarget ctx realization)
    (nisTarget : GeometricNisnevichDescentTarget ctx realization)
    (a1Target : GeometricA1InvarianceTarget ctx realization)
    (envTarget : GeometricEnvelopeExactnessTarget ctx realization)
    (tateTarget : GeometricTateStabilizationTarget ctx realization)
    (generatorCoverageTarget assignmentCompatibilityTarget motivicRecognitionInterfaceTarget : Prop) :
    (ofAssignments realization corrAssignment locAssignment nisAssignment a1Assignment envAssignment
      corrTarget locTarget nisTarget a1Target envTarget tateTarget generatorCoverageTarget
      assignmentCompatibilityTarget motivicRecognitionInterfaceTarget).a1Assignment = a1Assignment := rfl

@[simp] theorem ofAssignments_envAssignment
    {ctx : ClassicalComparisonContext.{u, v}}
    (realization : GeometricRealizationFunctorData ctx)
    (corrAssignment : CorrGeneratorRealizationAssignment ctx realization)
    (locAssignment : LocGeneratorRealizationAssignment ctx realization)
    (nisAssignment : NisGeneratorRealizationAssignment ctx realization)
    (a1Assignment : A1GeneratorRealizationAssignment ctx realization)
    (envAssignment : EnvGeneratorRealizationAssignment ctx realization)
    (corrTarget : GeometricCorrespondenceFunctorialityTarget ctx realization)
    (locTarget : GeometricOpenClosedLocalizationTarget ctx realization)
    (nisTarget : GeometricNisnevichDescentTarget ctx realization)
    (a1Target : GeometricA1InvarianceTarget ctx realization)
    (envTarget : GeometricEnvelopeExactnessTarget ctx realization)
    (tateTarget : GeometricTateStabilizationTarget ctx realization)
    (generatorCoverageTarget assignmentCompatibilityTarget motivicRecognitionInterfaceTarget : Prop) :
    (ofAssignments realization corrAssignment locAssignment nisAssignment a1Assignment envAssignment
      corrTarget locTarget nisTarget a1Target envTarget tateTarget generatorCoverageTarget
      assignmentCompatibilityTarget motivicRecognitionInterfaceTarget).envAssignment = envAssignment := rfl

@[simp] theorem ofAssignments_corr_sourceSlotName
    {ctx : ClassicalComparisonContext.{u, v}}
    (realization : GeometricRealizationFunctorData ctx)
    (corrAssignment : CorrGeneratorRealizationAssignment ctx realization)
    (locAssignment : LocGeneratorRealizationAssignment ctx realization)
    (nisAssignment : NisGeneratorRealizationAssignment ctx realization)
    (a1Assignment : A1GeneratorRealizationAssignment ctx realization)
    (envAssignment : EnvGeneratorRealizationAssignment ctx realization)
    (corrTarget : GeometricCorrespondenceFunctorialityTarget ctx realization)
    (locTarget : GeometricOpenClosedLocalizationTarget ctx realization)
    (nisTarget : GeometricNisnevichDescentTarget ctx realization)
    (a1Target : GeometricA1InvarianceTarget ctx realization)
    (envTarget : GeometricEnvelopeExactnessTarget ctx realization)
    (tateTarget : GeometricTateStabilizationTarget ctx realization)
    (generatorCoverageTarget assignmentCompatibilityTarget motivicRecognitionInterfaceTarget : Prop) :
    (ofAssignments realization corrAssignment locAssignment nisAssignment a1Assignment envAssignment
      corrTarget locTarget nisTarget a1Target envTarget tateTarget generatorCoverageTarget
      assignmentCompatibilityTarget motivicRecognitionInterfaceTarget).corrAssignment.sourceSlotName =
        corrAssignment.sourceSlotName := rfl

@[simp] theorem ofAssignments_corr_targetSlotName
    {ctx : ClassicalComparisonContext.{u, v}}
    (realization : GeometricRealizationFunctorData ctx)
    (corrAssignment : CorrGeneratorRealizationAssignment ctx realization)
    (locAssignment : LocGeneratorRealizationAssignment ctx realization)
    (nisAssignment : NisGeneratorRealizationAssignment ctx realization)
    (a1Assignment : A1GeneratorRealizationAssignment ctx realization)
    (envAssignment : EnvGeneratorRealizationAssignment ctx realization)
    (corrTarget : GeometricCorrespondenceFunctorialityTarget ctx realization)
    (locTarget : GeometricOpenClosedLocalizationTarget ctx realization)
    (nisTarget : GeometricNisnevichDescentTarget ctx realization)
    (a1Target : GeometricA1InvarianceTarget ctx realization)
    (envTarget : GeometricEnvelopeExactnessTarget ctx realization)
    (tateTarget : GeometricTateStabilizationTarget ctx realization)
    (generatorCoverageTarget assignmentCompatibilityTarget motivicRecognitionInterfaceTarget : Prop) :
    (ofAssignments realization corrAssignment locAssignment nisAssignment a1Assignment envAssignment
      corrTarget locTarget nisTarget a1Target envTarget tateTarget generatorCoverageTarget
      assignmentCompatibilityTarget motivicRecognitionInterfaceTarget).corrAssignment.targetSlotName =
        corrAssignment.targetSlotName := rfl

@[simp] theorem ofAssignments_loc_ambientSlotName
    {ctx : ClassicalComparisonContext.{u, v}}
    (realization : GeometricRealizationFunctorData ctx)
    (corrAssignment : CorrGeneratorRealizationAssignment ctx realization)
    (locAssignment : LocGeneratorRealizationAssignment ctx realization)
    (nisAssignment : NisGeneratorRealizationAssignment ctx realization)
    (a1Assignment : A1GeneratorRealizationAssignment ctx realization)
    (envAssignment : EnvGeneratorRealizationAssignment ctx realization)
    (corrTarget : GeometricCorrespondenceFunctorialityTarget ctx realization)
    (locTarget : GeometricOpenClosedLocalizationTarget ctx realization)
    (nisTarget : GeometricNisnevichDescentTarget ctx realization)
    (a1Target : GeometricA1InvarianceTarget ctx realization)
    (envTarget : GeometricEnvelopeExactnessTarget ctx realization)
    (tateTarget : GeometricTateStabilizationTarget ctx realization)
    (generatorCoverageTarget assignmentCompatibilityTarget motivicRecognitionInterfaceTarget : Prop) :
    (ofAssignments realization corrAssignment locAssignment nisAssignment a1Assignment envAssignment
      corrTarget locTarget nisTarget a1Target envTarget tateTarget generatorCoverageTarget
      assignmentCompatibilityTarget motivicRecognitionInterfaceTarget).locAssignment.ambientSlotName =
        locAssignment.ambientSlotName := rfl

@[simp] theorem ofAssignments_nis_baseSlotName
    {ctx : ClassicalComparisonContext.{u, v}}
    (realization : GeometricRealizationFunctorData ctx)
    (corrAssignment : CorrGeneratorRealizationAssignment ctx realization)
    (locAssignment : LocGeneratorRealizationAssignment ctx realization)
    (nisAssignment : NisGeneratorRealizationAssignment ctx realization)
    (a1Assignment : A1GeneratorRealizationAssignment ctx realization)
    (envAssignment : EnvGeneratorRealizationAssignment ctx realization)
    (corrTarget : GeometricCorrespondenceFunctorialityTarget ctx realization)
    (locTarget : GeometricOpenClosedLocalizationTarget ctx realization)
    (nisTarget : GeometricNisnevichDescentTarget ctx realization)
    (a1Target : GeometricA1InvarianceTarget ctx realization)
    (envTarget : GeometricEnvelopeExactnessTarget ctx realization)
    (tateTarget : GeometricTateStabilizationTarget ctx realization)
    (generatorCoverageTarget assignmentCompatibilityTarget motivicRecognitionInterfaceTarget : Prop) :
    (ofAssignments realization corrAssignment locAssignment nisAssignment a1Assignment envAssignment
      corrTarget locTarget nisTarget a1Target envTarget tateTarget generatorCoverageTarget
      assignmentCompatibilityTarget motivicRecognitionInterfaceTarget).nisAssignment.baseSlotName =
        nisAssignment.baseSlotName := rfl

@[simp] theorem ofAssignments_a1_baseSlotName
    {ctx : ClassicalComparisonContext.{u, v}}
    (realization : GeometricRealizationFunctorData ctx)
    (corrAssignment : CorrGeneratorRealizationAssignment ctx realization)
    (locAssignment : LocGeneratorRealizationAssignment ctx realization)
    (nisAssignment : NisGeneratorRealizationAssignment ctx realization)
    (a1Assignment : A1GeneratorRealizationAssignment ctx realization)
    (envAssignment : EnvGeneratorRealizationAssignment ctx realization)
    (corrTarget : GeometricCorrespondenceFunctorialityTarget ctx realization)
    (locTarget : GeometricOpenClosedLocalizationTarget ctx realization)
    (nisTarget : GeometricNisnevichDescentTarget ctx realization)
    (a1Target : GeometricA1InvarianceTarget ctx realization)
    (envTarget : GeometricEnvelopeExactnessTarget ctx realization)
    (tateTarget : GeometricTateStabilizationTarget ctx realization)
    (generatorCoverageTarget assignmentCompatibilityTarget motivicRecognitionInterfaceTarget : Prop) :
    (ofAssignments realization corrAssignment locAssignment nisAssignment a1Assignment envAssignment
      corrTarget locTarget nisTarget a1Target envTarget tateTarget generatorCoverageTarget
      assignmentCompatibilityTarget motivicRecognitionInterfaceTarget).a1Assignment.baseSlotName =
        a1Assignment.baseSlotName := rfl

@[simp] theorem ofAssignments_env_ambientSlotName
    {ctx : ClassicalComparisonContext.{u, v}}
    (realization : GeometricRealizationFunctorData ctx)
    (corrAssignment : CorrGeneratorRealizationAssignment ctx realization)
    (locAssignment : LocGeneratorRealizationAssignment ctx realization)
    (nisAssignment : NisGeneratorRealizationAssignment ctx realization)
    (a1Assignment : A1GeneratorRealizationAssignment ctx realization)
    (envAssignment : EnvGeneratorRealizationAssignment ctx realization)
    (corrTarget : GeometricCorrespondenceFunctorialityTarget ctx realization)
    (locTarget : GeometricOpenClosedLocalizationTarget ctx realization)
    (nisTarget : GeometricNisnevichDescentTarget ctx realization)
    (a1Target : GeometricA1InvarianceTarget ctx realization)
    (envTarget : GeometricEnvelopeExactnessTarget ctx realization)
    (tateTarget : GeometricTateStabilizationTarget ctx realization)
    (generatorCoverageTarget assignmentCompatibilityTarget motivicRecognitionInterfaceTarget : Prop) :
    (ofAssignments realization corrAssignment locAssignment nisAssignment a1Assignment envAssignment
      corrTarget locTarget nisTarget a1Target envTarget tateTarget generatorCoverageTarget
      assignmentCompatibilityTarget motivicRecognitionInterfaceTarget).envAssignment.ambientSlotName =
        envAssignment.ambientSlotName := rfl

@[simp] theorem ofAssignments_corrTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (realization : GeometricRealizationFunctorData ctx)
    (corrAssignment : CorrGeneratorRealizationAssignment ctx realization)
    (locAssignment : LocGeneratorRealizationAssignment ctx realization)
    (nisAssignment : NisGeneratorRealizationAssignment ctx realization)
    (a1Assignment : A1GeneratorRealizationAssignment ctx realization)
    (envAssignment : EnvGeneratorRealizationAssignment ctx realization)
    (corrTarget : GeometricCorrespondenceFunctorialityTarget ctx realization)
    (locTarget : GeometricOpenClosedLocalizationTarget ctx realization)
    (nisTarget : GeometricNisnevichDescentTarget ctx realization)
    (a1Target : GeometricA1InvarianceTarget ctx realization)
    (envTarget : GeometricEnvelopeExactnessTarget ctx realization)
    (tateTarget : GeometricTateStabilizationTarget ctx realization)
    (generatorCoverageTarget assignmentCompatibilityTarget motivicRecognitionInterfaceTarget : Prop) :
    (ofAssignments realization corrAssignment locAssignment nisAssignment a1Assignment envAssignment
      corrTarget locTarget nisTarget a1Target envTarget tateTarget generatorCoverageTarget
      assignmentCompatibilityTarget motivicRecognitionInterfaceTarget).corrTarget = corrTarget := rfl

@[simp] theorem ofAssignments_locTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (realization : GeometricRealizationFunctorData ctx)
    (corrAssignment : CorrGeneratorRealizationAssignment ctx realization)
    (locAssignment : LocGeneratorRealizationAssignment ctx realization)
    (nisAssignment : NisGeneratorRealizationAssignment ctx realization)
    (a1Assignment : A1GeneratorRealizationAssignment ctx realization)
    (envAssignment : EnvGeneratorRealizationAssignment ctx realization)
    (corrTarget : GeometricCorrespondenceFunctorialityTarget ctx realization)
    (locTarget : GeometricOpenClosedLocalizationTarget ctx realization)
    (nisTarget : GeometricNisnevichDescentTarget ctx realization)
    (a1Target : GeometricA1InvarianceTarget ctx realization)
    (envTarget : GeometricEnvelopeExactnessTarget ctx realization)
    (tateTarget : GeometricTateStabilizationTarget ctx realization)
    (generatorCoverageTarget assignmentCompatibilityTarget motivicRecognitionInterfaceTarget : Prop) :
    (ofAssignments realization corrAssignment locAssignment nisAssignment a1Assignment envAssignment
      corrTarget locTarget nisTarget a1Target envTarget tateTarget generatorCoverageTarget
      assignmentCompatibilityTarget motivicRecognitionInterfaceTarget).locTarget = locTarget := rfl

@[simp] theorem ofAssignments_nisTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (realization : GeometricRealizationFunctorData ctx)
    (corrAssignment : CorrGeneratorRealizationAssignment ctx realization)
    (locAssignment : LocGeneratorRealizationAssignment ctx realization)
    (nisAssignment : NisGeneratorRealizationAssignment ctx realization)
    (a1Assignment : A1GeneratorRealizationAssignment ctx realization)
    (envAssignment : EnvGeneratorRealizationAssignment ctx realization)
    (corrTarget : GeometricCorrespondenceFunctorialityTarget ctx realization)
    (locTarget : GeometricOpenClosedLocalizationTarget ctx realization)
    (nisTarget : GeometricNisnevichDescentTarget ctx realization)
    (a1Target : GeometricA1InvarianceTarget ctx realization)
    (envTarget : GeometricEnvelopeExactnessTarget ctx realization)
    (tateTarget : GeometricTateStabilizationTarget ctx realization)
    (generatorCoverageTarget assignmentCompatibilityTarget motivicRecognitionInterfaceTarget : Prop) :
    (ofAssignments realization corrAssignment locAssignment nisAssignment a1Assignment envAssignment
      corrTarget locTarget nisTarget a1Target envTarget tateTarget generatorCoverageTarget
      assignmentCompatibilityTarget motivicRecognitionInterfaceTarget).nisTarget = nisTarget := rfl

@[simp] theorem ofAssignments_a1Target
    {ctx : ClassicalComparisonContext.{u, v}}
    (realization : GeometricRealizationFunctorData ctx)
    (corrAssignment : CorrGeneratorRealizationAssignment ctx realization)
    (locAssignment : LocGeneratorRealizationAssignment ctx realization)
    (nisAssignment : NisGeneratorRealizationAssignment ctx realization)
    (a1Assignment : A1GeneratorRealizationAssignment ctx realization)
    (envAssignment : EnvGeneratorRealizationAssignment ctx realization)
    (corrTarget : GeometricCorrespondenceFunctorialityTarget ctx realization)
    (locTarget : GeometricOpenClosedLocalizationTarget ctx realization)
    (nisTarget : GeometricNisnevichDescentTarget ctx realization)
    (a1Target : GeometricA1InvarianceTarget ctx realization)
    (envTarget : GeometricEnvelopeExactnessTarget ctx realization)
    (tateTarget : GeometricTateStabilizationTarget ctx realization)
    (generatorCoverageTarget assignmentCompatibilityTarget motivicRecognitionInterfaceTarget : Prop) :
    (ofAssignments realization corrAssignment locAssignment nisAssignment a1Assignment envAssignment
      corrTarget locTarget nisTarget a1Target envTarget tateTarget generatorCoverageTarget
      assignmentCompatibilityTarget motivicRecognitionInterfaceTarget).a1Target = a1Target := rfl

@[simp] theorem ofAssignments_envTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (realization : GeometricRealizationFunctorData ctx)
    (corrAssignment : CorrGeneratorRealizationAssignment ctx realization)
    (locAssignment : LocGeneratorRealizationAssignment ctx realization)
    (nisAssignment : NisGeneratorRealizationAssignment ctx realization)
    (a1Assignment : A1GeneratorRealizationAssignment ctx realization)
    (envAssignment : EnvGeneratorRealizationAssignment ctx realization)
    (corrTarget : GeometricCorrespondenceFunctorialityTarget ctx realization)
    (locTarget : GeometricOpenClosedLocalizationTarget ctx realization)
    (nisTarget : GeometricNisnevichDescentTarget ctx realization)
    (a1Target : GeometricA1InvarianceTarget ctx realization)
    (envTarget : GeometricEnvelopeExactnessTarget ctx realization)
    (tateTarget : GeometricTateStabilizationTarget ctx realization)
    (generatorCoverageTarget assignmentCompatibilityTarget motivicRecognitionInterfaceTarget : Prop) :
    (ofAssignments realization corrAssignment locAssignment nisAssignment a1Assignment envAssignment
      corrTarget locTarget nisTarget a1Target envTarget tateTarget generatorCoverageTarget
      assignmentCompatibilityTarget motivicRecognitionInterfaceTarget).envTarget = envTarget := rfl

@[simp] theorem ofAssignments_generatorCoverageTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (realization : GeometricRealizationFunctorData ctx)
    (corrAssignment : CorrGeneratorRealizationAssignment ctx realization)
    (locAssignment : LocGeneratorRealizationAssignment ctx realization)
    (nisAssignment : NisGeneratorRealizationAssignment ctx realization)
    (a1Assignment : A1GeneratorRealizationAssignment ctx realization)
    (envAssignment : EnvGeneratorRealizationAssignment ctx realization)
    (corrTarget : GeometricCorrespondenceFunctorialityTarget ctx realization)
    (locTarget : GeometricOpenClosedLocalizationTarget ctx realization)
    (nisTarget : GeometricNisnevichDescentTarget ctx realization)
    (a1Target : GeometricA1InvarianceTarget ctx realization)
    (envTarget : GeometricEnvelopeExactnessTarget ctx realization)
    (tateTarget : GeometricTateStabilizationTarget ctx realization)
    (generatorCoverageTarget assignmentCompatibilityTarget motivicRecognitionInterfaceTarget : Prop) :
    (ofAssignments realization corrAssignment locAssignment nisAssignment a1Assignment envAssignment
      corrTarget locTarget nisTarget a1Target envTarget tateTarget generatorCoverageTarget
      assignmentCompatibilityTarget motivicRecognitionInterfaceTarget).generatorCoverageTarget =
        generatorCoverageTarget := rfl

@[simp] theorem ofAssignments_assignmentCompatibilityTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (realization : GeometricRealizationFunctorData ctx)
    (corrAssignment : CorrGeneratorRealizationAssignment ctx realization)
    (locAssignment : LocGeneratorRealizationAssignment ctx realization)
    (nisAssignment : NisGeneratorRealizationAssignment ctx realization)
    (a1Assignment : A1GeneratorRealizationAssignment ctx realization)
    (envAssignment : EnvGeneratorRealizationAssignment ctx realization)
    (corrTarget : GeometricCorrespondenceFunctorialityTarget ctx realization)
    (locTarget : GeometricOpenClosedLocalizationTarget ctx realization)
    (nisTarget : GeometricNisnevichDescentTarget ctx realization)
    (a1Target : GeometricA1InvarianceTarget ctx realization)
    (envTarget : GeometricEnvelopeExactnessTarget ctx realization)
    (tateTarget : GeometricTateStabilizationTarget ctx realization)
    (generatorCoverageTarget assignmentCompatibilityTarget motivicRecognitionInterfaceTarget : Prop) :
    (ofAssignments realization corrAssignment locAssignment nisAssignment a1Assignment envAssignment
      corrTarget locTarget nisTarget a1Target envTarget tateTarget generatorCoverageTarget
      assignmentCompatibilityTarget motivicRecognitionInterfaceTarget).assignmentCompatibilityTarget =
        assignmentCompatibilityTarget := rfl

@[simp] theorem ofAssignments_motivicRecognitionInterfaceTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (realization : GeometricRealizationFunctorData ctx)
    (corrAssignment : CorrGeneratorRealizationAssignment ctx realization)
    (locAssignment : LocGeneratorRealizationAssignment ctx realization)
    (nisAssignment : NisGeneratorRealizationAssignment ctx realization)
    (a1Assignment : A1GeneratorRealizationAssignment ctx realization)
    (envAssignment : EnvGeneratorRealizationAssignment ctx realization)
    (corrTarget : GeometricCorrespondenceFunctorialityTarget ctx realization)
    (locTarget : GeometricOpenClosedLocalizationTarget ctx realization)
    (nisTarget : GeometricNisnevichDescentTarget ctx realization)
    (a1Target : GeometricA1InvarianceTarget ctx realization)
    (envTarget : GeometricEnvelopeExactnessTarget ctx realization)
    (tateTarget : GeometricTateStabilizationTarget ctx realization)
    (generatorCoverageTarget assignmentCompatibilityTarget motivicRecognitionInterfaceTarget : Prop) :
    (ofAssignments realization corrAssignment locAssignment nisAssignment a1Assignment envAssignment
      corrTarget locTarget nisTarget a1Target envTarget tateTarget generatorCoverageTarget
      assignmentCompatibilityTarget motivicRecognitionInterfaceTarget).motivicRecognitionInterfaceTarget =
        motivicRecognitionInterfaceTarget := rfl

/-- Forget the assignment table to the named generator-family package. -/
def toGeometricGeneratorFamilyPackage
    {ctx : ClassicalComparisonContext.{u, v}}
    (table : GeneratorRealizationAssignmentTable ctx) : GeometricGeneratorFamilyPackage ctx where
  realization := table.realization
  corrFamily := table.corrAssignment.family
  locFamily := table.locAssignment.family
  nisFamily := table.nisAssignment.family
  a1Family := table.a1Assignment.family
  envFamily := table.envAssignment.family
  corrTarget := table.corrTarget
  locTarget := table.locTarget
  nisTarget := table.nisTarget
  a1Target := table.a1Target
  envTarget := table.envTarget
  tateTarget := table.tateTarget
  generatorCoverageTarget := table.generatorCoverageTarget
  realizationCompatibilityTarget := table.assignmentCompatibilityTarget
  motivicRecognitionInterfaceTarget := table.motivicRecognitionInterfaceTarget

/-- Forget the assignment table to the localization/descent package. -/
def toGeometricLocalizationPackage
    {ctx : ClassicalComparisonContext.{u, v}}
    (table : GeneratorRealizationAssignmentTable ctx) : GeometricLocalizationPackage ctx :=
  (table.toGeometricGeneratorFamilyPackage).toGeometricLocalizationPackage

/-- Assignment-table bridge into the motivic-readiness interface. -/
def toClassicalMotivicRealizationReadiness
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (table : GeneratorRealizationAssignmentTable ctx)
    (tomography : GeometricRealizationTomographySoundness ctx structuredEq)
    (hrealization : table.realization = tomography.geometricRealizationFunctor) :
    ClassicalMotivicRealizationReadiness ctx structuredEq :=
  (table.toGeometricGeneratorFamilyPackage).toClassicalMotivicRealizationReadiness tomography hrealization

/-! ### Projection lemmas for the assignment-table forgetful chain.

These are pure record-projection identities that let downstream code rewrite the assignment
table's named families and theorem targets through the family/localization packages without
unfolding the forgetful definitions. -/

@[simp] theorem toGeometricGeneratorFamilyPackage_realization
    {ctx : ClassicalComparisonContext.{u, v}}
    (table : GeneratorRealizationAssignmentTable ctx) :
    (table.toGeometricGeneratorFamilyPackage).realization = table.realization := rfl

@[simp] theorem toGeometricGeneratorFamilyPackage_corrFamily
    {ctx : ClassicalComparisonContext.{u, v}}
    (table : GeneratorRealizationAssignmentTable ctx) :
    (table.toGeometricGeneratorFamilyPackage).corrFamily = table.corrAssignment.family := rfl

@[simp] theorem toGeometricGeneratorFamilyPackage_locFamily
    {ctx : ClassicalComparisonContext.{u, v}}
    (table : GeneratorRealizationAssignmentTable ctx) :
    (table.toGeometricGeneratorFamilyPackage).locFamily = table.locAssignment.family := rfl

@[simp] theorem toGeometricGeneratorFamilyPackage_nisFamily
    {ctx : ClassicalComparisonContext.{u, v}}
    (table : GeneratorRealizationAssignmentTable ctx) :
    (table.toGeometricGeneratorFamilyPackage).nisFamily = table.nisAssignment.family := rfl

@[simp] theorem toGeometricGeneratorFamilyPackage_a1Family
    {ctx : ClassicalComparisonContext.{u, v}}
    (table : GeneratorRealizationAssignmentTable ctx) :
    (table.toGeometricGeneratorFamilyPackage).a1Family = table.a1Assignment.family := rfl

@[simp] theorem toGeometricGeneratorFamilyPackage_envFamily
    {ctx : ClassicalComparisonContext.{u, v}}
    (table : GeneratorRealizationAssignmentTable ctx) :
    (table.toGeometricGeneratorFamilyPackage).envFamily = table.envAssignment.family := rfl

@[simp] theorem toGeometricGeneratorFamilyPackage_corrTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (table : GeneratorRealizationAssignmentTable ctx) :
    (table.toGeometricGeneratorFamilyPackage).corrTarget = table.corrTarget := rfl

@[simp] theorem toGeometricGeneratorFamilyPackage_locTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (table : GeneratorRealizationAssignmentTable ctx) :
    (table.toGeometricGeneratorFamilyPackage).locTarget = table.locTarget := rfl

@[simp] theorem toGeometricGeneratorFamilyPackage_nisTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (table : GeneratorRealizationAssignmentTable ctx) :
    (table.toGeometricGeneratorFamilyPackage).nisTarget = table.nisTarget := rfl

@[simp] theorem toGeometricGeneratorFamilyPackage_a1Target
    {ctx : ClassicalComparisonContext.{u, v}}
    (table : GeneratorRealizationAssignmentTable ctx) :
    (table.toGeometricGeneratorFamilyPackage).a1Target = table.a1Target := rfl

@[simp] theorem toGeometricGeneratorFamilyPackage_envTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (table : GeneratorRealizationAssignmentTable ctx) :
    (table.toGeometricGeneratorFamilyPackage).envTarget = table.envTarget := rfl

@[simp] theorem toGeometricGeneratorFamilyPackage_tateTarget
  {ctx : ClassicalComparisonContext.{u, v}}
  (table : GeneratorRealizationAssignmentTable ctx) :
  (table.toGeometricGeneratorFamilyPackage).tateTarget = table.tateTarget := rfl

@[simp] theorem toGeometricGeneratorFamilyPackage_generatorCoverageTarget
  {ctx : ClassicalComparisonContext.{u, v}}
  (table : GeneratorRealizationAssignmentTable ctx) :
  (table.toGeometricGeneratorFamilyPackage).generatorCoverageTarget = table.generatorCoverageTarget := rfl

@[simp] theorem toGeometricGeneratorFamilyPackage_realizationCompatibilityTarget
  {ctx : ClassicalComparisonContext.{u, v}}
  (table : GeneratorRealizationAssignmentTable ctx) :
  (table.toGeometricGeneratorFamilyPackage).realizationCompatibilityTarget =
    table.assignmentCompatibilityTarget := rfl

@[simp] theorem toGeometricGeneratorFamilyPackage_motivicRecognitionInterfaceTarget
  {ctx : ClassicalComparisonContext.{u, v}}
  (table : GeneratorRealizationAssignmentTable ctx) :
  (table.toGeometricGeneratorFamilyPackage).motivicRecognitionInterfaceTarget =
    table.motivicRecognitionInterfaceTarget := rfl

@[simp] theorem toGeometricLocalizationPackage_realization
    {ctx : ClassicalComparisonContext.{u, v}}
    (table : GeneratorRealizationAssignmentTable ctx) :
    (table.toGeometricLocalizationPackage).realization = table.realization := rfl

@[simp] theorem toGeometricLocalizationPackage_a1Invariance
    {ctx : ClassicalComparisonContext.{u, v}}
    (table : GeneratorRealizationAssignmentTable ctx) :
    (table.toGeometricLocalizationPackage).a1Invariance = table.a1Target := rfl

@[simp] theorem toGeometricLocalizationPackage_nisnevichDescent
    {ctx : ClassicalComparisonContext.{u, v}}
    (table : GeneratorRealizationAssignmentTable ctx) :
    (table.toGeometricLocalizationPackage).nisnevichDescent = table.nisTarget := rfl

@[simp] theorem toGeometricLocalizationPackage_openClosedLocalization
    {ctx : ClassicalComparisonContext.{u, v}}
    (table : GeneratorRealizationAssignmentTable ctx) :
    (table.toGeometricLocalizationPackage).openClosedLocalization = table.locTarget := rfl

@[simp] theorem toGeometricLocalizationPackage_tateStabilization
  {ctx : ClassicalComparisonContext.{u, v}}
  (table : GeneratorRealizationAssignmentTable ctx) :
  (table.toGeometricLocalizationPackage).tateStabilization = table.tateTarget := rfl

@[simp] theorem toGeometricLocalizationPackage_correspondenceFunctoriality
    {ctx : ClassicalComparisonContext.{u, v}}
    (table : GeneratorRealizationAssignmentTable ctx) :
    (table.toGeometricLocalizationPackage).correspondenceFunctoriality = table.corrTarget := rfl

@[simp] theorem toGeometricLocalizationPackage_envelopeExactness
    {ctx : ClassicalComparisonContext.{u, v}}
    (table : GeneratorRealizationAssignmentTable ctx) :
    (table.toGeometricLocalizationPackage).envelopeExactness = table.envTarget := rfl

@[simp] theorem toGeometricLocalizationPackage_realizationCompatibilityTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (table : GeneratorRealizationAssignmentTable ctx) :
    (table.toGeometricLocalizationPackage).realizationCompatibilityTarget =
  (table.generatorCoverageTarget ∧ table.assignmentCompatibilityTarget) := rfl

@[simp] theorem toGeometricLocalizationPackage_motivicRecognitionInterfaceTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (table : GeneratorRealizationAssignmentTable ctx) :
    (table.toGeometricLocalizationPackage).motivicRecognitionInterfaceTarget =
      table.motivicRecognitionInterfaceTarget := rfl

@[simp] theorem toClassicalMotivicRealizationReadiness_localizationPackage
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (table : GeneratorRealizationAssignmentTable ctx)
    (tomography : GeometricRealizationTomographySoundness ctx structuredEq)
    (hrealization : table.realization = tomography.geometricRealizationFunctor) :
    (table.toClassicalMotivicRealizationReadiness tomography hrealization).localizationPackage =
      table.toGeometricLocalizationPackage := rfl

@[simp] theorem toClassicalMotivicRealizationReadiness_tomographySoundness
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (table : GeneratorRealizationAssignmentTable ctx)
    (tomography : GeometricRealizationTomographySoundness ctx structuredEq)
    (hrealization : table.realization = tomography.geometricRealizationFunctor) :
    (table.toClassicalMotivicRealizationReadiness tomography hrealization).tomographySoundness =
      tomography := rfl

end GeneratorRealizationAssignmentTable

end ClassicalPeriods
end TraceCalc