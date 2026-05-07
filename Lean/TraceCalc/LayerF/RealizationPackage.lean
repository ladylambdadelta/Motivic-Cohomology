import TraceCalc.LayerE.TargetComparisonPackage

universe u v w x y z

namespace TraceCalc
namespace LayerF

/-- Abstract structured-realization comparison data. This records only the carrier surfaces and
the theorem obligations needed to build the Layer D structured realization package; no concrete
Betti/de Rham construction is attempted here. -/
structure AbstractStructuredComparisonData
    (A : LayerE.AbstractMotivicTargetAxioms.{u, v})
    (targetData : LayerE.TargetRecognitionInputData A)
    (comparisonData : LayerE.ComparisonInputData A targetData.infinityAxioms) where
  BettiLikeCarrier : Type w
  DeRhamLikeCarrier : Type x
  comparisonMap : BettiLikeCarrier → DeRhamLikeCarrier → Prop
  comparisonIsomorphism : Prop
  comparisonIsomorphism_holds : comparisonIsomorphism
  bettiLikeFunctoriality : Prop
  bettiLikeFunctoriality_holds : bettiLikeFunctoriality
  deRhamLikeFunctoriality : Prop
  deRhamLikeFunctoriality_holds : deRhamLikeFunctoriality
  comparisonMapFunctorial : Prop
  comparisonMapFunctorial_holds : comparisonMapFunctorial
  compatibleWithSourcePackage : Prop
  compatibleWithSourcePackage_holds : compatibleWithSourcePackage
  compatibleWithTargetPackage : Prop
  compatibleWithTargetPackage_holds : compatibleWithTargetPackage
  compatibleWithComparisonPackage : Prop
  compatibleWithComparisonPackage_holds : compatibleWithComparisonPackage
  realizationFunctorsInfinity : Prop
  realizationFunctorsInfinity_holds : realizationFunctorsInfinity
  realizationFunctorsPiZero : Prop
  realizationFunctorsPiZero_holds : realizationFunctorsPiZero
  structuredFaithfulness : Prop
  structuredFaithfulness_holds : structuredFaithfulness

/-- Abstract scalar-shadow data extracted from the structured comparison layer. This keeps the
scalar period map and reflection theorem surfaces explicit, but abstract. -/
structure AbstractScalarShadowData
    {A : LayerE.AbstractMotivicTargetAxioms.{u, v}}
    {targetData : LayerE.TargetRecognitionInputData A}
    {comparisonData : LayerE.ComparisonInputData A targetData.infinityAxioms}
    (structuredData : AbstractStructuredComparisonData A targetData comparisonData) where
  ScalarCarrier : Type y
  scalarPeriodMap : structuredData.BettiLikeCarrier → structuredData.DeRhamLikeCarrier → ScalarCarrier
  extractedFromStructuredData : Prop
  extractedFromStructuredData_holds : extractedFromStructuredData
  scalarPeriodMapFunctorial : Prop
  scalarPeriodMapFunctorial_holds : scalarPeriodMapFunctorial
  compatibleWithStructuredPackage : Prop
  compatibleWithStructuredPackage_holds : compatibleWithStructuredPackage
  scalarReflectsStructured : Prop
  scalarReflectsStructured_holds : scalarReflectsStructured
  scalarShadowExtraction : Prop
  scalarShadowExtraction_holds : scalarShadowExtraction

/-- Exact input surface needed to build the existing Layer D structured realization package. -/
structure StructuredRealizationInputData
    (A : LayerE.AbstractMotivicTargetAxioms.{u, v}) where
  targetData : LayerE.TargetRecognitionInputData A
  comparisonData : LayerE.ComparisonInputData A targetData.infinityAxioms
  structuredData : AbstractStructuredComparisonData A targetData comparisonData

/-- Exact input surface needed to build the existing Layer D scalar-shadow package. -/
structure ScalarShadowInputData
    (A : LayerE.AbstractMotivicTargetAxioms.{u, v}) where
  structuredInput : StructuredRealizationInputData A
  scalarData : AbstractScalarShadowData structuredInput.structuredData

end LayerF

namespace LayerD
namespace StructuredRealizationPackage

def ofAbstractStructuredComparisonData
    {A : LayerE.AbstractMotivicTargetAxioms.{u, v}}
    (data : LayerF.StructuredRealizationInputData A) : TraceCalc.LayerD.StructuredRealizationPackage where
  realizationFunctorsPiZero := data.structuredData.realizationFunctorsPiZero
  realizationFunctorsPiZero_holds := data.structuredData.realizationFunctorsPiZero_holds
  realizationFunctorsInfinity := data.structuredData.realizationFunctorsInfinity
  realizationFunctorsInfinity_holds := data.structuredData.realizationFunctorsInfinity_holds
  structuredRealizationConsequence := data.structuredData.structuredFaithfulness
  structuredRealizationConsequence_holds := data.structuredData.structuredFaithfulness_holds

theorem constructed_structured_package_realizes_structuredBridge
    {A : LayerE.AbstractMotivicTargetAxioms.{u, v}}
    (data : LayerF.StructuredRealizationInputData A) :
    ((ofAbstractStructuredComparisonData data).package_gives_structuredRealizationBridgeReady).stageName =
        TraceCalc.LayerD.StructuredRealizationBridgeReady.stageName ∧
      ((ofAbstractStructuredComparisonData data).package_gives_structuredRealizationBridgeReady).availableStages =
        [ TraceCalc.LayerD.ComparisonFactorizationReady.stageName
        , TraceCalc.LayerD.InfinityComparisonReady.stageName
        ] ∧
      ∀ obligationId : TraceCalc.LayerD.MotivicObligationId,
        ((ofAbstractStructuredComparisonData data).package_gives_structuredRealizationBridgeReady).supportsObligationId
            obligationId ↔
          (ofAbstractStructuredComparisonData data).SupportsObligationId obligationId := by
  simpa using
    structuredPackage_realizes_exactly_structuredBridge
      (P := ofAbstractStructuredComparisonData data)

end StructuredRealizationPackage

namespace ScalarShadowExtractionPackage

def ofAbstractScalarShadowData
    {A : LayerE.AbstractMotivicTargetAxioms.{u, v}}
    (data : LayerF.ScalarShadowInputData A) : TraceCalc.LayerD.ScalarShadowExtractionPackage where
  scalarShadowExtraction := data.scalarData.scalarShadowExtraction
  scalarShadowExtraction_holds := data.scalarData.scalarShadowExtraction_holds

theorem constructed_scalar_package_realizes_scalarShadow
    {A : LayerE.AbstractMotivicTargetAxioms.{u, v}}
    (data : LayerF.ScalarShadowInputData A) :
    ((ofAbstractScalarShadowData data).package_gives_scalarShadowConsequenceReady).stageName =
        TraceCalc.LayerD.ScalarShadowConsequenceReady.stageName ∧
      ((ofAbstractScalarShadowData data).package_gives_scalarShadowConsequenceReady).availableStages =
        [TraceCalc.LayerD.StructuredRealizationBridgeReady.stageName] ∧
      ∀ obligationId : TraceCalc.LayerD.MotivicObligationId,
        ((ofAbstractScalarShadowData data).package_gives_scalarShadowConsequenceReady).supportsObligationId
            obligationId ↔
          (ofAbstractScalarShadowData data).SupportsObligationId obligationId := by
  simpa using
    scalarPackage_realizes_exactly_scalarShadow (P := ofAbstractScalarShadowData data)

end ScalarShadowExtractionPackage
end LayerD

namespace LayerF

/-- One-shot Layer F input surface for building the remaining structured/scalar packages used by
the final period-faithfulness assembly. -/
structure RealizationAndScalarInputData
    (A : LayerE.AbstractMotivicTargetAxioms.{u, v}) where
  structuredInput : StructuredRealizationInputData A
  scalarInput : ScalarShadowInputData A

/-- Structured comparison theorem package for the period-realization lane. -/
structure StructuredComparisonTheoremPackage where
  BettiLikeCarrier : Type w
  DeRhamLikeCarrier : Type x
  comparisonMap : BettiLikeCarrier → DeRhamLikeCarrier → Prop
  bettiLikeFunctoriality : Prop
  bettiLikeFunctoriality_holds : bettiLikeFunctoriality
  deRhamLikeFunctoriality : Prop
  deRhamLikeFunctoriality_holds : deRhamLikeFunctoriality
  comparisonMapFunctorial : Prop
  comparisonMapFunctorial_holds : comparisonMapFunctorial
  compatibleWithSourcePackage : Prop
  compatibleWithSourcePackage_holds : compatibleWithSourcePackage
  compatibleWithTargetPackage : Prop
  compatibleWithTargetPackage_holds : compatibleWithTargetPackage
  compatibleWithComparisonPackage : Prop
  compatibleWithComparisonPackage_holds : compatibleWithComparisonPackage
  realizationFunctorsInfinity : Prop
  realizationFunctorsInfinity_holds : realizationFunctorsInfinity
  realizationFunctorsPiZero : Prop
  realizationFunctorsPiZero_holds : realizationFunctorsPiZero

/-- Comparison-isomorphism theorem package for the period-realization lane. -/
structure ComparisonIsomorphismTheoremPackage where
  comparisonIsomorphism : Prop
  comparisonIsomorphism_holds : comparisonIsomorphism

/-- Structured-faithfulness theorem package for the period-realization lane. -/
structure StructuredFaithfulnessTheoremPackage where
  structuredFaithfulness : Prop
  structuredFaithfulness_holds : structuredFaithfulness

/-- Scalar period-map theorem package for the period-realization lane. -/
structure ScalarPeriodMapTheoremPackage
    (structuredComparison : StructuredComparisonTheoremPackage.{w, x}) where
  ScalarCarrier : Type y
  scalarPeriodMap :
    structuredComparison.BettiLikeCarrier → structuredComparison.DeRhamLikeCarrier → ScalarCarrier
  scalarPeriodMapFunctorial : Prop
  scalarPeriodMapFunctorial_holds : scalarPeriodMapFunctorial

/-- Scalar extraction theorem package for the period-realization lane. -/
structure ScalarExtractionTheoremPackage where
  extractedFromStructuredData : Prop
  extractedFromStructuredData_holds : extractedFromStructuredData
  compatibleWithStructuredPackage : Prop
  compatibleWithStructuredPackage_holds : compatibleWithStructuredPackage
  scalarShadowExtraction : Prop
  scalarShadowExtraction_holds : scalarShadowExtraction

/-- Scalar-reflects-structured theorem package for the period-realization lane. -/
structure ScalarReflectsStructuredTheoremPackage where
  scalarReflectsStructured : Prop
  scalarReflectsStructured_holds : scalarReflectsStructured

/-- Implementation-facing theorem ticket for the structured comparison lane. This sharpens the
carrier/map/functoriality package by bundling the comparison-isomorphism and structured-faithfulness
obligations that together feed the Layer F structured realization package. -/
structure StructuredComparisonImplementationTicket where
  BettiLikeCarrier : Type w
  DeRhamLikeCarrier : Type x
  comparisonMap : BettiLikeCarrier → DeRhamLikeCarrier → Prop
  comparisonIsomorphism : Prop
  comparisonIsomorphism_holds : comparisonIsomorphism
  bettiLikeFunctoriality : Prop
  bettiLikeFunctoriality_holds : bettiLikeFunctoriality
  deRhamLikeFunctoriality : Prop
  deRhamLikeFunctoriality_holds : deRhamLikeFunctoriality
  comparisonMapFunctorial : Prop
  comparisonMapFunctorial_holds : comparisonMapFunctorial
  compatibleWithSourcePackage : Prop
  compatibleWithSourcePackage_holds : compatibleWithSourcePackage
  compatibleWithTargetPackage : Prop
  compatibleWithTargetPackage_holds : compatibleWithTargetPackage
  compatibleWithComparisonPackage : Prop
  compatibleWithComparisonPackage_holds : compatibleWithComparisonPackage
  realizationFunctorsInfinity : Prop
  realizationFunctorsInfinity_holds : realizationFunctorsInfinity
  realizationFunctorsPiZero : Prop
  realizationFunctorsPiZero_holds : realizationFunctorsPiZero
  structuredFaithfulness : Prop
  structuredFaithfulness_holds : structuredFaithfulness

/-- Subordinate theorem data recording the functoriality side of a J.1 implementation.
This isolates the still-abstract naturality and realization-functor obligations from the core
comparison-isomorphism proof. -/
structure StructuredComparisonFunctorialityData
    (BettiLikeCarrier : Type w)
    (DeRhamLikeCarrier : Type x)
    (comparisonMap : BettiLikeCarrier → DeRhamLikeCarrier → Prop) where
  bettiLikeFunctoriality : Prop
  bettiLikeFunctoriality_holds : bettiLikeFunctoriality
  deRhamLikeFunctoriality : Prop
  deRhamLikeFunctoriality_holds : deRhamLikeFunctoriality
  comparisonMapFunctorial : Prop
  comparisonMapFunctorial_holds : comparisonMapFunctorial
  realizationFunctorsInfinity : Prop
  realizationFunctorsInfinity_holds : realizationFunctorsInfinity
  realizationFunctorsPiZero : Prop
  realizationFunctorsPiZero_holds : realizationFunctorsPiZero

/-- Subordinate theorem data recording package-compatibility and structured-faithfulness for a J.1
implementation. This keeps those obligations explicit without strengthening the main ticket. -/
structure StructuredComparisonCompatibilityData where
  compatibleWithSourcePackage : Prop
  compatibleWithSourcePackage_holds : compatibleWithSourcePackage
  compatibleWithTargetPackage : Prop
  compatibleWithTargetPackage_holds : compatibleWithTargetPackage
  compatibleWithComparisonPackage : Prop
  compatibleWithComparisonPackage_holds : compatibleWithComparisonPackage
  structuredFaithfulness : Prop
  structuredFaithfulness_holds : structuredFaithfulness

namespace StructuredComparisonImplementationTicket

/-- Minimal J.1 constructor from carrier/map data plus a comparison-isomorphism proof.
The remaining functoriality and compatibility obligations are supplied as subordinate theorem data
rather than being re-encoded in a new ticket shape. -/
def ofComparisonIsoData
    (BettiLikeCarrier : Type w)
    (DeRhamLikeCarrier : Type x)
    (comparisonMap : BettiLikeCarrier → DeRhamLikeCarrier → Prop)
    (comparisonIsomorphism : Prop)
    (comparisonIsomorphism_holds : comparisonIsomorphism)
    (functorialityData : StructuredComparisonFunctorialityData
      BettiLikeCarrier DeRhamLikeCarrier comparisonMap)
    (compatibilityData : StructuredComparisonCompatibilityData) :
    StructuredComparisonImplementationTicket.{w, x} where
  BettiLikeCarrier := BettiLikeCarrier
  DeRhamLikeCarrier := DeRhamLikeCarrier
  comparisonMap := comparisonMap
  comparisonIsomorphism := comparisonIsomorphism
  comparisonIsomorphism_holds := comparisonIsomorphism_holds
  bettiLikeFunctoriality := functorialityData.bettiLikeFunctoriality
  bettiLikeFunctoriality_holds := functorialityData.bettiLikeFunctoriality_holds
  deRhamLikeFunctoriality := functorialityData.deRhamLikeFunctoriality
  deRhamLikeFunctoriality_holds := functorialityData.deRhamLikeFunctoriality_holds
  comparisonMapFunctorial := functorialityData.comparisonMapFunctorial
  comparisonMapFunctorial_holds := functorialityData.comparisonMapFunctorial_holds
  compatibleWithSourcePackage := compatibilityData.compatibleWithSourcePackage
  compatibleWithSourcePackage_holds := compatibilityData.compatibleWithSourcePackage_holds
  compatibleWithTargetPackage := compatibilityData.compatibleWithTargetPackage
  compatibleWithTargetPackage_holds := compatibilityData.compatibleWithTargetPackage_holds
  compatibleWithComparisonPackage := compatibilityData.compatibleWithComparisonPackage
  compatibleWithComparisonPackage_holds := compatibilityData.compatibleWithComparisonPackage_holds
  realizationFunctorsInfinity := functorialityData.realizationFunctorsInfinity
  realizationFunctorsInfinity_holds := functorialityData.realizationFunctorsInfinity_holds
  realizationFunctorsPiZero := functorialityData.realizationFunctorsPiZero
  realizationFunctorsPiZero_holds := functorialityData.realizationFunctorsPiZero_holds
  structuredFaithfulness := compatibilityData.structuredFaithfulness
  structuredFaithfulness_holds := compatibilityData.structuredFaithfulness_holds

/-- The current sharp J.1 ticket records the explicit structured comparison data and the theorem
obligations that let it feed the structured realization package. -/
def theoremTarget
    (T : StructuredComparisonImplementationTicket.{w, x}) : Prop :=
  T.comparisonIsomorphism ∧
    T.bettiLikeFunctoriality ∧
    T.deRhamLikeFunctoriality ∧
    T.comparisonMapFunctorial ∧
    T.compatibleWithSourcePackage ∧
    T.compatibleWithTargetPackage ∧
    T.compatibleWithComparisonPackage ∧
    T.realizationFunctorsInfinity ∧
    T.realizationFunctorsPiZero ∧
    T.structuredFaithfulness

theorem theoremTarget_holds
    (T : StructuredComparisonImplementationTicket.{w, x}) : T.theoremTarget := by
  exact ⟨T.comparisonIsomorphism_holds, T.bettiLikeFunctoriality_holds,
    T.deRhamLikeFunctoriality_holds, T.comparisonMapFunctorial_holds,
    T.compatibleWithSourcePackage_holds, T.compatibleWithTargetPackage_holds,
    T.compatibleWithComparisonPackage_holds, T.realizationFunctorsInfinity_holds,
    T.realizationFunctorsPiZero_holds, T.structuredFaithfulness_holds⟩

theorem ofComparisonIsoData_supplies_ticket
    (BettiLikeCarrier : Type w)
    (DeRhamLikeCarrier : Type x)
    (comparisonMap : BettiLikeCarrier → DeRhamLikeCarrier → Prop)
    (comparisonIsomorphism : Prop)
    (comparisonIsomorphism_holds : comparisonIsomorphism)
    (functorialityData : StructuredComparisonFunctorialityData
      BettiLikeCarrier DeRhamLikeCarrier comparisonMap)
    (compatibilityData : StructuredComparisonCompatibilityData) :
    (ofComparisonIsoData BettiLikeCarrier DeRhamLikeCarrier comparisonMap
      comparisonIsomorphism comparisonIsomorphism_holds
      functorialityData compatibilityData).theoremTarget := by
  exact theoremTarget_holds _

def toStructuredComparisonTheoremPackage
    (T : StructuredComparisonImplementationTicket.{w, x}) :
    StructuredComparisonTheoremPackage.{w, x} where
  BettiLikeCarrier := T.BettiLikeCarrier
  DeRhamLikeCarrier := T.DeRhamLikeCarrier
  comparisonMap := T.comparisonMap
  bettiLikeFunctoriality := T.bettiLikeFunctoriality
  bettiLikeFunctoriality_holds := T.bettiLikeFunctoriality_holds
  deRhamLikeFunctoriality := T.deRhamLikeFunctoriality
  deRhamLikeFunctoriality_holds := T.deRhamLikeFunctoriality_holds
  comparisonMapFunctorial := T.comparisonMapFunctorial
  comparisonMapFunctorial_holds := T.comparisonMapFunctorial_holds
  compatibleWithSourcePackage := T.compatibleWithSourcePackage
  compatibleWithSourcePackage_holds := T.compatibleWithSourcePackage_holds
  compatibleWithTargetPackage := T.compatibleWithTargetPackage
  compatibleWithTargetPackage_holds := T.compatibleWithTargetPackage_holds
  compatibleWithComparisonPackage := T.compatibleWithComparisonPackage
  compatibleWithComparisonPackage_holds := T.compatibleWithComparisonPackage_holds
  realizationFunctorsInfinity := T.realizationFunctorsInfinity
  realizationFunctorsInfinity_holds := T.realizationFunctorsInfinity_holds
  realizationFunctorsPiZero := T.realizationFunctorsPiZero
  realizationFunctorsPiZero_holds := T.realizationFunctorsPiZero_holds

def toComparisonIsomorphismTheoremPackage
    (T : StructuredComparisonImplementationTicket.{w, x}) :
    ComparisonIsomorphismTheoremPackage where
  comparisonIsomorphism := T.comparisonIsomorphism
  comparisonIsomorphism_holds := T.comparisonIsomorphism_holds

def toStructuredFaithfulnessTheoremPackage
    (T : StructuredComparisonImplementationTicket.{w, x}) :
    StructuredFaithfulnessTheoremPackage where
  structuredFaithfulness := T.structuredFaithfulness
  structuredFaithfulness_holds := T.structuredFaithfulness_holds

def toAbstractStructuredComparisonData
    {A : LayerE.AbstractMotivicTargetAxioms.{u, v}}
    (targetData : LayerE.TargetRecognitionInputData A)
    (comparisonData : LayerE.ComparisonInputData A targetData.infinityAxioms)
    (T : StructuredComparisonImplementationTicket.{w, x}) :
    AbstractStructuredComparisonData A targetData comparisonData where
  BettiLikeCarrier := T.BettiLikeCarrier
  DeRhamLikeCarrier := T.DeRhamLikeCarrier
  comparisonMap := T.comparisonMap
  comparisonIsomorphism := T.comparisonIsomorphism
  comparisonIsomorphism_holds := T.comparisonIsomorphism_holds
  bettiLikeFunctoriality := T.bettiLikeFunctoriality
  bettiLikeFunctoriality_holds := T.bettiLikeFunctoriality_holds
  deRhamLikeFunctoriality := T.deRhamLikeFunctoriality
  deRhamLikeFunctoriality_holds := T.deRhamLikeFunctoriality_holds
  comparisonMapFunctorial := T.comparisonMapFunctorial
  comparisonMapFunctorial_holds := T.comparisonMapFunctorial_holds
  compatibleWithSourcePackage := T.compatibleWithSourcePackage
  compatibleWithSourcePackage_holds := T.compatibleWithSourcePackage_holds
  compatibleWithTargetPackage := T.compatibleWithTargetPackage
  compatibleWithTargetPackage_holds := T.compatibleWithTargetPackage_holds
  compatibleWithComparisonPackage := T.compatibleWithComparisonPackage
  compatibleWithComparisonPackage_holds := T.compatibleWithComparisonPackage_holds
  realizationFunctorsInfinity := T.realizationFunctorsInfinity
  realizationFunctorsInfinity_holds := T.realizationFunctorsInfinity_holds
  realizationFunctorsPiZero := T.realizationFunctorsPiZero
  realizationFunctorsPiZero_holds := T.realizationFunctorsPiZero_holds
  structuredFaithfulness := T.structuredFaithfulness
  structuredFaithfulness_holds := T.structuredFaithfulness_holds

def toStructuredRealizationInputData
    {A : LayerE.AbstractMotivicTargetAxioms.{u, v}}
    (targetData : LayerE.TargetRecognitionInputData A)
    (comparisonData : LayerE.ComparisonInputData A targetData.infinityAxioms)
    (T : StructuredComparisonImplementationTicket.{w, x}) :
    StructuredRealizationInputData A where
  targetData := targetData
  comparisonData := comparisonData
  structuredData := T.toAbstractStructuredComparisonData targetData comparisonData

theorem supplies_structuredRealizationPackage
    {A : LayerE.AbstractMotivicTargetAxioms.{u, v}}
    (targetData : LayerE.TargetRecognitionInputData A)
    (comparisonData : LayerE.ComparisonInputData A targetData.infinityAxioms)
    (T : StructuredComparisonImplementationTicket.{w, x}) :
    (LayerD.StructuredRealizationPackage.ofAbstractStructuredComparisonData
      (T.toStructuredRealizationInputData targetData comparisonData)).structuredRealizationConsequence =
      T.structuredFaithfulness ∧
    (LayerD.StructuredRealizationPackage.ofAbstractStructuredComparisonData
      (T.toStructuredRealizationInputData targetData comparisonData)).realizationFunctorsInfinity =
      T.realizationFunctorsInfinity ∧
    (LayerD.StructuredRealizationPackage.ofAbstractStructuredComparisonData
      (T.toStructuredRealizationInputData targetData comparisonData)).realizationFunctorsPiZero =
      T.realizationFunctorsPiZero := by
  exact ⟨rfl, rfl, rfl⟩

end StructuredComparisonImplementationTicket

/-- Implementation-facing theorem ticket for the scalar extraction lane. This sharpens the scalar
period-map and extraction surfaces into one implementation-facing object that still feeds the
existing scalar-shadow package. -/
structure ScalarExtractionImplementationTicket
    (structuredComparison : StructuredComparisonImplementationTicket.{w, x}) where
  ScalarCarrier : Type y
  scalarExtractionMap :
    structuredComparison.BettiLikeCarrier → structuredComparison.DeRhamLikeCarrier → ScalarCarrier
  scalarExtractionFunctorial : Prop
  scalarExtractionFunctorial_holds : scalarExtractionFunctorial
  extractedFromStructuredData : Prop
  extractedFromStructuredData_holds : extractedFromStructuredData
  compatibleWithStructuredPackage : Prop
  compatibleWithStructuredPackage_holds : compatibleWithStructuredPackage
  scalarShadowExtraction : Prop
  scalarShadowExtraction_holds : scalarShadowExtraction

namespace ScalarExtractionImplementationTicket

/-- The current sharp J.2 ticket records the scalar carrier/extraction data and the theorem
obligations that let it feed the scalar-shadow package. -/
def theoremTarget
    {structuredComparison : StructuredComparisonImplementationTicket.{w, x}}
    (T : ScalarExtractionImplementationTicket structuredComparison) : Prop :=
  T.scalarExtractionFunctorial ∧
    T.extractedFromStructuredData ∧
    T.compatibleWithStructuredPackage ∧
    T.scalarShadowExtraction

theorem theoremTarget_holds
    {structuredComparison : StructuredComparisonImplementationTicket.{w, x}}
    (T : ScalarExtractionImplementationTicket structuredComparison) : T.theoremTarget := by
  exact ⟨T.scalarExtractionFunctorial_holds, T.extractedFromStructuredData_holds,
    T.compatibleWithStructuredPackage_holds, T.scalarShadowExtraction_holds⟩

def toScalarPeriodMapTheoremPackage
    {structuredComparison : StructuredComparisonImplementationTicket.{w, x}}
    (T : ScalarExtractionImplementationTicket structuredComparison) :
    ScalarPeriodMapTheoremPackage structuredComparison.toStructuredComparisonTheoremPackage where
  ScalarCarrier := T.ScalarCarrier
  scalarPeriodMap := T.scalarExtractionMap
  scalarPeriodMapFunctorial := T.scalarExtractionFunctorial
  scalarPeriodMapFunctorial_holds := T.scalarExtractionFunctorial_holds

def toScalarExtractionTheoremPackage
    {structuredComparison : StructuredComparisonImplementationTicket.{w, x}}
    (T : ScalarExtractionImplementationTicket structuredComparison) :
    ScalarExtractionTheoremPackage where
  extractedFromStructuredData := T.extractedFromStructuredData
  extractedFromStructuredData_holds := T.extractedFromStructuredData_holds
  compatibleWithStructuredPackage := T.compatibleWithStructuredPackage
  compatibleWithStructuredPackage_holds := T.compatibleWithStructuredPackage_holds
  scalarShadowExtraction := T.scalarShadowExtraction
  scalarShadowExtraction_holds := T.scalarShadowExtraction_holds

def toAbstractScalarShadowData
    {A : LayerE.AbstractMotivicTargetAxioms.{u, v}}
    (targetData : LayerE.TargetRecognitionInputData A)
    (comparisonData : LayerE.ComparisonInputData A targetData.infinityAxioms)
    (structuredComparison : StructuredComparisonImplementationTicket.{w, x})
    (scalarReflectsStructured : ScalarReflectsStructuredTheoremPackage)
    (T : ScalarExtractionImplementationTicket structuredComparison) :
    AbstractScalarShadowData
      (structuredComparison.toAbstractStructuredComparisonData targetData comparisonData) where
  ScalarCarrier := T.ScalarCarrier
  scalarPeriodMap := T.scalarExtractionMap
  extractedFromStructuredData := T.extractedFromStructuredData
  extractedFromStructuredData_holds := T.extractedFromStructuredData_holds
  scalarPeriodMapFunctorial := T.scalarExtractionFunctorial
  scalarPeriodMapFunctorial_holds := T.scalarExtractionFunctorial_holds
  compatibleWithStructuredPackage := T.compatibleWithStructuredPackage
  compatibleWithStructuredPackage_holds := T.compatibleWithStructuredPackage_holds
  scalarReflectsStructured := scalarReflectsStructured.scalarReflectsStructured
  scalarReflectsStructured_holds := scalarReflectsStructured.scalarReflectsStructured_holds
  scalarShadowExtraction := T.scalarShadowExtraction
  scalarShadowExtraction_holds := T.scalarShadowExtraction_holds

def toScalarShadowInputData
    {A : LayerE.AbstractMotivicTargetAxioms.{u, v}}
    (targetData : LayerE.TargetRecognitionInputData A)
    (comparisonData : LayerE.ComparisonInputData A targetData.infinityAxioms)
    (structuredComparison : StructuredComparisonImplementationTicket.{w, x})
    (scalarReflectsStructured : ScalarReflectsStructuredTheoremPackage)
    (T : ScalarExtractionImplementationTicket structuredComparison) :
    ScalarShadowInputData A where
  structuredInput :=
    structuredComparison.toStructuredRealizationInputData targetData comparisonData
  scalarData :=
    T.toAbstractScalarShadowData targetData comparisonData structuredComparison
      scalarReflectsStructured

theorem supplies_scalarShadowExtractionPackage
    {A : LayerE.AbstractMotivicTargetAxioms.{u, v}}
    (targetData : LayerE.TargetRecognitionInputData A)
    (comparisonData : LayerE.ComparisonInputData A targetData.infinityAxioms)
    (structuredComparison : StructuredComparisonImplementationTicket.{w, x})
    (scalarReflectsStructured : ScalarReflectsStructuredTheoremPackage)
    (T : ScalarExtractionImplementationTicket structuredComparison) :
    (LayerD.ScalarShadowExtractionPackage.ofAbstractScalarShadowData
      (T.toScalarShadowInputData targetData comparisonData structuredComparison
        scalarReflectsStructured)).scalarShadowExtraction =
      T.scalarShadowExtraction := by
  rfl

end ScalarExtractionImplementationTicket

/-- Implementation-facing theorem ticket for the scalar-reflects-structured lane. This sharpens
the reflection theorem into an explicit object depending on the structured comparison and scalar
extraction tickets while still feeding the existing scalar-shadow package surface. -/
structure ScalarReflectsStructuredImplementationTicket
    (structuredComparison : StructuredComparisonImplementationTicket.{w, x})
    (scalarExtraction : ScalarExtractionImplementationTicket structuredComparison) where
  scalarShadowEquality : scalarExtraction.ScalarCarrier → scalarExtraction.ScalarCarrier → Prop
  structuredEquality :
    structuredComparison.BettiLikeCarrier → structuredComparison.DeRhamLikeCarrier →
      structuredComparison.BettiLikeCarrier → structuredComparison.DeRhamLikeCarrier → Prop
  reflectionTheorem : Prop
  reflectionTheorem_holds : reflectionTheorem
  compatibleWithScalarExtractionTicket : Prop
  compatibleWithScalarExtractionTicket_holds : compatibleWithScalarExtractionTicket
  compatibleWithStructuredComparisonTicket : Prop
  compatibleWithStructuredComparisonTicket_holds : compatibleWithStructuredComparisonTicket
  scalarReflectsStructured : Prop
  scalarReflectsStructured_holds : scalarReflectsStructured

namespace ScalarReflectsStructuredImplementationTicket

/-- The current sharp J.3 ticket records the scalar-shadow equality premise, the structured
equality conclusion, and the theorem obligations that let scalar data reflect structured data. -/
def theoremTarget
    {structuredComparison : StructuredComparisonImplementationTicket.{w, x}}
    {scalarExtraction : ScalarExtractionImplementationTicket structuredComparison}
    (T : ScalarReflectsStructuredImplementationTicket structuredComparison scalarExtraction) : Prop :=
  T.reflectionTheorem ∧
    T.compatibleWithScalarExtractionTicket ∧
    T.compatibleWithStructuredComparisonTicket ∧
    T.scalarReflectsStructured

theorem theoremTarget_holds
    {structuredComparison : StructuredComparisonImplementationTicket.{w, x}}
    {scalarExtraction : ScalarExtractionImplementationTicket structuredComparison}
    (T : ScalarReflectsStructuredImplementationTicket structuredComparison scalarExtraction) :
    T.theoremTarget := by
  exact ⟨T.reflectionTheorem_holds, T.compatibleWithScalarExtractionTicket_holds,
    T.compatibleWithStructuredComparisonTicket_holds, T.scalarReflectsStructured_holds⟩

def toScalarReflectsStructuredTheoremPackage
    {structuredComparison : StructuredComparisonImplementationTicket.{w, x}}
    {scalarExtraction : ScalarExtractionImplementationTicket structuredComparison}
    (T : ScalarReflectsStructuredImplementationTicket structuredComparison scalarExtraction) :
    ScalarReflectsStructuredTheoremPackage where
  scalarReflectsStructured := T.scalarReflectsStructured
  scalarReflectsStructured_holds := T.scalarReflectsStructured_holds

theorem supplies_scalarReflectsStructured_field
    {A : LayerE.AbstractMotivicTargetAxioms.{u, v}}
    (targetData : LayerE.TargetRecognitionInputData A)
    (comparisonData : LayerE.ComparisonInputData A targetData.infinityAxioms)
    (structuredComparison : StructuredComparisonImplementationTicket.{w, x})
    (scalarExtraction : ScalarExtractionImplementationTicket structuredComparison)
    (T : ScalarReflectsStructuredImplementationTicket structuredComparison scalarExtraction) :
    ((scalarExtraction.toAbstractScalarShadowData targetData comparisonData structuredComparison
        T.toScalarReflectsStructuredTheoremPackage).scalarReflectsStructured) =
      T.scalarReflectsStructured := by
  rfl

end ScalarReflectsStructuredImplementationTicket

/-- Single theorem-package object for the structured/scalar period-realization lane. It records
the exact abstract theorem surfaces needed to instantiate the Layer F structured-realization and
scalar-shadow packages while keeping the Betti/de Rham comparison burden bundled into one object. -/
structure StructuredScalarTheoremPackage where
  targetAxioms : LayerE.AbstractMotivicTargetAxioms.{u, v}
  targetData : LayerE.TargetRecognitionInputData targetAxioms
  comparisonData : LayerE.ComparisonInputData targetAxioms targetData.infinityAxioms
  structuredData : AbstractStructuredComparisonData targetAxioms targetData comparisonData
  scalarData : AbstractScalarShadowData structuredData

/-- Decomposed theorem-subpackage view of the structured/scalar period-realization lane. The
ambient target and comparison data remain explicit, while the theorem burden is grouped into
named internal theorem subpackages pending full Lean implementation. -/
structure StructuredScalarTheoremSubpackages where
  targetAxioms : LayerE.AbstractMotivicTargetAxioms.{u, v}
  targetData : LayerE.TargetRecognitionInputData targetAxioms
  comparisonData : LayerE.ComparisonInputData targetAxioms targetData.infinityAxioms
  structuredComparison : StructuredComparisonTheoremPackage.{w, x}
  comparisonIsomorphism : ComparisonIsomorphismTheoremPackage
  structuredFaithfulness : StructuredFaithfulnessTheoremPackage
  scalarPeriodMap : ScalarPeriodMapTheoremPackage structuredComparison
  scalarExtraction : ScalarExtractionTheoremPackage
  scalarReflectsStructured : ScalarReflectsStructuredTheoremPackage

namespace StructuredScalarTheoremSubpackages

def structuredComparisonTicket
    (P : StructuredScalarTheoremSubpackages.{u, v, w, x, y}) :
    StructuredComparisonImplementationTicket :=
  { BettiLikeCarrier := P.structuredComparison.BettiLikeCarrier
    DeRhamLikeCarrier := P.structuredComparison.DeRhamLikeCarrier
    comparisonMap := P.structuredComparison.comparisonMap
    comparisonIsomorphism := P.comparisonIsomorphism.comparisonIsomorphism
    comparisonIsomorphism_holds := P.comparisonIsomorphism.comparisonIsomorphism_holds
    bettiLikeFunctoriality := P.structuredComparison.bettiLikeFunctoriality
    bettiLikeFunctoriality_holds := P.structuredComparison.bettiLikeFunctoriality_holds
    deRhamLikeFunctoriality := P.structuredComparison.deRhamLikeFunctoriality
    deRhamLikeFunctoriality_holds := P.structuredComparison.deRhamLikeFunctoriality_holds
    comparisonMapFunctorial := P.structuredComparison.comparisonMapFunctorial
    comparisonMapFunctorial_holds := P.structuredComparison.comparisonMapFunctorial_holds
    compatibleWithSourcePackage := P.structuredComparison.compatibleWithSourcePackage
    compatibleWithSourcePackage_holds := P.structuredComparison.compatibleWithSourcePackage_holds
    compatibleWithTargetPackage := P.structuredComparison.compatibleWithTargetPackage
    compatibleWithTargetPackage_holds := P.structuredComparison.compatibleWithTargetPackage_holds
    compatibleWithComparisonPackage := P.structuredComparison.compatibleWithComparisonPackage
    compatibleWithComparisonPackage_holds := P.structuredComparison.compatibleWithComparisonPackage_holds
    realizationFunctorsInfinity := P.structuredComparison.realizationFunctorsInfinity
    realizationFunctorsInfinity_holds := P.structuredComparison.realizationFunctorsInfinity_holds
    realizationFunctorsPiZero := P.structuredComparison.realizationFunctorsPiZero
    realizationFunctorsPiZero_holds := P.structuredComparison.realizationFunctorsPiZero_holds
    structuredFaithfulness := P.structuredFaithfulness.structuredFaithfulness
    structuredFaithfulness_holds := P.structuredFaithfulness.structuredFaithfulness_holds }

def scalarExtractionTicket
    (P : StructuredScalarTheoremSubpackages.{u, v, w, x, y}) :
  ScalarExtractionImplementationTicket P.structuredComparisonTicket :=
  { ScalarCarrier := P.scalarPeriodMap.ScalarCarrier
    scalarExtractionMap := P.scalarPeriodMap.scalarPeriodMap
    scalarExtractionFunctorial := P.scalarPeriodMap.scalarPeriodMapFunctorial
    scalarExtractionFunctorial_holds := P.scalarPeriodMap.scalarPeriodMapFunctorial_holds
    extractedFromStructuredData := P.scalarExtraction.extractedFromStructuredData
    extractedFromStructuredData_holds := P.scalarExtraction.extractedFromStructuredData_holds
    compatibleWithStructuredPackage := P.scalarExtraction.compatibleWithStructuredPackage
    compatibleWithStructuredPackage_holds := P.scalarExtraction.compatibleWithStructuredPackage_holds
    scalarShadowExtraction := P.scalarExtraction.scalarShadowExtraction
    scalarShadowExtraction_holds := P.scalarExtraction.scalarShadowExtraction_holds }

def scalarReflectsStructuredTicket
    (P : StructuredScalarTheoremSubpackages.{u, v, w, x, y}) :
    ScalarReflectsStructuredImplementationTicket P.structuredComparisonTicket P.scalarExtractionTicket :=
  { scalarShadowEquality := fun s1 s2 => s1 = s2
    structuredEquality := fun b1 d1 b2 d2 =>
      P.structuredComparison.comparisonMap b1 d1 ↔ P.structuredComparison.comparisonMap b2 d2
    reflectionTheorem := P.scalarReflectsStructured.scalarReflectsStructured
    reflectionTheorem_holds := P.scalarReflectsStructured.scalarReflectsStructured_holds
    compatibleWithScalarExtractionTicket := P.scalarExtraction.compatibleWithStructuredPackage
    compatibleWithScalarExtractionTicket_holds :=
      P.scalarExtraction.compatibleWithStructuredPackage_holds
    compatibleWithStructuredComparisonTicket := P.structuredComparison.compatibleWithComparisonPackage
    compatibleWithStructuredComparisonTicket_holds :=
      P.structuredComparison.compatibleWithComparisonPackage_holds
    scalarReflectsStructured := P.scalarReflectsStructured.scalarReflectsStructured
    scalarReflectsStructured_holds := P.scalarReflectsStructured.scalarReflectsStructured_holds }

def toAbstractStructuredComparisonData (P : StructuredScalarTheoremSubpackages.{u, v, w, x, y}) :
    AbstractStructuredComparisonData P.targetAxioms P.targetData P.comparisonData where
  BettiLikeCarrier := P.structuredComparison.BettiLikeCarrier
  DeRhamLikeCarrier := P.structuredComparison.DeRhamLikeCarrier
  comparisonMap := P.structuredComparison.comparisonMap
  comparisonIsomorphism := P.comparisonIsomorphism.comparisonIsomorphism
  comparisonIsomorphism_holds := P.comparisonIsomorphism.comparisonIsomorphism_holds
  bettiLikeFunctoriality := P.structuredComparison.bettiLikeFunctoriality
  bettiLikeFunctoriality_holds := P.structuredComparison.bettiLikeFunctoriality_holds
  deRhamLikeFunctoriality := P.structuredComparison.deRhamLikeFunctoriality
  deRhamLikeFunctoriality_holds := P.structuredComparison.deRhamLikeFunctoriality_holds
  comparisonMapFunctorial := P.structuredComparison.comparisonMapFunctorial
  comparisonMapFunctorial_holds := P.structuredComparison.comparisonMapFunctorial_holds
  compatibleWithSourcePackage := P.structuredComparison.compatibleWithSourcePackage
  compatibleWithSourcePackage_holds := P.structuredComparison.compatibleWithSourcePackage_holds
  compatibleWithTargetPackage := P.structuredComparison.compatibleWithTargetPackage
  compatibleWithTargetPackage_holds := P.structuredComparison.compatibleWithTargetPackage_holds
  compatibleWithComparisonPackage := P.structuredComparison.compatibleWithComparisonPackage
  compatibleWithComparisonPackage_holds :=
    P.structuredComparison.compatibleWithComparisonPackage_holds
  realizationFunctorsInfinity := P.structuredComparison.realizationFunctorsInfinity
  realizationFunctorsInfinity_holds := P.structuredComparison.realizationFunctorsInfinity_holds
  realizationFunctorsPiZero := P.structuredComparison.realizationFunctorsPiZero
  realizationFunctorsPiZero_holds := P.structuredComparison.realizationFunctorsPiZero_holds
  structuredFaithfulness := P.structuredFaithfulness.structuredFaithfulness
  structuredFaithfulness_holds := P.structuredFaithfulness.structuredFaithfulness_holds

def toStructuredRealizationInputData (P : StructuredScalarTheoremSubpackages.{u, v, w, x, y}) :
    StructuredRealizationInputData P.targetAxioms where
  targetData := P.targetData
  comparisonData := P.comparisonData
  structuredData := P.toAbstractStructuredComparisonData

def toAbstractScalarShadowData (P : StructuredScalarTheoremSubpackages.{u, v, w, x, y}) :
    AbstractScalarShadowData P.toAbstractStructuredComparisonData where
  ScalarCarrier := P.scalarPeriodMap.ScalarCarrier
  scalarPeriodMap := P.scalarPeriodMap.scalarPeriodMap
  extractedFromStructuredData := P.scalarExtraction.extractedFromStructuredData
  extractedFromStructuredData_holds := P.scalarExtraction.extractedFromStructuredData_holds
  scalarPeriodMapFunctorial := P.scalarPeriodMap.scalarPeriodMapFunctorial
  scalarPeriodMapFunctorial_holds := P.scalarPeriodMap.scalarPeriodMapFunctorial_holds
  compatibleWithStructuredPackage := P.scalarExtraction.compatibleWithStructuredPackage
  compatibleWithStructuredPackage_holds := P.scalarExtraction.compatibleWithStructuredPackage_holds
  scalarReflectsStructured := P.scalarReflectsStructured.scalarReflectsStructured
  scalarReflectsStructured_holds := P.scalarReflectsStructured.scalarReflectsStructured_holds
  scalarShadowExtraction := P.scalarExtraction.scalarShadowExtraction
  scalarShadowExtraction_holds := P.scalarExtraction.scalarShadowExtraction_holds

def toScalarShadowInputData (P : StructuredScalarTheoremSubpackages.{u, v, w, x, y}) :
    ScalarShadowInputData P.targetAxioms where
  structuredInput := P.toStructuredRealizationInputData
  scalarData := P.toAbstractScalarShadowData

def toStructuredScalarTheoremPackage (P : StructuredScalarTheoremSubpackages.{u, v, w, x, y}) :
  StructuredScalarTheoremPackage where
  targetAxioms := P.targetAxioms
  targetData := P.targetData
  comparisonData := P.comparisonData
  structuredData := P.toAbstractStructuredComparisonData
  scalarData := P.toAbstractScalarShadowData

def toStructuredAndScalarPackages (P : StructuredScalarTheoremSubpackages.{u, v, w, x, y}) :
    LayerD.StructuredRealizationPackage × LayerD.ScalarShadowExtractionPackage :=
  ( LayerD.StructuredRealizationPackage.ofAbstractStructuredComparisonData
      P.toStructuredRealizationInputData
  , LayerD.ScalarShadowExtractionPackage.ofAbstractScalarShadowData
      P.toScalarShadowInputData
  )

theorem toStructuredAndScalarPackages_fst
    (P : StructuredScalarTheoremSubpackages.{u, v, w, x, y}) :
    P.toStructuredAndScalarPackages.1 =
      LayerD.StructuredRealizationPackage.ofAbstractStructuredComparisonData
        P.toStructuredRealizationInputData := by
  rfl

theorem toStructuredAndScalarPackages_snd
    (P : StructuredScalarTheoremSubpackages.{u, v, w, x, y}) :
    P.toStructuredAndScalarPackages.2 =
      LayerD.ScalarShadowExtractionPackage.ofAbstractScalarShadowData
        P.toScalarShadowInputData := by
  rfl

end StructuredScalarTheoremSubpackages

namespace StructuredScalarTheoremPackage

def toStructuredRealizationInputData (P : StructuredScalarTheoremPackage.{u, v, w, x, y, z}) :
    StructuredRealizationInputData P.targetAxioms where
  targetData := P.targetData
  comparisonData := P.comparisonData
  structuredData := P.structuredData

def toScalarShadowInputData (P : StructuredScalarTheoremPackage.{u, v, w, x, y, z}) :
    ScalarShadowInputData P.targetAxioms where
  structuredInput := P.toStructuredRealizationInputData
  scalarData := P.scalarData

def toRealizationAndScalarInputData (P : StructuredScalarTheoremPackage.{u, v, w, x, y, z}) :
    RealizationAndScalarInputData P.targetAxioms where
  structuredInput := P.toStructuredRealizationInputData
  scalarInput := P.toScalarShadowInputData

def toStructuredAndScalarPackages (P : StructuredScalarTheoremPackage.{u, v, w, x, y, z}) :
    LayerD.StructuredRealizationPackage × LayerD.ScalarShadowExtractionPackage :=
  ( LayerD.StructuredRealizationPackage.ofAbstractStructuredComparisonData
      P.toStructuredRealizationInputData
  , LayerD.ScalarShadowExtractionPackage.ofAbstractScalarShadowData
      P.toScalarShadowInputData
  )

theorem toStructuredAndScalarPackages_fst
    (P : StructuredScalarTheoremPackage.{u, v, w, x, y, z}) :
    P.toStructuredAndScalarPackages.1 =
      LayerD.StructuredRealizationPackage.ofAbstractStructuredComparisonData
        P.toStructuredRealizationInputData := by
  rfl

theorem toStructuredAndScalarPackages_snd
    (P : StructuredScalarTheoremPackage.{u, v, w, x, y, z}) :
    P.toStructuredAndScalarPackages.2 =
      LayerD.ScalarShadowExtractionPackage.ofAbstractScalarShadowData
        P.toScalarShadowInputData := by
  rfl

end StructuredScalarTheoremPackage

def structuredScalarSubpackages_assemble
    (P : StructuredScalarTheoremSubpackages.{u, v, w, x, y}) :
  StructuredScalarTheoremPackage :=
  P.toStructuredScalarTheoremPackage

def structuredScalarSubpackages_to_packages
    (P : StructuredScalarTheoremSubpackages.{u, v, w, x, y}) :
    LayerD.StructuredRealizationPackage × LayerD.ScalarShadowExtractionPackage :=
  P.toStructuredAndScalarPackages

def structuredScalarSubpackages_to_structuredPackage
    (P : StructuredScalarTheoremSubpackages.{u, v, w, x, y}) :
    LayerD.StructuredRealizationPackage :=
  P.toStructuredAndScalarPackages.1

def structuredScalarSubpackages_to_scalarPackage
    (P : StructuredScalarTheoremSubpackages.{u, v, w, x, y}) :
    LayerD.ScalarShadowExtractionPackage :=
  P.toStructuredAndScalarPackages.2

theorem structuredScalarSubpackages_realize_structuredBridge
    (P : StructuredScalarTheoremSubpackages.{u, v, w, x, y}) :
    (structuredScalarSubpackages_to_structuredPackage P).package_gives_structuredRealizationBridgeReady.stageName =
        TraceCalc.LayerD.StructuredRealizationBridgeReady.stageName ∧
      (structuredScalarSubpackages_to_structuredPackage P).package_gives_structuredRealizationBridgeReady.availableStages =
        [ TraceCalc.LayerD.ComparisonFactorizationReady.stageName
        , TraceCalc.LayerD.InfinityComparisonReady.stageName
        ] ∧
      ∀ obligationId : TraceCalc.LayerD.MotivicObligationId,
        (structuredScalarSubpackages_to_structuredPackage P).package_gives_structuredRealizationBridgeReady.supportsObligationId
            obligationId ↔
          (structuredScalarSubpackages_to_structuredPackage P).SupportsObligationId obligationId := by
  simpa [structuredScalarSubpackages_to_structuredPackage] using
    LayerD.StructuredRealizationPackage.structuredPackage_realizes_exactly_structuredBridge
      (P := structuredScalarSubpackages_to_structuredPackage P)

theorem structuredScalarSubpackages_realize_scalarShadow
    (P : StructuredScalarTheoremSubpackages.{u, v, w, x, y}) :
    (structuredScalarSubpackages_to_scalarPackage P).package_gives_scalarShadowConsequenceReady.stageName =
        TraceCalc.LayerD.ScalarShadowConsequenceReady.stageName ∧
      (structuredScalarSubpackages_to_scalarPackage P).package_gives_scalarShadowConsequenceReady.availableStages =
        [TraceCalc.LayerD.StructuredRealizationBridgeReady.stageName] ∧
      ∀ obligationId : TraceCalc.LayerD.MotivicObligationId,
        (structuredScalarSubpackages_to_scalarPackage P).package_gives_scalarShadowConsequenceReady.supportsObligationId
            obligationId ↔
          (structuredScalarSubpackages_to_scalarPackage P).SupportsObligationId obligationId := by
  simpa [structuredScalarSubpackages_to_scalarPackage] using
    LayerD.ScalarShadowExtractionPackage.scalarPackage_realizes_exactly_scalarShadow
      (P := structuredScalarSubpackages_to_scalarPackage P)

def realizationAndScalarPackages_from_abstract_comparison_data
    {A : LayerE.AbstractMotivicTargetAxioms.{u, v}}
    (data : RealizationAndScalarInputData A) :
    LayerD.StructuredRealizationPackage × LayerD.ScalarShadowExtractionPackage :=
  ( LayerD.StructuredRealizationPackage.ofAbstractStructuredComparisonData data.structuredInput
  , LayerD.ScalarShadowExtractionPackage.ofAbstractScalarShadowData data.scalarInput
  )

theorem realizationAndScalarPackages_from_abstract_comparison_data_exact
    {A : LayerE.AbstractMotivicTargetAxioms.{u, v}}
    (data : RealizationAndScalarInputData A) :
    (realizationAndScalarPackages_from_abstract_comparison_data data).1 =
        LayerD.StructuredRealizationPackage.ofAbstractStructuredComparisonData
          data.structuredInput ∧
      (realizationAndScalarPackages_from_abstract_comparison_data data).2 =
        LayerD.ScalarShadowExtractionPackage.ofAbstractScalarShadowData data.scalarInput := by
  exact ⟨rfl, rfl⟩

def structuredScalarTheoremPackage_to_packages
    (P : StructuredScalarTheoremPackage.{u, v, w, x, y, z}) :
    LayerD.StructuredRealizationPackage × LayerD.ScalarShadowExtractionPackage :=
  P.toStructuredAndScalarPackages

end LayerF
end TraceCalc