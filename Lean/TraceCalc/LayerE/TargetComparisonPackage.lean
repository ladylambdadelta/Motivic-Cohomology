import TraceCalc.LayerD.PeriodFaithfulnessAssembly

universe u v w

namespace TraceCalc
namespace LayerE

/-- Abstract target-side axioms for the motivic comparison lane. This packages only the
carrier-level target data and the theorem surfaces that future motivic geometry must
instantiate. No concrete `DM_gm` construction is attempted here. -/
structure AbstractMotivicTargetAxioms where
  Obj : Type u
  Hom : Obj → Obj → Type v
  EqHom : {X Y : Obj} → Hom X Y → Hom X Y → Prop
  tensor : Obj → Obj → Obj
  unit : Obj
  shiftOrSuspension : Obj → Obj
  cofiberOrTriangle : {X Y : Obj} → Hom X Y → Obj
  A1Invariant : Prop
  A1Invariant_holds : A1Invariant
  NisnevichDescent : Prop
  NisnevichDescent_holds : NisnevichDescent
  Localization : Prop
  Localization_holds : Localization
  TateStabilization : Prop
  TateStabilization_holds : TateStabilization
  SymmetricMonoidalStable : Prop
  SymmetricMonoidalStable_holds : SymmetricMonoidalStable
  CompactGenerationOrGeometricGenerators : Prop
  CompactGenerationOrGeometricGenerators_holds : CompactGenerationOrGeometricGenerators
  UniversalProperty : Prop
  UniversalProperty_holds : UniversalProperty

/-- The `pi0`-shadow target-recognition surface stays separate from the full infinity target. -/
structure PiZeroTargetAxioms (A : AbstractMotivicTargetAxioms.{u, v}) where
  targetCategoryRecognition : Prop
  targetCategoryRecognition_holds : targetCategoryRecognition
  triangulatedShadow : Prop
  triangulatedShadow_holds : triangulatedShadow
  monoidalShadow : Prop
  monoidalShadow_holds : monoidalShadow
  A1InvariantShadow : Prop
  A1InvariantShadow_holds : A1InvariantShadow
  NisnevichDescentShadow : Prop
  NisnevichDescentShadow_holds : NisnevichDescentShadow
  LocalizationShadow : Prop
  LocalizationShadow_holds : LocalizationShadow
  TateStabilizationShadow : Prop
  TateStabilizationShadow_holds : TateStabilizationShadow

/-- The infinity-level target package carries the stronger recognition statements consumed by
the target-recognition and realization-bridge layers. -/
structure InfinityTargetAxioms (A : AbstractMotivicTargetAxioms.{u, v}) where
  targetCategoryRecognition : Prop
  targetCategoryRecognition_holds : targetCategoryRecognition
  targetUniversalPropertyRecognition : Prop
  targetUniversalPropertyRecognition_holds : targetUniversalPropertyRecognition
  targetRealizationStructureRecognition : Prop
  targetRealizationStructureRecognition_holds : targetRealizationStructureRecognition

/-- Explicit bridge data recording what descends from the infinity target semantics to the
classical `pi0` shadow. This keeps `pi0` recognition downstream of the stronger infinity lane
rather than conflating the two. -/
structure InfinityToPiZeroShadow
    {A : AbstractMotivicTargetAxioms.{u, v}}
    (I : InfinityTargetAxioms A) where
  targetCategoryRecognitionPiZero : Prop
  targetCategoryRecognitionPiZero_holds : targetCategoryRecognitionPiZero
  triangulatedShadow : Prop
  triangulatedShadow_holds : triangulatedShadow
  monoidalShadow : Prop
  monoidalShadow_holds : monoidalShadow
  A1InvariantShadow : Prop
  A1InvariantShadow_holds : A1InvariantShadow
  NisnevichDescentShadow : Prop
  NisnevichDescentShadow_holds : NisnevichDescentShadow
  LocalizationShadow : Prop
  LocalizationShadow_holds : LocalizationShadow
  TateStabilizationShadow : Prop
  TateStabilizationShadow_holds : TateStabilizationShadow

namespace InfinityTargetAxioms

def toPiZeroTargetAxioms
    {A : AbstractMotivicTargetAxioms.{u, v}}
    (I : InfinityTargetAxioms A)
    (S : InfinityToPiZeroShadow I) : PiZeroTargetAxioms A where
  targetCategoryRecognition := S.targetCategoryRecognitionPiZero
  targetCategoryRecognition_holds := S.targetCategoryRecognitionPiZero_holds
  triangulatedShadow := S.triangulatedShadow
  triangulatedShadow_holds := S.triangulatedShadow_holds
  monoidalShadow := S.monoidalShadow
  monoidalShadow_holds := S.monoidalShadow_holds
  A1InvariantShadow := S.A1InvariantShadow
  A1InvariantShadow_holds := S.A1InvariantShadow_holds
  NisnevichDescentShadow := S.NisnevichDescentShadow
  NisnevichDescentShadow_holds := S.NisnevichDescentShadow_holds
  LocalizationShadow := S.LocalizationShadow
  LocalizationShadow_holds := S.LocalizationShadow_holds
  TateStabilizationShadow := S.TateStabilizationShadow
  TateStabilizationShadow_holds := S.TateStabilizationShadow_holds

theorem infinity_and_shadow_give_piZero_target_recognition
    {A : AbstractMotivicTargetAxioms.{u, v}}
    (I : InfinityTargetAxioms A)
    (S : InfinityToPiZeroShadow I) :
    (I.toPiZeroTargetAxioms S).targetCategoryRecognition :=
  S.targetCategoryRecognitionPiZero_holds

end InfinityTargetAxioms

/-- Exact input surface needed to build the existing Layer D target-recognition package. -/
structure TargetRecognitionInputData (A : AbstractMotivicTargetAxioms.{u, v}) where
  infinityAxioms : InfinityTargetAxioms A
  piZeroShadow : InfinityToPiZeroShadow infinityAxioms

end LayerE

namespace LayerD
namespace TargetMotivicRecognitionPackage

def ofInfinityTargetAxioms
    {A : LayerE.AbstractMotivicTargetAxioms.{u, v}}
    (data : LayerE.TargetRecognitionInputData A) : TraceCalc.LayerD.TargetMotivicRecognitionPackage where
  targetCategoryRecognitionPiZero :=
    (data.infinityAxioms.toPiZeroTargetAxioms data.piZeroShadow).targetCategoryRecognition
  targetCategoryRecognitionPiZero_holds :=
    (data.infinityAxioms.toPiZeroTargetAxioms data.piZeroShadow).targetCategoryRecognition_holds
  targetCategoryRecognitionInfinity := data.infinityAxioms.targetCategoryRecognition
  targetCategoryRecognitionInfinity_holds := data.infinityAxioms.targetCategoryRecognition_holds
  targetUniversalPropertyRecognition := data.infinityAxioms.targetUniversalPropertyRecognition
  targetUniversalPropertyRecognition_holds :=
    data.infinityAxioms.targetUniversalPropertyRecognition_holds
  targetRealizationStructureRecognition :=
    data.infinityAxioms.targetRealizationStructureRecognition
  targetRealizationStructureRecognition_holds :=
    data.infinityAxioms.targetRealizationStructureRecognition_holds

theorem constructed_target_package_realizes_target_recognition
    {A : LayerE.AbstractMotivicTargetAxioms.{u, v}}
    (data : LayerE.TargetRecognitionInputData A) :
    ((ofInfinityTargetAxioms data).package_gives_targetRecognitionReady).stageName =
        TraceCalc.LayerD.TargetRecognitionReady.stageName ∧
      ((ofInfinityTargetAxioms data).package_gives_targetRecognitionReady).availableStages = [] ∧
      ∀ obligationId : TraceCalc.LayerD.MotivicObligationId,
        ((ofInfinityTargetAxioms data).package_gives_targetRecognitionReady).supportsObligationId
            obligationId ↔
          (ofInfinityTargetAxioms data).SupportsObligationId obligationId := by
  simpa using
    targetPackage_realizes_exactly_targetRecognition (P := ofInfinityTargetAxioms data)

end TargetMotivicRecognitionPackage
end LayerD

namespace LayerE

/-- Abstract comparison/factorization data over the infinity target. This is still only a
theorem package: it names the comparison surface without constructing a concrete motivic target. -/
structure AbstractInfinityComparisonData
    (A : AbstractMotivicTargetAxioms.{u, v})
    (I : InfinityTargetAxioms A) where
  Source : Type w
  sourceWitness : Source
  functorOrFactorization : Prop
  functorOrFactorization_holds : functorOrFactorization
  preservesTensor : Prop
  preservesTensor_holds : preservesTensor
  preservesStableStructure : Prop
  preservesStableStructure_holds : preservesStableStructure
  respectsA1NisLocTate : Prop
  respectsA1NisLocTate_holds : respectsA1NisLocTate
  fullFaithfulOrConservativeOnImage : Prop
  fullFaithfulOrConservativeOnImage_holds : fullFaithfulOrConservativeOnImage
  compatibleWithUniversalProperty : Prop
  compatibleWithUniversalProperty_holds : compatibleWithUniversalProperty
  frontierUniversalPropertyInfinity : Prop
  frontierUniversalPropertyInfinity_holds : frontierUniversalPropertyInfinity
  factorizationShadowExtraction : Prop
  factorizationShadowExtraction_holds : factorizationShadowExtraction

/-- Explicit bridge from the infinity comparison surface to the `pi0` comparison shadow. -/
structure InfinityComparisonToPiZeroShadow
    {A : AbstractMotivicTargetAxioms.{u, v}}
    {I : InfinityTargetAxioms A}
    (C : AbstractInfinityComparisonData A I) where
  frontierUniversalPropertyPiZero : Prop
  frontierUniversalPropertyPiZero_holds : frontierUniversalPropertyPiZero

/-- Exact input surface needed to build the existing Layer D comparison package. -/
structure ComparisonInputData
    (A : AbstractMotivicTargetAxioms.{u, v})
    (I : InfinityTargetAxioms A) where
  comparisonData : AbstractInfinityComparisonData A I
  piZeroShadow : InfinityComparisonToPiZeroShadow comparisonData

end LayerE

namespace LayerD
namespace InfinityComparisonPackage

def ofAbstractComparisonData
    {A : LayerE.AbstractMotivicTargetAxioms.{u, v}}
    {I : LayerE.InfinityTargetAxioms A}
    (data : LayerE.ComparisonInputData A I) : TraceCalc.LayerD.InfinityComparisonPackage where
  frontierUniversalPropertyPiZero := data.piZeroShadow.frontierUniversalPropertyPiZero
  frontierUniversalPropertyPiZero_holds := data.piZeroShadow.frontierUniversalPropertyPiZero_holds
  frontierUniversalPropertyInfinity := data.comparisonData.frontierUniversalPropertyInfinity
  frontierUniversalPropertyInfinity_holds :=
    data.comparisonData.frontierUniversalPropertyInfinity_holds
  factorizationShadowExtraction := data.comparisonData.factorizationShadowExtraction
  factorizationShadowExtraction_holds := data.comparisonData.factorizationShadowExtraction_holds

theorem constructed_comparison_package_realizes_comparison_factorization
    {A : LayerE.AbstractMotivicTargetAxioms.{u, v}}
    {I : LayerE.InfinityTargetAxioms A}
    (data : LayerE.ComparisonInputData A I) :
    ((ofAbstractComparisonData data).package_gives_comparisonFactorizationReady).stageName =
        TraceCalc.LayerD.ComparisonFactorizationReady.stageName ∧
      ((ofAbstractComparisonData data).package_gives_comparisonFactorizationReady).availableStages =
        [ TraceCalc.LayerD.PiZeroFactorizationReady.stageName
        , TraceCalc.LayerD.InfinityFactorizationReady.stageName
        , TraceCalc.LayerD.FactorizationShadowExtractionReady.stageName
        ] ∧
      ∀ obligationId : TraceCalc.LayerD.MotivicObligationId,
        ((ofAbstractComparisonData data).package_gives_comparisonFactorizationReady).supportsObligationId
            obligationId ↔
          (ofAbstractComparisonData data).SupportsObligationId obligationId := by
  simpa using
    comparisonPackage_realizes_exactly_comparisonFactorization
      (P := ofAbstractComparisonData data)

end InfinityComparisonPackage
end LayerD

namespace LayerE

/-- One-shot Layer E input surface for the two theorem-package inputs now being refined. -/
structure AbstractTargetComparisonPackageData
    (A : AbstractMotivicTargetAxioms.{u, v}) where
  targetData : TargetRecognitionInputData A
  comparisonData : ComparisonInputData A targetData.infinityAxioms

/-- Geometric-localization theorem package for the motivic target lane. -/
structure MotivicLocalizationTheoremPackage where
  A1Invariant : Prop
  A1Invariant_holds : A1Invariant
  NisnevichDescent : Prop
  NisnevichDescent_holds : NisnevichDescent
  Localization : Prop
  Localization_holds : Localization
  TateStabilization : Prop
  TateStabilization_holds : TateStabilization

/-- Implementation-facing theorem ticket for `A1` invariance. -/
structure A1InvarianceTheoremTicket (Obj : Type u) (Hom : Obj → Obj → Type v) where
  intervalObject : Obj
  productWithA1 : Obj → Obj
  projectionMap : (X : Obj) → Hom (productWithA1 X) X
  projectionIsA1Equivalence : Prop
  projectionIsA1Equivalence_holds : projectionIsA1Equivalence
  localizationInvertsProjection : Prop
  localizationInvertsProjection_holds : localizationInvertsProjection

namespace A1InvarianceTheoremTicket

/-- The current sharp A1 ticket states that the canonical projection off the `A1` product is an
`A1` equivalence and is inverted by the intended localization. -/
def theoremTarget
    {Obj : Type u} {Hom : Obj → Obj → Type v}
    (T : A1InvarianceTheoremTicket Obj Hom) : Prop :=
  T.projectionIsA1Equivalence ∧ T.localizationInvertsProjection

theorem theoremTarget_holds
    {Obj : Type u} {Hom : Obj → Obj → Type v}
    (T : A1InvarianceTheoremTicket Obj Hom) : T.theoremTarget := by
  exact ⟨T.projectionIsA1Equivalence_holds, T.localizationInvertsProjection_holds⟩

theorem projection_is_A1_equivalence
    {Obj : Type u} {Hom : Obj → Obj → Type v}
    (T : A1InvarianceTheoremTicket Obj Hom) : T.projectionIsA1Equivalence :=
  T.projectionIsA1Equivalence_holds

theorem localization_inverts_projection
    {Obj : Type u} {Hom : Obj → Obj → Type v}
    (T : A1InvarianceTheoremTicket Obj Hom) : T.localizationInvertsProjection :=
  T.localizationInvertsProjection_holds

end A1InvarianceTheoremTicket

/-- Implementation-facing theorem ticket for Nisnevich descent. -/
structure NisnevichDescentTheoremTicket (Obj : Type u) (Hom : Obj → Obj → Type v) where
  NisnevichSquare : Type u
  upperLeft : NisnevichSquare → Obj
  upperRight : NisnevichSquare → Obj
  lowerLeft : NisnevichSquare → Obj
  lowerRight : NisnevichSquare → Obj
  leftMap : (sq : NisnevichSquare) → Hom (upperLeft sq) (lowerLeft sq)
  topMap : (sq : NisnevichSquare) → Hom (upperLeft sq) (upperRight sq)
  rightMap : (sq : NisnevichSquare) → Hom (upperRight sq) (lowerRight sq)
  bottomMap : (sq : NisnevichSquare) → Hom (lowerLeft sq) (lowerRight sq)
  descentSquareCondition : NisnevichSquare → Prop
  descentSquareCondition_holds : ∀ sq : NisnevichSquare, descentSquareCondition sq
  localizationSatisfiesDescent : Prop
  localizationSatisfiesDescent_holds : localizationSatisfiesDescent

namespace NisnevichDescentTheoremTicket

/-- The current sharp Nisnevich ticket states that each chosen Nisnevich square satisfies the
intended descent condition and that the target localization enforces that descent relation. -/
def theoremTarget
    {Obj : Type u} {Hom : Obj → Obj → Type v}
    (T : NisnevichDescentTheoremTicket Obj Hom) : Prop :=
  (∀ sq : T.NisnevichSquare, T.descentSquareCondition sq) ∧ T.localizationSatisfiesDescent

theorem theoremTarget_holds
    {Obj : Type u} {Hom : Obj → Obj → Type v}
    (T : NisnevichDescentTheoremTicket Obj Hom) : T.theoremTarget := by
  exact ⟨T.descentSquareCondition_holds, T.localizationSatisfiesDescent_holds⟩

theorem descent_square_condition
    {Obj : Type u} {Hom : Obj → Obj → Type v}
    (T : NisnevichDescentTheoremTicket Obj Hom)
    (sq : T.NisnevichSquare) : T.descentSquareCondition sq :=
  T.descentSquareCondition_holds sq

theorem localization_satisfies_descent
    {Obj : Type u} {Hom : Obj → Obj → Type v}
    (T : NisnevichDescentTheoremTicket Obj Hom) : T.localizationSatisfiesDescent :=
  T.localizationSatisfiesDescent_holds

end NisnevichDescentTheoremTicket

/-- Implementation-facing theorem ticket for localization. -/
structure LocalizationTheoremTicket (Obj : Type u) (Hom : Obj → Obj → Type v) where
  LocalizationDatum : Type u
  closedPart : LocalizationDatum → Obj
  ambientPart : LocalizationDatum → Obj
  openPart : LocalizationDatum → Obj
  closedIntoAmbient : (d : LocalizationDatum) → Hom (closedPart d) (ambientPart d)
  ambientToOpen : (d : LocalizationDatum) → Hom (ambientPart d) (openPart d)
  localizationTriangleCondition : LocalizationDatum → Prop
  localizationTriangleCondition_holds : ∀ d : LocalizationDatum, localizationTriangleCondition d
  localizationExactness : Prop
  localizationExactness_holds : localizationExactness

namespace LocalizationTheoremTicket

/-- The current sharp localization ticket states that each chosen localization datum carries the
intended triangle/cofiber condition and that the target localization satisfies the resulting exactness. -/
def theoremTarget
    {Obj : Type u} {Hom : Obj → Obj → Type v}
    (T : LocalizationTheoremTicket Obj Hom) : Prop :=
  (∀ d : T.LocalizationDatum, T.localizationTriangleCondition d) ∧ T.localizationExactness

theorem theoremTarget_holds
    {Obj : Type u} {Hom : Obj → Obj → Type v}
    (T : LocalizationTheoremTicket Obj Hom) : T.theoremTarget := by
  exact ⟨T.localizationTriangleCondition_holds, T.localizationExactness_holds⟩

theorem localization_triangle_condition
    {Obj : Type u} {Hom : Obj → Obj → Type v}
    (T : LocalizationTheoremTicket Obj Hom)
    (d : T.LocalizationDatum) : T.localizationTriangleCondition d :=
  T.localizationTriangleCondition_holds d

theorem localization_exactness_holds'
    {Obj : Type u} {Hom : Obj → Obj → Type v}
    (T : LocalizationTheoremTicket Obj Hom) : T.localizationExactness :=
  T.localizationExactness_holds

end LocalizationTheoremTicket

/-- Implementation-facing theorem ticket for Tate/`P1` stabilization. -/
structure TateP1StabilizationTheoremTicket (Obj : Type u) (Hom : Obj → Obj → Type v) where
  tateObject : Obj
  p1Object : Obj
  stabilizeWithTate : Obj → Obj
  stabilizeWithP1 : Obj → Obj
  p1ToTateComparison : (X : Obj) → Hom (stabilizeWithP1 X) (stabilizeWithTate X)
  stabilizationComparison : Prop
  stabilizationComparison_holds : stabilizationComparison
  localizationRespectsStabilization : Prop
  localizationRespectsStabilization_holds : localizationRespectsStabilization

/-- Smallest explicit theorem surface currently available for Tate/`P1`
stabilization before it is packaged as a `TateP1StabilizationTheoremTicket`.

The repository already has a generic ticket builder, but it does not yet carry
the concrete Tate object, `P1` object, stabilization endofunctors, or their
comparison maps inside the bundled target theorem packages. This compatibility
record keeps those missing ingredients explicit and proof-bearing. -/
structure TateP1StabilizationCompatibilityData
    (Obj : Type u) (Hom : Obj → Obj → Type v) where
  tateObject : Obj
  p1Object : Obj
  stabilizeWithTate : Obj → Obj
  stabilizeWithP1 : Obj → Obj
  p1ToTateComparison : (X : Obj) → Hom (stabilizeWithP1 X) (stabilizeWithTate X)
  stabilizationComparison : Prop
  stabilizationComparison_holds : stabilizationComparison
  localizationRespectsStabilization : Prop
  localizationRespectsStabilization_holds : localizationRespectsStabilization

namespace TateP1StabilizationTheoremTicket

def ofTraceStabilizationData
    {Obj : Type u} {Hom : Obj → Obj → Type v}
    (data : TateP1StabilizationCompatibilityData Obj Hom) :
    TateP1StabilizationTheoremTicket Obj Hom where
  tateObject := data.tateObject
  p1Object := data.p1Object
  stabilizeWithTate := data.stabilizeWithTate
  stabilizeWithP1 := data.stabilizeWithP1
  p1ToTateComparison := data.p1ToTateComparison
  stabilizationComparison := data.stabilizationComparison
  stabilizationComparison_holds := data.stabilizationComparison_holds
  localizationRespectsStabilization := data.localizationRespectsStabilization
  localizationRespectsStabilization_holds := data.localizationRespectsStabilization_holds

/-- The current sharp stabilization ticket states that `P1` and Tate stabilization are compared by
the chosen transition maps and that the target localization respects that stabilization relation. -/
def theoremTarget
    {Obj : Type u} {Hom : Obj → Obj → Type v}
    (T : TateP1StabilizationTheoremTicket Obj Hom) : Prop :=
  T.stabilizationComparison ∧ T.localizationRespectsStabilization

theorem theoremTarget_holds
    {Obj : Type u} {Hom : Obj → Obj → Type v}
    (T : TateP1StabilizationTheoremTicket Obj Hom) : T.theoremTarget := by
  exact ⟨T.stabilizationComparison_holds, T.localizationRespectsStabilization_holds⟩

theorem stabilization_comparison
    {Obj : Type u} {Hom : Obj → Obj → Type v}
    (T : TateP1StabilizationTheoremTicket Obj Hom) : T.stabilizationComparison :=
  T.stabilizationComparison_holds

theorem localization_respects_stabilization
    {Obj : Type u} {Hom : Obj → Obj → Type v}
    (T : TateP1StabilizationTheoremTicket Obj Hom) : T.localizationRespectsStabilization :=
  T.localizationRespectsStabilization_holds

end TateP1StabilizationTheoremTicket

namespace MotivicLocalizationTheoremPackage

def toA1InvarianceTheoremTicket
    {Obj : Type u} {Hom : Obj → Obj → Type v}
    (P : MotivicLocalizationTheoremPackage)
    (intervalObject : Obj)
    (productWithA1 : Obj → Obj)
    (projectionMap : (X : Obj) → Hom (productWithA1 X) X)
    (projectionIsA1Equivalence : Prop)
    (projectionIsA1Equivalence_holds : projectionIsA1Equivalence)
    (localizationInvertsProjection : Prop)
    (localizationInvertsProjection_holds : localizationInvertsProjection)
    (_A1Invariant_eq :
      P.A1Invariant = (projectionIsA1Equivalence ∧ localizationInvertsProjection)) :
    A1InvarianceTheoremTicket Obj Hom where
  intervalObject := intervalObject
  productWithA1 := productWithA1
  projectionMap := projectionMap
  projectionIsA1Equivalence := projectionIsA1Equivalence
  projectionIsA1Equivalence_holds := projectionIsA1Equivalence_holds
  localizationInvertsProjection := localizationInvertsProjection
  localizationInvertsProjection_holds := localizationInvertsProjection_holds

theorem toA1InvarianceTheoremTicket_supplies_A1Invariant
    {Obj : Type u} {Hom : Obj → Obj → Type v}
    (P : MotivicLocalizationTheoremPackage)
    (intervalObject : Obj)
    (productWithA1 : Obj → Obj)
    (projectionMap : (X : Obj) → Hom (productWithA1 X) X)
    (projectionIsA1Equivalence : Prop)
    (projectionIsA1Equivalence_holds : projectionIsA1Equivalence)
    (localizationInvertsProjection : Prop)
    (localizationInvertsProjection_holds : localizationInvertsProjection)
    (A1Invariant_eq :
      P.A1Invariant = (projectionIsA1Equivalence ∧ localizationInvertsProjection)) :
    (A1InvarianceTheoremTicket.theoremTarget
        (toA1InvarianceTheoremTicket P intervalObject productWithA1 projectionMap
          projectionIsA1Equivalence projectionIsA1Equivalence_holds
          localizationInvertsProjection localizationInvertsProjection_holds
          A1Invariant_eq)) =
      P.A1Invariant := by
  simpa [A1InvarianceTheoremTicket.theoremTarget] using A1Invariant_eq.symm

def toNisnevichDescentTheoremTicket
    {Obj : Type u} {Hom : Obj → Obj → Type v}
    (P : MotivicLocalizationTheoremPackage)
    (NisnevichSquare : Type u)
    (upperLeft : NisnevichSquare → Obj)
    (upperRight : NisnevichSquare → Obj)
    (lowerLeft : NisnevichSquare → Obj)
    (lowerRight : NisnevichSquare → Obj)
    (leftMap : (sq : NisnevichSquare) → Hom (upperLeft sq) (lowerLeft sq))
    (topMap : (sq : NisnevichSquare) → Hom (upperLeft sq) (upperRight sq))
    (rightMap : (sq : NisnevichSquare) → Hom (upperRight sq) (lowerRight sq))
    (bottomMap : (sq : NisnevichSquare) → Hom (lowerLeft sq) (lowerRight sq))
    (descentSquareCondition : NisnevichSquare → Prop)
    (descentSquareCondition_holds : ∀ sq : NisnevichSquare, descentSquareCondition sq)
    (localizationSatisfiesDescent : Prop)
    (localizationSatisfiesDescent_holds : localizationSatisfiesDescent)
    (_NisnevichDescent_eq :
      P.NisnevichDescent =
        ((∀ sq : NisnevichSquare, descentSquareCondition sq) ∧ localizationSatisfiesDescent)) :
    NisnevichDescentTheoremTicket Obj Hom where
  NisnevichSquare := NisnevichSquare
  upperLeft := upperLeft
  upperRight := upperRight
  lowerLeft := lowerLeft
  lowerRight := lowerRight
  leftMap := leftMap
  topMap := topMap
  rightMap := rightMap
  bottomMap := bottomMap
  descentSquareCondition := descentSquareCondition
  descentSquareCondition_holds := descentSquareCondition_holds
  localizationSatisfiesDescent := localizationSatisfiesDescent
  localizationSatisfiesDescent_holds := localizationSatisfiesDescent_holds

theorem toNisnevichDescentTheoremTicket_supplies_NisnevichDescent
    {Obj : Type u} {Hom : Obj → Obj → Type v}
    (P : MotivicLocalizationTheoremPackage)
    (NisnevichSquare : Type u)
    (upperLeft : NisnevichSquare → Obj)
    (upperRight : NisnevichSquare → Obj)
    (lowerLeft : NisnevichSquare → Obj)
    (lowerRight : NisnevichSquare → Obj)
    (leftMap : (sq : NisnevichSquare) → Hom (upperLeft sq) (lowerLeft sq))
    (topMap : (sq : NisnevichSquare) → Hom (upperLeft sq) (upperRight sq))
    (rightMap : (sq : NisnevichSquare) → Hom (upperRight sq) (lowerRight sq))
    (bottomMap : (sq : NisnevichSquare) → Hom (lowerLeft sq) (lowerRight sq))
    (descentSquareCondition : NisnevichSquare → Prop)
    (descentSquareCondition_holds : ∀ sq : NisnevichSquare, descentSquareCondition sq)
    (localizationSatisfiesDescent : Prop)
    (localizationSatisfiesDescent_holds : localizationSatisfiesDescent)
    (NisnevichDescent_eq :
      P.NisnevichDescent =
        ((∀ sq : NisnevichSquare, descentSquareCondition sq) ∧ localizationSatisfiesDescent)) :
    (NisnevichDescentTheoremTicket.theoremTarget
        (toNisnevichDescentTheoremTicket P NisnevichSquare upperLeft upperRight lowerLeft lowerRight
          leftMap topMap rightMap bottomMap descentSquareCondition descentSquareCondition_holds
          localizationSatisfiesDescent localizationSatisfiesDescent_holds NisnevichDescent_eq)) =
      P.NisnevichDescent := by
  simpa [NisnevichDescentTheoremTicket.theoremTarget] using NisnevichDescent_eq.symm

def toLocalizationTheoremTicket
    {Obj : Type u} {Hom : Obj → Obj → Type v}
    (P : MotivicLocalizationTheoremPackage)
    (LocalizationDatum : Type u)
    (closedPart : LocalizationDatum → Obj)
    (ambientPart : LocalizationDatum → Obj)
    (openPart : LocalizationDatum → Obj)
    (closedIntoAmbient : (d : LocalizationDatum) → Hom (closedPart d) (ambientPart d))
    (ambientToOpen : (d : LocalizationDatum) → Hom (ambientPart d) (openPart d))
    (localizationTriangleCondition : LocalizationDatum → Prop)
    (localizationTriangleCondition_holds : ∀ d : LocalizationDatum, localizationTriangleCondition d)
    (localizationExactness : Prop)
    (localizationExactness_holds : localizationExactness)
    (_Localization_eq :
      P.Localization =
        ((∀ d : LocalizationDatum, localizationTriangleCondition d) ∧ localizationExactness)) :
    LocalizationTheoremTicket Obj Hom where
  LocalizationDatum := LocalizationDatum
  closedPart := closedPart
  ambientPart := ambientPart
  openPart := openPart
  closedIntoAmbient := closedIntoAmbient
  ambientToOpen := ambientToOpen
  localizationTriangleCondition := localizationTriangleCondition
  localizationTriangleCondition_holds := localizationTriangleCondition_holds
  localizationExactness := localizationExactness
  localizationExactness_holds := localizationExactness_holds

theorem toLocalizationTheoremTicket_supplies_Localization
    {Obj : Type u} {Hom : Obj → Obj → Type v}
    (P : MotivicLocalizationTheoremPackage)
    (LocalizationDatum : Type u)
    (closedPart : LocalizationDatum → Obj)
    (ambientPart : LocalizationDatum → Obj)
    (openPart : LocalizationDatum → Obj)
    (closedIntoAmbient : (d : LocalizationDatum) → Hom (closedPart d) (ambientPart d))
    (ambientToOpen : (d : LocalizationDatum) → Hom (ambientPart d) (openPart d))
    (localizationTriangleCondition : LocalizationDatum → Prop)
    (localizationTriangleCondition_holds : ∀ d : LocalizationDatum, localizationTriangleCondition d)
    (localizationExactness : Prop)
    (localizationExactness_holds : localizationExactness)
    (Localization_eq :
      P.Localization =
        ((∀ d : LocalizationDatum, localizationTriangleCondition d) ∧ localizationExactness)) :
    (LocalizationTheoremTicket.theoremTarget
        (toLocalizationTheoremTicket P LocalizationDatum closedPart ambientPart openPart
          closedIntoAmbient ambientToOpen localizationTriangleCondition
          localizationTriangleCondition_holds localizationExactness localizationExactness_holds
          Localization_eq)) =
      P.Localization := by
  simpa [LocalizationTheoremTicket.theoremTarget] using Localization_eq.symm

def toTateP1StabilizationTheoremTicket
    {Obj : Type u} {Hom : Obj → Obj → Type v}
    (P : MotivicLocalizationTheoremPackage)
    (tateObject : Obj)
    (p1Object : Obj)
    (stabilizeWithTate : Obj → Obj)
    (stabilizeWithP1 : Obj → Obj)
    (p1ToTateComparison : (X : Obj) → Hom (stabilizeWithP1 X) (stabilizeWithTate X))
    (stabilizationComparison : Prop)
    (stabilizationComparison_holds : stabilizationComparison)
    (localizationRespectsStabilization : Prop)
    (localizationRespectsStabilization_holds : localizationRespectsStabilization)
    (_TateStabilization_eq :
      P.TateStabilization =
        (stabilizationComparison ∧ localizationRespectsStabilization)) :
    TateP1StabilizationTheoremTicket Obj Hom where
  tateObject := tateObject
  p1Object := p1Object
  stabilizeWithTate := stabilizeWithTate
  stabilizeWithP1 := stabilizeWithP1
  p1ToTateComparison := p1ToTateComparison
  stabilizationComparison := stabilizationComparison
  stabilizationComparison_holds := stabilizationComparison_holds
  localizationRespectsStabilization := localizationRespectsStabilization
  localizationRespectsStabilization_holds := localizationRespectsStabilization_holds

theorem toTateP1StabilizationTheoremTicket_supplies_TateStabilization
    {Obj : Type u} {Hom : Obj → Obj → Type v}
    (P : MotivicLocalizationTheoremPackage)
    (tateObject : Obj)
    (p1Object : Obj)
    (stabilizeWithTate : Obj → Obj)
    (stabilizeWithP1 : Obj → Obj)
    (p1ToTateComparison : (X : Obj) → Hom (stabilizeWithP1 X) (stabilizeWithTate X))
    (stabilizationComparison : Prop)
    (stabilizationComparison_holds : stabilizationComparison)
    (localizationRespectsStabilization : Prop)
    (localizationRespectsStabilization_holds : localizationRespectsStabilization)
    (TateStabilization_eq :
      P.TateStabilization =
        (stabilizationComparison ∧ localizationRespectsStabilization)) :
    (TateP1StabilizationTheoremTicket.theoremTarget
        (toTateP1StabilizationTheoremTicket P tateObject p1Object stabilizeWithTate
          stabilizeWithP1 p1ToTateComparison stabilizationComparison
          stabilizationComparison_holds localizationRespectsStabilization
          localizationRespectsStabilization_holds TateStabilization_eq)) =
      P.TateStabilization := by
  simpa [TateP1StabilizationTheoremTicket.theoremTarget] using TateStabilization_eq.symm

def ofImplementationTickets
    {Obj : Type u} {Hom : Obj → Obj → Type v}
    (a1 : A1InvarianceTheoremTicket Obj Hom)
    (nis : NisnevichDescentTheoremTicket Obj Hom)
    (loc : LocalizationTheoremTicket Obj Hom)
    (tate : TateP1StabilizationTheoremTicket Obj Hom) : MotivicLocalizationTheoremPackage where
  A1Invariant := A1InvarianceTheoremTicket.theoremTarget a1
  A1Invariant_holds := A1InvarianceTheoremTicket.theoremTarget_holds a1
  NisnevichDescent := NisnevichDescentTheoremTicket.theoremTarget nis
  NisnevichDescent_holds := NisnevichDescentTheoremTicket.theoremTarget_holds nis
  Localization := LocalizationTheoremTicket.theoremTarget loc
  Localization_holds := LocalizationTheoremTicket.theoremTarget_holds loc
  TateStabilization := TateP1StabilizationTheoremTicket.theoremTarget tate
  TateStabilization_holds := TateP1StabilizationTheoremTicket.theoremTarget_holds tate

theorem ofImplementationTickets_a1
    {Obj : Type u} {Hom : Obj → Obj → Type v}
    (a1 : A1InvarianceTheoremTicket Obj Hom)
    (nis : NisnevichDescentTheoremTicket Obj Hom)
    (loc : LocalizationTheoremTicket Obj Hom)
    (tate : TateP1StabilizationTheoremTicket Obj Hom) :
    (ofImplementationTickets a1 nis loc tate).A1Invariant =
      A1InvarianceTheoremTicket.theoremTarget a1 := rfl

theorem ofImplementationTickets_nisnevich
  {Obj : Type u} {Hom : Obj → Obj → Type v}
  (a1 : A1InvarianceTheoremTicket Obj Hom)
    (nis : NisnevichDescentTheoremTicket Obj Hom)
    (loc : LocalizationTheoremTicket Obj Hom)
    (tate : TateP1StabilizationTheoremTicket Obj Hom) :
    (ofImplementationTickets a1 nis loc tate).NisnevichDescent =
      NisnevichDescentTheoremTicket.theoremTarget nis := rfl

theorem ofImplementationTickets_localization
  {Obj : Type u} {Hom : Obj → Obj → Type v}
  (a1 : A1InvarianceTheoremTicket Obj Hom)
    (nis : NisnevichDescentTheoremTicket Obj Hom)
    (loc : LocalizationTheoremTicket Obj Hom)
    (tate : TateP1StabilizationTheoremTicket Obj Hom) :
    (ofImplementationTickets a1 nis loc tate).Localization =
      LocalizationTheoremTicket.theoremTarget loc := rfl

theorem ofImplementationTickets_tateP1
  {Obj : Type u} {Hom : Obj → Obj → Type v}
  (a1 : A1InvarianceTheoremTicket Obj Hom)
    (nis : NisnevichDescentTheoremTicket Obj Hom)
    (loc : LocalizationTheoremTicket Obj Hom)
    (tate : TateP1StabilizationTheoremTicket Obj Hom) :
    (ofImplementationTickets a1 nis loc tate).TateStabilization =
      TateP1StabilizationTheoremTicket.theoremTarget tate := rfl

end MotivicLocalizationTheoremPackage

/-- Stable symmetric monoidal infinity theorem package for the motivic target lane. -/
structure StableSymmetricMonoidalInfinityTheoremPackage where
  SymmetricMonoidalStable : Prop
  SymmetricMonoidalStable_holds : SymmetricMonoidalStable
  CompactGenerationOrGeometricGenerators : Prop
  CompactGenerationOrGeometricGenerators_holds : CompactGenerationOrGeometricGenerators

/-- Target-recognition theorem package for the motivic target lane. -/
structure MotivicTargetRecognitionTheoremPackage where
  UniversalProperty : Prop
  UniversalProperty_holds : UniversalProperty
  targetCategoryRecognition : Prop
  targetCategoryRecognition_holds : targetCategoryRecognition
  targetUniversalPropertyRecognition : Prop
  targetUniversalPropertyRecognition_holds : targetUniversalPropertyRecognition
  targetRealizationStructureRecognition : Prop
  targetRealizationStructureRecognition_holds : targetRealizationStructureRecognition

/-- `pi0`-shadow theorem package for the motivic target lane. -/
structure PiZeroShadowTheoremPackage where
  targetCategoryRecognitionPiZero : Prop
  targetCategoryRecognitionPiZero_holds : targetCategoryRecognitionPiZero
  triangulatedShadow : Prop
  triangulatedShadow_holds : triangulatedShadow
  monoidalShadow : Prop
  monoidalShadow_holds : monoidalShadow
  A1InvariantShadow : Prop
  A1InvariantShadow_holds : A1InvariantShadow
  NisnevichDescentShadow : Prop
  NisnevichDescentShadow_holds : NisnevichDescentShadow
  LocalizationShadow : Prop
  LocalizationShadow_holds : LocalizationShadow
  TateStabilizationShadow : Prop
  TateStabilizationShadow_holds : TateStabilizationShadow

/-- Comparison/factorization theorem package for the motivic target lane. -/
structure MotivicComparisonFactorizationTheoremPackage where
  functorOrFactorization : Prop
  functorOrFactorization_holds : functorOrFactorization
  preservesTensor : Prop
  preservesTensor_holds : preservesTensor
  preservesStableStructure : Prop
  preservesStableStructure_holds : preservesStableStructure
  respectsA1NisLocTate : Prop
  respectsA1NisLocTate_holds : respectsA1NisLocTate
  fullFaithfulOrConservativeOnImage : Prop
  fullFaithfulOrConservativeOnImage_holds : fullFaithfulOrConservativeOnImage
  compatibleWithUniversalProperty : Prop
  compatibleWithUniversalProperty_holds : compatibleWithUniversalProperty
  frontierUniversalPropertyPiZero : Prop
  frontierUniversalPropertyPiZero_holds : frontierUniversalPropertyPiZero
  frontierUniversalPropertyInfinity : Prop
  frontierUniversalPropertyInfinity_holds : frontierUniversalPropertyInfinity
  factorizationShadowExtraction : Prop
  factorizationShadowExtraction_holds : factorizationShadowExtraction

/-- Single theorem-package object for the target recognition/comparison lane. It records the
ambient target carrier data together with exactly the theorem surfaces needed to instantiate the
Layer E target-recognition and comparison packages. -/
structure MotivicTargetTheoremPackage where
  targetAxioms : AbstractMotivicTargetAxioms.{u, v}
  infinityTargetAxioms : InfinityTargetAxioms targetAxioms
  piZeroShadow : InfinityToPiZeroShadow infinityTargetAxioms
  comparisonData : AbstractInfinityComparisonData targetAxioms infinityTargetAxioms
  comparisonPiZeroShadow : InfinityComparisonToPiZeroShadow comparisonData

/-- Decomposed theorem-subpackage view of the bundled motivic target theorem package. The ambient
target carrier data stays explicit here, while the theorem burden is grouped into named internal
theorem subpackages pending full Lean implementation. -/
structure MotivicTargetTheoremSubpackages where
  Obj : Type u
  Hom : Obj → Obj → Type v
  EqHom : {X Y : Obj} → Hom X Y → Hom X Y → Prop
  tensor : Obj → Obj → Obj
  unit : Obj
  shiftOrSuspension : Obj → Obj
  cofiberOrTriangle : {X Y : Obj} → Hom X Y → Obj
  Source : Type w
  sourceWitness : Source
  localization : MotivicLocalizationTheoremPackage
  stableSymmetricMonoidal : StableSymmetricMonoidalInfinityTheoremPackage
  recognition : MotivicTargetRecognitionTheoremPackage
  piZeroShadow : PiZeroShadowTheoremPackage
  comparison : MotivicComparisonFactorizationTheoremPackage

namespace MotivicTargetTheoremSubpackages

def a1InvarianceTicket
    (P : MotivicTargetTheoremSubpackages.{u, v, w})
    (intervalObject : P.Obj)
    (productWithA1 : P.Obj → P.Obj)
    (projectionMap : (X : P.Obj) → P.Hom (productWithA1 X) X)
    (projectionIsA1Equivalence : Prop)
    (projectionIsA1Equivalence_holds : projectionIsA1Equivalence)
    (localizationInvertsProjection : Prop)
    (localizationInvertsProjection_holds : localizationInvertsProjection)
    (A1Invariant_eq :
      P.localization.A1Invariant =
        (projectionIsA1Equivalence ∧ localizationInvertsProjection)) :
    A1InvarianceTheoremTicket P.Obj P.Hom :=
  P.localization.toA1InvarianceTheoremTicket intervalObject productWithA1 projectionMap
    projectionIsA1Equivalence projectionIsA1Equivalence_holds
    localizationInvertsProjection localizationInvertsProjection_holds
    A1Invariant_eq

def nisnevichDescentTicket
    (P : MotivicTargetTheoremSubpackages.{u, v, w})
    (NisnevichSquare : Type u)
    (upperLeft : NisnevichSquare → P.Obj)
    (upperRight : NisnevichSquare → P.Obj)
    (lowerLeft : NisnevichSquare → P.Obj)
    (lowerRight : NisnevichSquare → P.Obj)
    (leftMap : (sq : NisnevichSquare) → P.Hom (upperLeft sq) (lowerLeft sq))
    (topMap : (sq : NisnevichSquare) → P.Hom (upperLeft sq) (upperRight sq))
    (rightMap : (sq : NisnevichSquare) → P.Hom (upperRight sq) (lowerRight sq))
    (bottomMap : (sq : NisnevichSquare) → P.Hom (lowerLeft sq) (lowerRight sq))
    (descentSquareCondition : NisnevichSquare → Prop)
    (descentSquareCondition_holds : ∀ sq : NisnevichSquare, descentSquareCondition sq)
    (localizationSatisfiesDescent : Prop)
    (localizationSatisfiesDescent_holds : localizationSatisfiesDescent)
    (NisnevichDescent_eq :
      P.localization.NisnevichDescent =
        ((∀ sq : NisnevichSquare, descentSquareCondition sq) ∧ localizationSatisfiesDescent)) :
    NisnevichDescentTheoremTicket P.Obj P.Hom :=
  P.localization.toNisnevichDescentTheoremTicket NisnevichSquare upperLeft upperRight lowerLeft
    lowerRight leftMap topMap rightMap bottomMap descentSquareCondition
    descentSquareCondition_holds localizationSatisfiesDescent
    localizationSatisfiesDescent_holds NisnevichDescent_eq

def localizationTicket
    (P : MotivicTargetTheoremSubpackages.{u, v, w})
    (LocalizationDatum : Type u)
    (closedPart : LocalizationDatum → P.Obj)
    (ambientPart : LocalizationDatum → P.Obj)
    (openPart : LocalizationDatum → P.Obj)
    (closedIntoAmbient : (d : LocalizationDatum) → P.Hom (closedPart d) (ambientPart d))
    (ambientToOpen : (d : LocalizationDatum) → P.Hom (ambientPart d) (openPart d))
    (localizationTriangleCondition : LocalizationDatum → Prop)
    (localizationTriangleCondition_holds : ∀ d : LocalizationDatum, localizationTriangleCondition d)
    (localizationExactness : Prop)
    (localizationExactness_holds : localizationExactness)
    (Localization_eq :
      P.localization.Localization =
        ((∀ d : LocalizationDatum, localizationTriangleCondition d) ∧ localizationExactness)) :
    LocalizationTheoremTicket P.Obj P.Hom :=
  P.localization.toLocalizationTheoremTicket LocalizationDatum closedPart ambientPart openPart
    closedIntoAmbient ambientToOpen localizationTriangleCondition
    localizationTriangleCondition_holds localizationExactness localizationExactness_holds
    Localization_eq

def tateP1StabilizationTicket
    (P : MotivicTargetTheoremSubpackages.{u, v, w})
    (tateObject : P.Obj)
    (p1Object : P.Obj)
    (stabilizeWithTate : P.Obj → P.Obj)
    (stabilizeWithP1 : P.Obj → P.Obj)
    (p1ToTateComparison : (X : P.Obj) → P.Hom (stabilizeWithP1 X) (stabilizeWithTate X))
    (stabilizationComparison : Prop)
    (stabilizationComparison_holds : stabilizationComparison)
    (localizationRespectsStabilization : Prop)
    (localizationRespectsStabilization_holds : localizationRespectsStabilization)
    (TateStabilization_eq :
      P.localization.TateStabilization =
        (stabilizationComparison ∧ localizationRespectsStabilization)) :
    TateP1StabilizationTheoremTicket P.Obj P.Hom :=
  P.localization.toTateP1StabilizationTheoremTicket tateObject p1Object stabilizeWithTate
    stabilizeWithP1 p1ToTateComparison stabilizationComparison
    stabilizationComparison_holds localizationRespectsStabilization
    localizationRespectsStabilization_holds TateStabilization_eq

def toAbstractMotivicTargetAxioms (P : MotivicTargetTheoremSubpackages.{u, v, w}) :
    AbstractMotivicTargetAxioms.{u, v} where
  Obj := P.Obj
  Hom := P.Hom
  EqHom := P.EqHom
  tensor := P.tensor
  unit := P.unit
  shiftOrSuspension := P.shiftOrSuspension
  cofiberOrTriangle := P.cofiberOrTriangle
  A1Invariant := P.localization.A1Invariant
  A1Invariant_holds := P.localization.A1Invariant_holds
  NisnevichDescent := P.localization.NisnevichDescent
  NisnevichDescent_holds := P.localization.NisnevichDescent_holds
  Localization := P.localization.Localization
  Localization_holds := P.localization.Localization_holds
  TateStabilization := P.localization.TateStabilization
  TateStabilization_holds := P.localization.TateStabilization_holds
  SymmetricMonoidalStable := P.stableSymmetricMonoidal.SymmetricMonoidalStable
  SymmetricMonoidalStable_holds := P.stableSymmetricMonoidal.SymmetricMonoidalStable_holds
  CompactGenerationOrGeometricGenerators :=
    P.stableSymmetricMonoidal.CompactGenerationOrGeometricGenerators
  CompactGenerationOrGeometricGenerators_holds :=
    P.stableSymmetricMonoidal.CompactGenerationOrGeometricGenerators_holds
  UniversalProperty := P.recognition.UniversalProperty
  UniversalProperty_holds := P.recognition.UniversalProperty_holds

def toInfinityTargetAxioms (P : MotivicTargetTheoremSubpackages.{u, v, w}) :
    InfinityTargetAxioms P.toAbstractMotivicTargetAxioms where
  targetCategoryRecognition := P.recognition.targetCategoryRecognition
  targetCategoryRecognition_holds := P.recognition.targetCategoryRecognition_holds
  targetUniversalPropertyRecognition := P.recognition.targetUniversalPropertyRecognition
  targetUniversalPropertyRecognition_holds :=
    P.recognition.targetUniversalPropertyRecognition_holds
  targetRealizationStructureRecognition := P.recognition.targetRealizationStructureRecognition
  targetRealizationStructureRecognition_holds :=
    P.recognition.targetRealizationStructureRecognition_holds

def toInfinityToPiZeroShadow (P : MotivicTargetTheoremSubpackages.{u, v, w}) :
    InfinityToPiZeroShadow P.toInfinityTargetAxioms where
  targetCategoryRecognitionPiZero := P.piZeroShadow.targetCategoryRecognitionPiZero
  targetCategoryRecognitionPiZero_holds := P.piZeroShadow.targetCategoryRecognitionPiZero_holds
  triangulatedShadow := P.piZeroShadow.triangulatedShadow
  triangulatedShadow_holds := P.piZeroShadow.triangulatedShadow_holds
  monoidalShadow := P.piZeroShadow.monoidalShadow
  monoidalShadow_holds := P.piZeroShadow.monoidalShadow_holds
  A1InvariantShadow := P.piZeroShadow.A1InvariantShadow
  A1InvariantShadow_holds := P.piZeroShadow.A1InvariantShadow_holds
  NisnevichDescentShadow := P.piZeroShadow.NisnevichDescentShadow
  NisnevichDescentShadow_holds := P.piZeroShadow.NisnevichDescentShadow_holds
  LocalizationShadow := P.piZeroShadow.LocalizationShadow
  LocalizationShadow_holds := P.piZeroShadow.LocalizationShadow_holds
  TateStabilizationShadow := P.piZeroShadow.TateStabilizationShadow
  TateStabilizationShadow_holds := P.piZeroShadow.TateStabilizationShadow_holds

def toTargetRecognitionInputData (P : MotivicTargetTheoremSubpackages.{u, v, w}) :
    TargetRecognitionInputData P.toAbstractMotivicTargetAxioms where
  infinityAxioms := P.toInfinityTargetAxioms
  piZeroShadow := P.toInfinityToPiZeroShadow

def toAbstractInfinityComparisonData (P : MotivicTargetTheoremSubpackages.{u, v, w}) :
    AbstractInfinityComparisonData P.toAbstractMotivicTargetAxioms P.toInfinityTargetAxioms where
  Source := P.Source
  sourceWitness := P.sourceWitness
  functorOrFactorization := P.comparison.functorOrFactorization
  functorOrFactorization_holds := P.comparison.functorOrFactorization_holds
  preservesTensor := P.comparison.preservesTensor
  preservesTensor_holds := P.comparison.preservesTensor_holds
  preservesStableStructure := P.comparison.preservesStableStructure
  preservesStableStructure_holds := P.comparison.preservesStableStructure_holds
  respectsA1NisLocTate := P.comparison.respectsA1NisLocTate
  respectsA1NisLocTate_holds := P.comparison.respectsA1NisLocTate_holds
  fullFaithfulOrConservativeOnImage := P.comparison.fullFaithfulOrConservativeOnImage
  fullFaithfulOrConservativeOnImage_holds :=
    P.comparison.fullFaithfulOrConservativeOnImage_holds
  compatibleWithUniversalProperty := P.comparison.compatibleWithUniversalProperty
  compatibleWithUniversalProperty_holds := P.comparison.compatibleWithUniversalProperty_holds
  frontierUniversalPropertyInfinity := P.comparison.frontierUniversalPropertyInfinity
  frontierUniversalPropertyInfinity_holds := P.comparison.frontierUniversalPropertyInfinity_holds
  factorizationShadowExtraction := P.comparison.factorizationShadowExtraction
  factorizationShadowExtraction_holds := P.comparison.factorizationShadowExtraction_holds

def toInfinityComparisonToPiZeroShadow (P : MotivicTargetTheoremSubpackages.{u, v, w}) :
    InfinityComparisonToPiZeroShadow P.toAbstractInfinityComparisonData where
  frontierUniversalPropertyPiZero := P.comparison.frontierUniversalPropertyPiZero
  frontierUniversalPropertyPiZero_holds := P.comparison.frontierUniversalPropertyPiZero_holds

def toComparisonInputData (P : MotivicTargetTheoremSubpackages.{u, v, w}) :
    ComparisonInputData P.toAbstractMotivicTargetAxioms P.toInfinityTargetAxioms where
  comparisonData := P.toAbstractInfinityComparisonData
  piZeroShadow := P.toInfinityComparisonToPiZeroShadow

def toMotivicTargetTheoremPackage (P : MotivicTargetTheoremSubpackages.{u, v, w}) :
    MotivicTargetTheoremPackage.{u, v, w} where
  targetAxioms := P.toAbstractMotivicTargetAxioms
  infinityTargetAxioms := P.toInfinityTargetAxioms
  piZeroShadow := P.toInfinityToPiZeroShadow
  comparisonData := P.toAbstractInfinityComparisonData
  comparisonPiZeroShadow := P.toInfinityComparisonToPiZeroShadow

def toTargetAndComparisonPackages (P : MotivicTargetTheoremSubpackages.{u, v, w}) :
    LayerD.TargetMotivicRecognitionPackage × LayerD.InfinityComparisonPackage :=
  ( LayerD.TargetMotivicRecognitionPackage.ofInfinityTargetAxioms P.toTargetRecognitionInputData
  , LayerD.InfinityComparisonPackage.ofAbstractComparisonData P.toComparisonInputData
  )

theorem toTargetAndComparisonPackages_fst
    (P : MotivicTargetTheoremSubpackages.{u, v, w}) :
    P.toTargetAndComparisonPackages.1 =
      LayerD.TargetMotivicRecognitionPackage.ofInfinityTargetAxioms
        P.toTargetRecognitionInputData := by
  rfl

theorem toTargetAndComparisonPackages_snd
    (P : MotivicTargetTheoremSubpackages.{u, v, w}) :
    P.toTargetAndComparisonPackages.2 =
      LayerD.InfinityComparisonPackage.ofAbstractComparisonData
        P.toComparisonInputData := by
  rfl

end MotivicTargetTheoremSubpackages

namespace MotivicTargetTheoremPackage

def toTargetRecognitionInputData (P : MotivicTargetTheoremPackage.{u, v, w}) :
    TargetRecognitionInputData P.targetAxioms where
  infinityAxioms := P.infinityTargetAxioms
  piZeroShadow := P.piZeroShadow

def toComparisonInputData (P : MotivicTargetTheoremPackage.{u, v, w}) :
    ComparisonInputData P.targetAxioms P.infinityTargetAxioms where
  comparisonData := P.comparisonData
  piZeroShadow := P.comparisonPiZeroShadow

def toAbstractTargetComparisonPackageData (P : MotivicTargetTheoremPackage.{u, v, w}) :
    AbstractTargetComparisonPackageData P.targetAxioms where
  targetData := P.toTargetRecognitionInputData
  comparisonData := P.toComparisonInputData

def toTargetAndComparisonPackages (P : MotivicTargetTheoremPackage.{u, v, w}) :
    LayerD.TargetMotivicRecognitionPackage × LayerD.InfinityComparisonPackage :=
  ( LayerD.TargetMotivicRecognitionPackage.ofInfinityTargetAxioms P.toTargetRecognitionInputData
  , LayerD.InfinityComparisonPackage.ofAbstractComparisonData P.toComparisonInputData
  )

theorem toTargetAndComparisonPackages_fst
    (P : MotivicTargetTheoremPackage.{u, v, w}) :
    P.toTargetAndComparisonPackages.1 =
      LayerD.TargetMotivicRecognitionPackage.ofInfinityTargetAxioms
        P.toTargetRecognitionInputData := by
  rfl

theorem toTargetAndComparisonPackages_snd
    (P : MotivicTargetTheoremPackage.{u, v, w}) :
    P.toTargetAndComparisonPackages.2 =
      LayerD.InfinityComparisonPackage.ofAbstractComparisonData
        P.toComparisonInputData := by
  rfl

end MotivicTargetTheoremPackage

def motivicTargetSubpackages_assemble
    (P : MotivicTargetTheoremSubpackages.{u, v, w}) :
    MotivicTargetTheoremPackage.{u, v, w} :=
  P.toMotivicTargetTheoremPackage

def motivicTargetSubpackages_to_packages
    (P : MotivicTargetTheoremSubpackages.{u, v, w}) :
    LayerD.TargetMotivicRecognitionPackage × LayerD.InfinityComparisonPackage :=
  P.toTargetAndComparisonPackages

def motivicTargetSubpackages_to_targetPackage
    (P : MotivicTargetTheoremSubpackages.{u, v, w}) :
    LayerD.TargetMotivicRecognitionPackage :=
  P.toTargetAndComparisonPackages.1

def motivicTargetSubpackages_to_comparisonPackage
    (P : MotivicTargetTheoremSubpackages.{u, v, w}) :
    LayerD.InfinityComparisonPackage :=
  P.toTargetAndComparisonPackages.2

theorem motivicTargetSubpackages_realize_targetRecognition
    (P : MotivicTargetTheoremSubpackages.{u, v, w}) :
    (motivicTargetSubpackages_to_targetPackage P).package_gives_targetRecognitionReady.stageName =
        LayerD.TargetRecognitionReady.stageName ∧
      (motivicTargetSubpackages_to_targetPackage P).package_gives_targetRecognitionReady.availableStages = [] ∧
      ∀ obligationId : LayerD.MotivicObligationId,
        (motivicTargetSubpackages_to_targetPackage P).package_gives_targetRecognitionReady.supportsObligationId
            obligationId ↔
          (motivicTargetSubpackages_to_targetPackage P).SupportsObligationId obligationId := by
  simpa [motivicTargetSubpackages_to_targetPackage] using
    LayerD.TargetMotivicRecognitionPackage.targetPackage_realizes_exactly_targetRecognition
      (P := motivicTargetSubpackages_to_targetPackage P)

theorem motivicTargetSubpackages_realize_comparisonFactorization
    (P : MotivicTargetTheoremSubpackages.{u, v, w}) :
    (motivicTargetSubpackages_to_comparisonPackage P).package_gives_comparisonFactorizationReady.stageName =
        LayerD.ComparisonFactorizationReady.stageName ∧
      (motivicTargetSubpackages_to_comparisonPackage P).package_gives_comparisonFactorizationReady.availableStages =
        [ LayerD.PiZeroFactorizationReady.stageName
        , LayerD.InfinityFactorizationReady.stageName
        , LayerD.FactorizationShadowExtractionReady.stageName
        ] ∧
      ∀ obligationId : LayerD.MotivicObligationId,
        (motivicTargetSubpackages_to_comparisonPackage P).package_gives_comparisonFactorizationReady.supportsObligationId
            obligationId ↔
          (motivicTargetSubpackages_to_comparisonPackage P).SupportsObligationId obligationId := by
  simpa [motivicTargetSubpackages_to_comparisonPackage] using
    LayerD.InfinityComparisonPackage.comparisonPackage_realizes_exactly_comparisonFactorization
      (P := motivicTargetSubpackages_to_comparisonPackage P)

def targetAndComparisonPackages_from_abstract_motivic_target
    {A : AbstractMotivicTargetAxioms.{u, v}}
    (data : AbstractTargetComparisonPackageData A) :
    LayerD.TargetMotivicRecognitionPackage × LayerD.InfinityComparisonPackage :=
  ( LayerD.TargetMotivicRecognitionPackage.ofInfinityTargetAxioms data.targetData
  , LayerD.InfinityComparisonPackage.ofAbstractComparisonData data.comparisonData
  )

theorem targetAndComparisonPackages_from_abstract_motivic_target_exact
    {A : AbstractMotivicTargetAxioms.{u, v}}
    (data : AbstractTargetComparisonPackageData A) :
    (targetAndComparisonPackages_from_abstract_motivic_target data).1 =
        LayerD.TargetMotivicRecognitionPackage.ofInfinityTargetAxioms data.targetData ∧
      (targetAndComparisonPackages_from_abstract_motivic_target data).2 =
        LayerD.InfinityComparisonPackage.ofAbstractComparisonData data.comparisonData := by
  exact ⟨rfl, rfl⟩

def motivicTargetTheoremPackage_to_packages
    (P : MotivicTargetTheoremPackage.{u, v, w}) :
    LayerD.TargetMotivicRecognitionPackage × LayerD.InfinityComparisonPackage :=
  P.toTargetAndComparisonPackages

end LayerE
end TraceCalc