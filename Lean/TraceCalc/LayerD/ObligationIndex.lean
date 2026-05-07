import TraceCalc.LayerD.ComparisonRoadmap

namespace TraceCalc
namespace LayerD

/-- Stable status marker for an indexed roadmap obligation. -/
inductive ObligationIndexStatus
  | registered
  | scaffolded
  | internalTheoremTarget
  | externalTheoremToInternalize
  | provedLater
  deriving DecidableEq, Repr

/-- Stable cross-reference entry for one roadmap obligation. -/
structure ObligationIndexEntry where
  obligationId : MotivicObligationId
  leanName : String
  texLabel : String
  humanTitle : String
  levelTag : MotivicObligationLevel
  theoremRole : TheoremRole
  status : ObligationIndexStatus
  deriving Repr

def mkObligationIndexEntry
    (obligation : MotivicComparisonObligation)
    (humanTitle : String)
    (status : ObligationIndexStatus) : ObligationIndexEntry where
  obligationId := obligation.id
  leanName := obligation.leanAnchor
  texLabel := obligation.texAnchor
  humanTitle := humanTitle
  levelTag := obligation.level
  theoremRole := obligation.auditClass
  status := status

def index_frontierUniversalProperty_pi0 : ObligationIndexEntry :=
  mkObligationIndexEntry obligation_frontierUniversalProperty_pi0
    "Pi0 frontier universal property" .scaffolded

def index_frontierUniversalProperty_infty : ObligationIndexEntry :=
  mkObligationIndexEntry obligation_frontierUniversalProperty_infty
    "Infinity frontier universal property" .scaffolded

def index_factorizationShadowExtraction : ObligationIndexEntry :=
  mkObligationIndexEntry obligation_factorizationShadowExtraction
    "Infinity-to-pi0 factorization shadow extraction" .registered

def index_symmetricMonoidal_pi0 : ObligationIndexEntry :=
  mkObligationIndexEntry obligation_symmetricMonoidal_pi0
    "Pi0 symmetric monoidal structure" .internalTheoremTarget

def index_symmetricMonoidal_infty : ObligationIndexEntry :=
  mkObligationIndexEntry obligation_symmetricMonoidal_infty
    "Infinity symmetric monoidal structure" .internalTheoremTarget

def index_triangulatedStable_pi0 : ObligationIndexEntry :=
  mkObligationIndexEntry obligation_triangulatedStable_pi0
    "Pi0 triangulated/stable structure" .internalTheoremTarget

def index_triangulatedStable_infty : ObligationIndexEntry :=
  mkObligationIndexEntry obligation_triangulatedStable_infty
    "Infinity triangulated/stable structure" .internalTheoremTarget

def index_a1Invariance_pi0 : ObligationIndexEntry :=
  mkObligationIndexEntry obligation_a1Invariance_pi0
    "Pi0 A1 invariance" .internalTheoremTarget

def index_a1Invariance_infty : ObligationIndexEntry :=
  mkObligationIndexEntry obligation_a1Invariance_infty
    "Infinity A1 invariance" .internalTheoremTarget

def index_nisnevichDescent_pi0 : ObligationIndexEntry :=
  mkObligationIndexEntry obligation_nisnevichDescent_pi0
    "Pi0 Nisnevich descent" .internalTheoremTarget

def index_nisnevichDescent_infty : ObligationIndexEntry :=
  mkObligationIndexEntry obligation_nisnevichDescent_infty
    "Infinity Nisnevich descent" .internalTheoremTarget

def index_localization_pi0 : ObligationIndexEntry :=
  mkObligationIndexEntry obligation_localization_pi0
    "Pi0 localization" .internalTheoremTarget

def index_localization_infty : ObligationIndexEntry :=
  mkObligationIndexEntry obligation_localization_infty
    "Infinity localization" .internalTheoremTarget

def index_tateStabilization_pi0 : ObligationIndexEntry :=
  mkObligationIndexEntry obligation_tateStabilization_pi0
    "Pi0 Tate stabilization" .internalTheoremTarget

def index_tateStabilization_infty : ObligationIndexEntry :=
  mkObligationIndexEntry obligation_tateStabilization_infty
    "Infinity Tate stabilization" .internalTheoremTarget

def index_targetCategoryRecognition_pi0 : ObligationIndexEntry :=
  mkObligationIndexEntry obligation_targetCategoryRecognition_pi0
    "Pi0 target-category recognition" .externalTheoremToInternalize

def index_targetCategoryRecognition_infty : ObligationIndexEntry :=
  mkObligationIndexEntry obligation_targetCategoryRecognition_infty
    "Infinity target-category recognition" .externalTheoremToInternalize

def index_targetUniversalPropertyRecognition : ObligationIndexEntry :=
  mkObligationIndexEntry obligation_targetUniversalPropertyRecognition
    "Infinity target universal-property recognition" .externalTheoremToInternalize

def index_targetRealizationStructureRecognition : ObligationIndexEntry :=
  mkObligationIndexEntry obligation_targetRealizationStructureRecognition
    "Infinity target realization-structure recognition" .externalTheoremToInternalize

def index_realizationFunctors_pi0 : ObligationIndexEntry :=
  mkObligationIndexEntry obligation_realizationFunctors_pi0
    "Pi0 realization functors" .provedLater

def index_realizationFunctors_infty : ObligationIndexEntry :=
  mkObligationIndexEntry obligation_realizationFunctors_infty
    "Infinity realization functors" .provedLater

def index_structuredRealizationConsequence : ObligationIndexEntry :=
  mkObligationIndexEntry obligation_structuredRealizationConsequence
    "Structured realization consequence" .provedLater

def index_scalarShadowExtraction : ObligationIndexEntry :=
  mkObligationIndexEntry obligation_scalarShadowExtraction
    "Scalar-shadow extraction" .provedLater

def index_finalPeriodFaithfulnessConsequence : ObligationIndexEntry :=
  mkObligationIndexEntry obligation_finalPeriodFaithfulnessConsequence
    "Final period-faithfulness consequence" .provedLater

def obligationIndexMap : List ObligationIndexEntry :=
  [ index_frontierUniversalProperty_pi0
  , index_frontierUniversalProperty_infty
  , index_factorizationShadowExtraction
  , index_symmetricMonoidal_pi0
  , index_symmetricMonoidal_infty
  , index_triangulatedStable_pi0
  , index_triangulatedStable_infty
  , index_a1Invariance_pi0
  , index_a1Invariance_infty
  , index_nisnevichDescent_pi0
  , index_nisnevichDescent_infty
  , index_localization_pi0
  , index_localization_infty
  , index_tateStabilization_pi0
  , index_tateStabilization_infty
  , index_targetCategoryRecognition_pi0
  , index_targetCategoryRecognition_infty
  , index_targetUniversalPropertyRecognition
  , index_targetRealizationStructureRecognition
  , index_realizationFunctors_pi0
  , index_realizationFunctors_infty
  , index_structuredRealizationConsequence
  , index_scalarShadowExtraction
  , index_finalPeriodFaithfulnessConsequence
  ]

def obligationsByLevel (level : MotivicObligationLevel) : List ObligationIndexEntry :=
  obligationIndexMap.filter fun entry => entry.levelTag = level

def obligationsByRole (role : TheoremRole) : List ObligationIndexEntry :=
  obligationIndexMap.filter fun entry => entry.theoremRole = role

def obligationsByStatus (status : ObligationIndexStatus) : List ObligationIndexEntry :=
  obligationIndexMap.filter fun entry => entry.status = status

def indexedObligationsWithIds (ids : List MotivicObligationId) : List ObligationIndexEntry :=
  obligationIndexMap.filter fun entry => entry.obligationId ∈ ids

theorem mem_obligationsByLevel_iff
    (entry : ObligationIndexEntry) (level : MotivicObligationLevel) :
    entry ∈ obligationsByLevel level ↔ entry ∈ obligationIndexMap ∧ entry.levelTag = level := by
  simp [obligationsByLevel]

theorem mem_obligationsByRole_iff
    (entry : ObligationIndexEntry) (role : TheoremRole) :
    entry ∈ obligationsByRole role ↔ entry ∈ obligationIndexMap ∧ entry.theoremRole = role := by
  simp [obligationsByRole]

theorem mem_obligationsByStatus_iff
    (entry : ObligationIndexEntry) (status : ObligationIndexStatus) :
    entry ∈ obligationsByStatus status ↔ entry ∈ obligationIndexMap ∧ entry.status = status := by
  simp [obligationsByStatus]

theorem mem_indexedObligationsWithIds_iff
    (entry : ObligationIndexEntry) (ids : List MotivicObligationId) :
    entry ∈ indexedObligationsWithIds ids ↔ entry ∈ obligationIndexMap ∧ entry.obligationId ∈ ids := by
  simp [indexedObligationsWithIds]

def periodFaithfulnessBlockingObligationIds : List MotivicObligationId :=
  [ obligation_frontierUniversalProperty_pi0.id
  , obligation_frontierUniversalProperty_infty.id
  , obligation_factorizationShadowExtraction.id
  , obligation_symmetricMonoidal_pi0.id
  , obligation_symmetricMonoidal_infty.id
  , obligation_triangulatedStable_pi0.id
  , obligation_triangulatedStable_infty.id
  , obligation_a1Invariance_pi0.id
  , obligation_a1Invariance_infty.id
  , obligation_nisnevichDescent_pi0.id
  , obligation_nisnevichDescent_infty.id
  , obligation_localization_pi0.id
  , obligation_localization_infty.id
  , obligation_tateStabilization_pi0.id
  , obligation_tateStabilization_infty.id
  , obligation_targetCategoryRecognition_pi0.id
  , obligation_targetCategoryRecognition_infty.id
  , obligation_targetUniversalPropertyRecognition.id
  , obligation_targetRealizationStructureRecognition.id
  , obligation_realizationFunctors_pi0.id
  , obligation_realizationFunctors_infty.id
  , obligation_structuredRealizationConsequence.id
  , obligation_scalarShadowExtraction.id
  , obligation_finalPeriodFaithfulnessConsequence.id
  ]

def infinityComparisonBlockingObligationIds : List MotivicObligationId :=
  [ obligation_frontierUniversalProperty_infty.id
  , obligation_triangulatedStable_infty.id
  , obligation_symmetricMonoidal_infty.id
  , obligation_a1Invariance_infty.id
  , obligation_nisnevichDescent_infty.id
  , obligation_localization_infty.id
  , obligation_tateStabilization_infty.id
  , obligation_targetCategoryRecognition_infty.id
  , obligation_targetUniversalPropertyRecognition.id
  ]

def noncircularityParticipantObligationIds : List MotivicObligationId :=
  [ obligation_frontierUniversalProperty_pi0.id
  , obligation_frontierUniversalProperty_infty.id
  , obligation_factorizationShadowExtraction.id
  , obligation_targetCategoryRecognition_pi0.id
  , obligation_targetCategoryRecognition_infty.id
  , obligation_targetUniversalPropertyRecognition.id
  , obligation_targetRealizationStructureRecognition.id
  , obligation_scalarShadowExtraction.id
  , obligation_finalPeriodFaithfulnessConsequence.id
  ]

def obligationsBlockingPeriodFaithfulness : List ObligationIndexEntry :=
  [ index_frontierUniversalProperty_pi0
  , index_frontierUniversalProperty_infty
  , index_factorizationShadowExtraction
  , index_symmetricMonoidal_pi0
  , index_symmetricMonoidal_infty
  , index_triangulatedStable_pi0
  , index_triangulatedStable_infty
  , index_a1Invariance_pi0
  , index_a1Invariance_infty
  , index_nisnevichDescent_pi0
  , index_nisnevichDescent_infty
  , index_localization_pi0
  , index_localization_infty
  , index_tateStabilization_pi0
  , index_tateStabilization_infty
  , index_targetCategoryRecognition_pi0
  , index_targetCategoryRecognition_infty
  , index_targetUniversalPropertyRecognition
  , index_targetRealizationStructureRecognition
  , index_realizationFunctors_pi0
  , index_realizationFunctors_infty
  , index_structuredRealizationConsequence
  , index_scalarShadowExtraction
  , index_finalPeriodFaithfulnessConsequence
  ]

def obligationsBlockingInfinityComparison : List ObligationIndexEntry :=
  [ index_frontierUniversalProperty_infty
  , index_triangulatedStable_infty
  , index_symmetricMonoidal_infty
  , index_a1Invariance_infty
  , index_nisnevichDescent_infty
  , index_localization_infty
  , index_tateStabilization_infty
  , index_targetCategoryRecognition_infty
  , index_targetUniversalPropertyRecognition
  ]

def obligationsParticipatingInNoncircularityDependencies : List ObligationIndexEntry :=
  [ index_frontierUniversalProperty_pi0
  , index_frontierUniversalProperty_infty
  , index_factorizationShadowExtraction
  , index_targetCategoryRecognition_pi0
  , index_targetCategoryRecognition_infty
  , index_targetUniversalPropertyRecognition
  , index_targetRealizationStructureRecognition
  , index_scalarShadowExtraction
  , index_finalPeriodFaithfulnessConsequence
  ]

theorem obligation_index_count :
    ∀ obligationId : MotivicObligationId,
      obligationId ∈ obligationIndexMap.map ObligationIndexEntry.obligationId ↔
        obligationId ∈ motivicComparisonObligationMap.map MotivicComparisonObligation.id := by
  intro obligationId
  simp [obligationIndexMap, motivicComparisonObligationMap, mkObligationIndexEntry,
    index_frontierUniversalProperty_pi0, index_frontierUniversalProperty_infty,
    index_factorizationShadowExtraction, index_symmetricMonoidal_pi0,
    index_symmetricMonoidal_infty, index_triangulatedStable_pi0,
    index_triangulatedStable_infty, index_a1Invariance_pi0, index_a1Invariance_infty,
    index_nisnevichDescent_pi0, index_nisnevichDescent_infty, index_localization_pi0,
    index_localization_infty, index_tateStabilization_pi0, index_tateStabilization_infty,
    index_targetCategoryRecognition_pi0, index_targetCategoryRecognition_infty,
    index_targetUniversalPropertyRecognition, index_targetRealizationStructureRecognition,
    index_realizationFunctors_pi0, index_realizationFunctors_infty,
    index_structuredRealizationConsequence, index_scalarShadowExtraction,
    index_finalPeriodFaithfulnessConsequence, MotivicComparisonObligation.id]

theorem theorem_period_faithfulness_blockers_indexed :
    ∀ obligationId : MotivicObligationId,
      obligationId ∈ obligationsBlockingPeriodFaithfulness.map ObligationIndexEntry.obligationId ↔
        obligationId ∈ periodFaithfulnessBlockingObligationIds := by
  intro obligationId
  simp [obligationsBlockingPeriodFaithfulness, obligationIndexMap,
    periodFaithfulnessBlockingObligationIds, mkObligationIndexEntry,
    index_frontierUniversalProperty_pi0, index_frontierUniversalProperty_infty,
    index_factorizationShadowExtraction, index_symmetricMonoidal_pi0,
    index_symmetricMonoidal_infty, index_triangulatedStable_pi0,
    index_triangulatedStable_infty, index_a1Invariance_pi0, index_a1Invariance_infty,
    index_nisnevichDescent_pi0, index_nisnevichDescent_infty, index_localization_pi0,
    index_localization_infty, index_tateStabilization_pi0, index_tateStabilization_infty,
    index_targetCategoryRecognition_pi0, index_targetCategoryRecognition_infty,
    index_targetUniversalPropertyRecognition, index_targetRealizationStructureRecognition,
    index_realizationFunctors_pi0, index_realizationFunctors_infty,
    index_structuredRealizationConsequence, index_scalarShadowExtraction,
    index_finalPeriodFaithfulnessConsequence]

theorem theorem_infinity_comparison_blockers_indexed :
    ∀ obligationId : MotivicObligationId,
      obligationId ∈ obligationsBlockingInfinityComparison.map ObligationIndexEntry.obligationId ↔
        obligationId ∈ infinityComparisonBlockingObligationIds := by
  intro obligationId
  simp [obligationsBlockingInfinityComparison, obligationIndexMap,
    infinityComparisonBlockingObligationIds, mkObligationIndexEntry,
    index_frontierUniversalProperty_infty, index_triangulatedStable_infty,
    index_symmetricMonoidal_infty, index_a1Invariance_infty,
    index_nisnevichDescent_infty, index_localization_infty, index_tateStabilization_infty,
    index_targetCategoryRecognition_infty, index_targetUniversalPropertyRecognition]

theorem theorem_noncircularity_dependencies_indexed :
    ∀ obligationId : MotivicObligationId,
      obligationId ∈ obligationsParticipatingInNoncircularityDependencies.map ObligationIndexEntry.obligationId ↔
        obligationId ∈ noncircularityParticipantObligationIds := by
  intro obligationId
  simp [obligationsParticipatingInNoncircularityDependencies, obligationIndexMap,
    noncircularityParticipantObligationIds, mkObligationIndexEntry,
    index_frontierUniversalProperty_pi0, index_frontierUniversalProperty_infty,
    index_factorizationShadowExtraction, index_targetCategoryRecognition_pi0,
    index_targetCategoryRecognition_infty, index_targetUniversalPropertyRecognition,
    index_targetRealizationStructureRecognition, index_scalarShadowExtraction,
    index_finalPeriodFaithfulnessConsequence]

/-- Stable stage marker for an indexed roadmap milestone. -/
inductive MilestoneStageKind
  | traceSide
  | sourceConstruction
  | targetRecognition
  | comparison
  | factorization
  | realization
  | scalarShadow
  | finalAssembly
  deriving DecidableEq, Repr

/-- Stable status marker for an indexed roadmap milestone. -/
inductive MilestoneIndexStatus
  | readinessPackage
  | registered
  | provedLater
  deriving DecidableEq, Repr

/-- Stable cross-reference entry for one roadmap milestone. -/
structure MilestoneIndexEntry where
  milestoneId : String
  leanAnchor : String
  texLabel : String
  humanTitle : String
  stageKind : MilestoneStageKind
  status : MilestoneIndexStatus
  obligationsIncluded : List MotivicObligationId
  prerequisiteMilestones : List String
  deriving Repr

def mkMilestoneIndexEntry
    (milestone : ComparisonMilestone)
    (leanAnchor texLabel humanTitle : String)
    (stageKind : MilestoneStageKind)
    (status : MilestoneIndexStatus) : MilestoneIndexEntry where
  milestoneId := milestone.stageName
  leanAnchor := leanAnchor
  texLabel := texLabel
  humanTitle := humanTitle
  stageKind := stageKind
  status := status
  obligationsIncluded := milestone.requiredObligations
  prerequisiteMilestones := milestone.upstreamMilestones

def milestoneIndex_TraceSideReady : MilestoneIndexEntry :=
  mkMilestoneIndexEntry TraceSideReady
    "TraceCalc.LayerD.TraceSideReady"
    "roadmap:trace-side-ready"
    "Trace-side readiness"
    .traceSide
    .readinessPackage

def milestoneIndex_PiZeroComparisonReady : MilestoneIndexEntry :=
  mkMilestoneIndexEntry PiZeroComparisonReady
    "TraceCalc.LayerD.PiZeroComparisonReady"
    "roadmap:pi0-comparison-ready"
    "Pi0 comparison readiness"
    .comparison
    .readinessPackage

def milestoneIndex_InfinityComparisonReady : MilestoneIndexEntry :=
  mkMilestoneIndexEntry InfinityComparisonReady
    "TraceCalc.LayerD.InfinityComparisonReady"
    "roadmap:infinity-comparison-ready"
    "Infinity comparison readiness"
    .comparison
    .readinessPackage

def milestoneIndex_PiZeroFactorizationReady : MilestoneIndexEntry :=
  mkMilestoneIndexEntry PiZeroFactorizationReady
    "TraceCalc.LayerD.PiZeroFactorizationReady"
    "roadmap:pi0-factorization-ready"
    "Pi0 factorization readiness"
    .factorization
    .readinessPackage

def milestoneIndex_InfinityFactorizationReady : MilestoneIndexEntry :=
  mkMilestoneIndexEntry InfinityFactorizationReady
    "TraceCalc.LayerD.InfinityFactorizationReady"
    "roadmap:infinity-factorization-ready"
    "Infinity factorization readiness"
    .factorization
    .readinessPackage

def milestoneIndex_FactorizationShadowExtractionReady : MilestoneIndexEntry :=
  mkMilestoneIndexEntry FactorizationShadowExtractionReady
    "TraceCalc.LayerD.FactorizationShadowExtractionReady"
    "roadmap:factorization-shadow-extraction-ready"
    "Factorization shadow-extraction readiness"
    .factorization
    .registered

def milestoneIndex_ComparisonFactorizationReady : MilestoneIndexEntry :=
  mkMilestoneIndexEntry ComparisonFactorizationReady
    "TraceCalc.LayerD.ComparisonFactorizationReady"
    "roadmap:comparison-factorization-ready"
    "Comparison factorization readiness"
    .comparison
    .readinessPackage

def milestoneIndex_RealizationBridgeReady : MilestoneIndexEntry :=
  mkMilestoneIndexEntry RealizationBridgeReady
    "TraceCalc.LayerD.RealizationBridgeReady"
    "roadmap:realization-bridge-ready"
    "Realization bridge readiness"
    .realization
    .readinessPackage

def milestoneIndex_PeriodFaithfulnessReady : MilestoneIndexEntry :=
  mkMilestoneIndexEntry PeriodFaithfulnessReady
    "TraceCalc.LayerD.PeriodFaithfulnessReady"
    "roadmap:period-faithfulness-ready"
    "Period-faithfulness readiness"
    .finalAssembly
    .provedLater

def milestoneIndex_SourceConstructionReady : MilestoneIndexEntry :=
  mkMilestoneIndexEntry SourceConstructionReady
    "TraceCalc.LayerD.SourceConstructionReady"
    "roadmap:source-construction-ready"
    "Source-construction readiness"
    .sourceConstruction
    .readinessPackage

def milestoneIndex_TargetRecognitionReady : MilestoneIndexEntry :=
  mkMilestoneIndexEntry TargetRecognitionReady
    "TraceCalc.LayerD.TargetRecognitionReady"
    "roadmap:target-recognition-ready"
    "Target-recognition readiness"
    .targetRecognition
    .readinessPackage

def milestoneIndex_StructuredRealizationBridgeReady : MilestoneIndexEntry :=
  mkMilestoneIndexEntry StructuredRealizationBridgeReady
    "TraceCalc.LayerD.StructuredRealizationBridgeReady"
    "roadmap:structured-realization-bridge-ready"
    "Structured realization bridge readiness"
    .realization
    .provedLater

def milestoneIndex_ScalarShadowConsequenceReady : MilestoneIndexEntry :=
  mkMilestoneIndexEntry ScalarShadowConsequenceReady
    "TraceCalc.LayerD.ScalarShadowConsequenceReady"
    "roadmap:scalar-shadow-consequence-ready"
    "Scalar-shadow consequence readiness"
    .scalarShadow
    .provedLater

def milestoneIndex_FinalComparisonEquivalenceAssemblyReady : MilestoneIndexEntry :=
  mkMilestoneIndexEntry FinalComparisonEquivalenceAssemblyReady
    "TraceCalc.LayerD.FinalComparisonEquivalenceAssemblyReady"
    "roadmap:final-comparison-equivalence-assembly-ready"
    "Final comparison-equivalence assembly readiness"
    .finalAssembly
    .provedLater

def milestoneIndexMap : List MilestoneIndexEntry :=
  [ milestoneIndex_TraceSideReady
  , milestoneIndex_PiZeroComparisonReady
  , milestoneIndex_InfinityComparisonReady
  , milestoneIndex_PiZeroFactorizationReady
  , milestoneIndex_InfinityFactorizationReady
  , milestoneIndex_FactorizationShadowExtractionReady
  , milestoneIndex_ComparisonFactorizationReady
  , milestoneIndex_RealizationBridgeReady
  , milestoneIndex_PeriodFaithfulnessReady
  , milestoneIndex_SourceConstructionReady
  , milestoneIndex_TargetRecognitionReady
  , milestoneIndex_StructuredRealizationBridgeReady
  , milestoneIndex_ScalarShadowConsequenceReady
  , milestoneIndex_FinalComparisonEquivalenceAssemblyReady
  ]

def milestonesByStatus (status : MilestoneIndexStatus) : List MilestoneIndexEntry :=
  milestoneIndexMap.filter fun entry => entry.status = status

def milestonesByStage (stage : MilestoneStageKind) : List MilestoneIndexEntry :=
  milestoneIndexMap.filter fun entry => entry.stageKind = stage

def milestoneEntryById? (milestoneId : String) : Option MilestoneIndexEntry :=
  milestoneIndexMap.find? fun entry => entry.milestoneId = milestoneId

def milestonePrerequisites (milestoneId : String) : List String :=
  match milestoneEntryById? milestoneId with
  | some entry => entry.prerequisiteMilestones
  | none => []

theorem mem_milestonesByStatus_iff
    (entry : MilestoneIndexEntry) (status : MilestoneIndexStatus) :
    entry ∈ milestonesByStatus status ↔ entry ∈ milestoneIndexMap ∧ entry.status = status := by
  simp [milestonesByStatus]

theorem mem_milestonesByStage_iff
    (entry : MilestoneIndexEntry) (stage : MilestoneStageKind) :
    entry ∈ milestonesByStage stage ↔ entry ∈ milestoneIndexMap ∧ entry.stageKind = stage := by
  simp [milestonesByStage]

def infinityComparisonBlockingMilestoneIds : List String :=
  [ TraceSideReady.stageName
  , TargetRecognitionReady.stageName
  , InfinityFactorizationReady.stageName
  , InfinityComparisonReady.stageName
  ]

def periodFaithfulnessBlockingMilestoneIds : List String :=
  [ TraceSideReady.stageName
  , SourceConstructionReady.stageName
  , TargetRecognitionReady.stageName
  , PiZeroFactorizationReady.stageName
  , InfinityFactorizationReady.stageName
  , FactorizationShadowExtractionReady.stageName
  , ComparisonFactorizationReady.stageName
  , InfinityComparisonReady.stageName
  , RealizationBridgeReady.stageName
  , StructuredRealizationBridgeReady.stageName
  , ScalarShadowConsequenceReady.stageName
  , FinalComparisonEquivalenceAssemblyReady.stageName
  , PeriodFaithfulnessReady.stageName
  ]

def milestonesBlockingInfinityComparison : List MilestoneIndexEntry :=
  [ milestoneIndex_TraceSideReady
  , milestoneIndex_TargetRecognitionReady
  , milestoneIndex_InfinityFactorizationReady
  , milestoneIndex_InfinityComparisonReady
  ]

def milestonesBlockingPeriodFaithfulness : List MilestoneIndexEntry :=
  [ milestoneIndex_TraceSideReady
  , milestoneIndex_SourceConstructionReady
  , milestoneIndex_TargetRecognitionReady
  , milestoneIndex_PiZeroFactorizationReady
  , milestoneIndex_InfinityFactorizationReady
  , milestoneIndex_FactorizationShadowExtractionReady
  , milestoneIndex_ComparisonFactorizationReady
  , milestoneIndex_InfinityComparisonReady
  , milestoneIndex_RealizationBridgeReady
  , milestoneIndex_StructuredRealizationBridgeReady
  , milestoneIndex_ScalarShadowConsequenceReady
  , milestoneIndex_FinalComparisonEquivalenceAssemblyReady
  , milestoneIndex_PeriodFaithfulnessReady
  ]

theorem theorem_milestone_index_registered :
    ∀ milestoneId : String,
      milestoneId ∈ milestoneIndexMap.map MilestoneIndexEntry.milestoneId ↔
        milestoneId ∈ comparisonMilestoneLadder.map ComparisonMilestone.stageName := by
  intro milestoneId
  change milestoneId ∈
      [ TraceSideReady.stageName
      , PiZeroComparisonReady.stageName
      , InfinityComparisonReady.stageName
      , PiZeroFactorizationReady.stageName
      , InfinityFactorizationReady.stageName
      , FactorizationShadowExtractionReady.stageName
      , ComparisonFactorizationReady.stageName
      , RealizationBridgeReady.stageName
      , PeriodFaithfulnessReady.stageName
      , SourceConstructionReady.stageName
      , TargetRecognitionReady.stageName
      , StructuredRealizationBridgeReady.stageName
      , ScalarShadowConsequenceReady.stageName
      , FinalComparisonEquivalenceAssemblyReady.stageName
      ] ↔ milestoneId ∈
      [ TraceSideReady.stageName
      , PiZeroComparisonReady.stageName
      , InfinityComparisonReady.stageName
      , RealizationBridgeReady.stageName
      , SourceConstructionReady.stageName
      , TargetRecognitionReady.stageName
      , PiZeroFactorizationReady.stageName
      , InfinityFactorizationReady.stageName
      , FactorizationShadowExtractionReady.stageName
      , ComparisonFactorizationReady.stageName
      , StructuredRealizationBridgeReady.stageName
      , ScalarShadowConsequenceReady.stageName
      , FinalComparisonEquivalenceAssemblyReady.stageName
      , PeriodFaithfulnessReady.stageName
      ]
  simp [or_assoc, or_left_comm, or_comm]

theorem theorem_period_faithfulness_milestones_indexed :
    ∀ milestoneId : String,
      milestoneId ∈ milestonesBlockingPeriodFaithfulness.map MilestoneIndexEntry.milestoneId ↔
        milestoneId ∈ periodFaithfulnessBlockingMilestoneIds := by
  intro milestoneId
  simp [milestonesBlockingPeriodFaithfulness, milestoneIndexMap,
    periodFaithfulnessBlockingMilestoneIds, mkMilestoneIndexEntry,
    milestoneIndex_TraceSideReady, milestoneIndex_SourceConstructionReady,
    milestoneIndex_TargetRecognitionReady, milestoneIndex_PiZeroFactorizationReady,
    milestoneIndex_InfinityFactorizationReady, milestoneIndex_FactorizationShadowExtractionReady,
    milestoneIndex_ComparisonFactorizationReady, milestoneIndex_InfinityComparisonReady,
    milestoneIndex_RealizationBridgeReady, milestoneIndex_StructuredRealizationBridgeReady,
    milestoneIndex_ScalarShadowConsequenceReady,
    milestoneIndex_FinalComparisonEquivalenceAssemblyReady,
    milestoneIndex_PeriodFaithfulnessReady]

theorem theorem_infinity_comparison_milestones_indexed :
    ∀ milestoneId : String,
      milestoneId ∈ milestonesBlockingInfinityComparison.map MilestoneIndexEntry.milestoneId ↔
        milestoneId ∈ infinityComparisonBlockingMilestoneIds := by
  intro milestoneId
  simp [milestonesBlockingInfinityComparison, milestoneIndexMap,
    infinityComparisonBlockingMilestoneIds, mkMilestoneIndexEntry,
    milestoneIndex_TraceSideReady, milestoneIndex_TargetRecognitionReady,
    milestoneIndex_InfinityFactorizationReady, milestoneIndex_InfinityComparisonReady]

theorem theorem_final_assembly_milestones_indexed :
    ∀ milestoneId : String,
      milestoneId ∈ milestonePrerequisites FinalComparisonEquivalenceAssemblyReady.stageName ↔
        milestoneId = SourceConstructionReady.stageName ∨
        milestoneId = TargetRecognitionReady.stageName ∨
        milestoneId = ComparisonFactorizationReady.stageName ∨
        milestoneId = StructuredRealizationBridgeReady.stageName ∨
        milestoneId = ScalarShadowConsequenceReady.stageName := by
  intro milestoneId
  change milestoneId ∈
      [ SourceConstructionReady.stageName
      , TargetRecognitionReady.stageName
      , ComparisonFactorizationReady.stageName
      , StructuredRealizationBridgeReady.stageName
      , ScalarShadowConsequenceReady.stageName
      ] ↔
        milestoneId = SourceConstructionReady.stageName ∨
        milestoneId = TargetRecognitionReady.stageName ∨
        milestoneId = ComparisonFactorizationReady.stageName ∨
        milestoneId = StructuredRealizationBridgeReady.stageName ∨
        milestoneId = ScalarShadowConsequenceReady.stageName
  simp

/-- Endpoint kind for indexed dependency edges. -/
inductive DependencyEndpointKind
  | obligation
  | milestone
  deriving DecidableEq, Repr

/-- Stable kind marker for indexed dependency edges. -/
inductive DependencyEdgeKind
  | prerequisite
  | bridge
  | warning
  | forbidden
  deriving DecidableEq, Repr

/-- Stable status marker for indexed dependency edges. -/
inductive DependencyEdgeIndexStatus
  | registered
  | auditConstraint
  deriving DecidableEq, Repr

/-- Stable cross-reference entry for one roadmap dependency edge. -/
structure DependencyEdgeIndexEntry where
  edgeId : String
  leanAnchor : String
  texLabel : String
  humanTitle : String
  sourceRef : String
  sourceKind : DependencyEndpointKind
  targetRef : String
  targetKind : DependencyEndpointKind
  edgeKind : DependencyEdgeKind
  reason : String
  status : DependencyEdgeIndexStatus
  deriving Repr

def prerequisiteEdgeId (sourceRef targetRef : String) : String :=
  s!"prerequisite:{sourceRef}->{targetRef}"

def bridgeEdgeId (sourceRef targetRef : String) : String :=
  s!"bridge:{sourceRef}->{targetRef}"

def auditEdgeId (kind : DependencyAuditKind) (sourceRef targetRef : String) : String :=
  match kind with
  | .warning => s!"warning:{sourceRef}->{targetRef}"
  | .forbidden => s!"forbidden:{sourceRef}->{targetRef}"

def mkPrerequisiteDependencyEdgeIndexEntry
    (edge : MotivicObligationDependency) : DependencyEdgeIndexEntry where
  edgeId := prerequisiteEdgeId edge.prerequisite edge.dependent
  leanAnchor := s!"dependencyEdge_{edge.prerequisite}_{edge.dependent}"
  texLabel := s!"roadmap:{edge.prerequisite}-to-{edge.dependent}"
  humanTitle := s!"Prerequisite edge: {edge.prerequisite} -> {edge.dependent}"
  sourceRef := edge.prerequisite
  sourceKind := .obligation
  targetRef := edge.dependent
  targetKind := .obligation
  edgeKind := .prerequisite
  reason := edge.reason
  status := .registered

def mkStageBridgeDependencyEdgeIndexEntry
    (edge : TargetRecognitionStageFeed) : DependencyEdgeIndexEntry where
  edgeId := bridgeEdgeId edge.prerequisite edge.dependentStage
  leanAnchor := s!"dependencyEdge_{edge.prerequisite}_{edge.dependentStage}"
  texLabel := s!"roadmap:{edge.prerequisite}-to-{edge.dependentStage}"
  humanTitle := s!"Bridge edge: {edge.prerequisite} -> {edge.dependentStage}"
  sourceRef := edge.prerequisite
  sourceKind := .obligation
  targetRef := edge.dependentStage
  targetKind := .milestone
  edgeKind := .bridge
  reason := edge.reason
  status := .registered

def mkAuditDependencyEdgeIndexEntry
    (edge : DependencyAuditEdge) : DependencyEdgeIndexEntry where
  edgeId := auditEdgeId edge.kind edge.source edge.target
  leanAnchor := s!"dependencyEdge_{edge.source}_{edge.target}"
  texLabel := s!"roadmap:{edge.source}-to-{edge.target}"
  humanTitle := s!"Audit edge: {edge.source} -> {edge.target}"
  sourceRef := edge.source
  sourceKind := .obligation
  targetRef := edge.target
  targetKind := .milestone
  edgeKind :=
    match edge.kind with
    | .warning => .warning
    | .forbidden => .forbidden
  reason := edge.reason
  status := .auditConstraint

def dependencyEdgeIndexMap : List DependencyEdgeIndexEntry :=
  motivicObligationDependencies.map mkPrerequisiteDependencyEdgeIndexEntry ++
  targetRecognitionStageFeeds.map mkStageBridgeDependencyEdgeIndexEntry ++
  comparisonFactorizationStageFeeds.map mkStageBridgeDependencyEdgeIndexEntry ++
  targetRecognitionAuditEdges.map mkAuditDependencyEdgeIndexEntry ++
  comparisonFactorizationAuditEdges.map mkAuditDependencyEdgeIndexEntry

def dependencyEdgesByKind (kind : DependencyEdgeKind) : List DependencyEdgeIndexEntry :=
  dependencyEdgeIndexMap.filter fun entry => entry.edgeKind = kind

def forbiddenEdges : List DependencyEdgeIndexEntry :=
  dependencyEdgesByKind .forbidden

def bridgeEdges : List DependencyEdgeIndexEntry :=
  dependencyEdgesByKind .bridge

theorem mem_dependencyEdgesByKind_iff
    (entry : DependencyEdgeIndexEntry) (kind : DependencyEdgeKind) :
    entry ∈ dependencyEdgesByKind kind ↔ entry ∈ dependencyEdgeIndexMap ∧ entry.edgeKind = kind := by
  simp [dependencyEdgesByKind]

theorem mem_forbiddenEdges_iff (entry : DependencyEdgeIndexEntry) :
    entry ∈ forbiddenEdges ↔ entry ∈ dependencyEdgeIndexMap ∧ entry.edgeKind = .forbidden := by
  simp [forbiddenEdges, mem_dependencyEdgesByKind_iff]

theorem mem_bridgeEdges_iff (entry : DependencyEdgeIndexEntry) :
    entry ∈ bridgeEdges ↔ entry ∈ dependencyEdgeIndexMap ∧ entry.edgeKind = .bridge := by
  simp [bridgeEdges, mem_dependencyEdgesByKind_iff]

def periodFaithfulnessBlockingEdgeIds : List String :=
  [ prerequisiteEdgeId obligation_targetCategoryRecognition_pi0.id obligation_factorizationShadowExtraction.id
  , prerequisiteEdgeId obligation_frontierUniversalProperty_infty.id obligation_factorizationShadowExtraction.id
  , bridgeEdgeId obligation_factorizationShadowExtraction.id FactorizationShadowExtractionReady.stageName
  , bridgeEdgeId obligation_factorizationShadowExtraction.id PiZeroComparisonReady.stageName
  , prerequisiteEdgeId obligation_factorizationShadowExtraction.id obligation_realizationFunctors_pi0.id
  , prerequisiteEdgeId obligation_realizationFunctors_infty.id obligation_structuredRealizationConsequence.id
  , prerequisiteEdgeId obligation_structuredRealizationConsequence.id obligation_scalarShadowExtraction.id
  , prerequisiteEdgeId obligation_scalarShadowExtraction.id obligation_finalPeriodFaithfulnessConsequence.id
  , auditEdgeId DependencyAuditKind.forbidden obligation_finalPeriodFaithfulnessConsequence.id ComparisonFactorizationReady.stageName
  ]

def infinityComparisonBlockingEdgeIds : List String :=
  [ bridgeEdgeId obligation_targetCategoryRecognition_infty.id InfinityComparisonReady.stageName
  , bridgeEdgeId obligation_targetCategoryRecognition_infty.id InfinityFactorizationReady.stageName
  , bridgeEdgeId obligation_targetUniversalPropertyRecognition.id InfinityFactorizationReady.stageName
  , bridgeEdgeId obligation_frontierUniversalProperty_infty.id InfinityFactorizationReady.stageName
  , prerequisiteEdgeId obligation_frontierUniversalProperty_infty.id obligation_realizationFunctors_infty.id
  , prerequisiteEdgeId obligation_targetUniversalPropertyRecognition.id obligation_realizationFunctors_infty.id
  , prerequisiteEdgeId obligation_targetCategoryRecognition_infty.id obligation_realizationFunctors_infty.id
  , auditEdgeId DependencyAuditKind.forbidden obligation_targetCategoryRecognition_pi0.id InfinityComparisonReady.stageName
  , auditEdgeId DependencyAuditKind.forbidden obligation_frontierUniversalProperty_pi0.id InfinityComparisonReady.stageName
  ]

def edgesBlockingInfinityComparison : List DependencyEdgeIndexEntry :=
  [ mkStageBridgeDependencyEdgeIndexEntry
      { prerequisite := obligation_targetCategoryRecognition_infty.id
      , dependentStage := InfinityComparisonReady.stageName
      , reason := "Infinity target-category recognition feeds the infinity comparison readiness package."
      }
  , mkStageBridgeDependencyEdgeIndexEntry
      { prerequisite := obligation_targetCategoryRecognition_infty.id
      , dependentStage := InfinityFactorizationReady.stageName
      , reason := "Infinity target recognition feeds the infinity factorization stage."
      }
  , mkStageBridgeDependencyEdgeIndexEntry
      { prerequisite := obligation_targetUniversalPropertyRecognition.id
      , dependentStage := InfinityFactorizationReady.stageName
      , reason := "Infinity target universal-property recognition feeds the infinity factorization stage."
      }
  , mkStageBridgeDependencyEdgeIndexEntry
      { prerequisite := obligation_frontierUniversalProperty_infty.id
      , dependentStage := InfinityFactorizationReady.stageName
      , reason := "Infinity frontier universal property feeds the infinity factorization stage."
      }
  , mkPrerequisiteDependencyEdgeIndexEntry
      { prerequisite := obligation_frontierUniversalProperty_infty.id
      , dependent := obligation_realizationFunctors_infty.id
      , reason := "The full infinity comparison functor needs the infinity-level frontier factorization contract."
      }
  , mkPrerequisiteDependencyEdgeIndexEntry
      { prerequisite := obligation_targetUniversalPropertyRecognition.id
      , dependent := obligation_realizationFunctors_infty.id
      , reason := "The target-side universal characterization is consumed by the infinity comparison / realization step."
      }
  , mkPrerequisiteDependencyEdgeIndexEntry
      { prerequisite := obligation_targetCategoryRecognition_infty.id
      , dependent := obligation_realizationFunctors_infty.id
      , reason := "The infinity realization bridge must know which target stable category is being recognized."
      }
  , mkAuditDependencyEdgeIndexEntry
      { source := obligation_targetCategoryRecognition_pi0.id
      , target := InfinityComparisonReady.stageName
      , kind := .forbidden
      , reason := "Pi0 target recognition cannot substitute for infinity target recognition."
      }
  , mkAuditDependencyEdgeIndexEntry
      { source := obligation_frontierUniversalProperty_pi0.id
      , target := InfinityComparisonReady.stageName
      , kind := .forbidden
      , reason := "Pi0 factorization must not feed infinity comparison readiness."
      }
  ]

def edgesBlockingPeriodFaithfulness : List DependencyEdgeIndexEntry :=
  [ mkPrerequisiteDependencyEdgeIndexEntry
      { prerequisite := obligation_targetCategoryRecognition_pi0.id
      , dependent := obligation_factorizationShadowExtraction.id
      , reason := "The pi0 comparison shadow is only meaningful after identifying the pi0 target category it lands in."
      }
  , mkPrerequisiteDependencyEdgeIndexEntry
      { prerequisite := obligation_frontierUniversalProperty_infty.id
      , dependent := obligation_factorizationShadowExtraction.id
      , reason := "Infinity factorization feeds the pi0 comparison shadow only through an explicit bridge obligation."
      }
  , mkStageBridgeDependencyEdgeIndexEntry
      { prerequisite := obligation_factorizationShadowExtraction.id
      , dependentStage := FactorizationShadowExtractionReady.stageName
      , reason := "The explicit bridge feeds the standalone factorization shadow-extraction stage."
      }
  , mkStageBridgeDependencyEdgeIndexEntry
      { prerequisite := obligation_factorizationShadowExtraction.id
      , dependentStage := PiZeroComparisonReady.stageName
      , reason := "The pi0 comparison shadow can only claim descent from infinity factorization through the explicit bridge."
      }
  , mkPrerequisiteDependencyEdgeIndexEntry
      { prerequisite := obligation_factorizationShadowExtraction.id
      , dependent := obligation_realizationFunctors_pi0.id
      , reason := "The pi0 comparison shadow may only be claimed after the explicit infinity-to-pi0 factorization bridge is registered."
      }
  , mkPrerequisiteDependencyEdgeIndexEntry
      { prerequisite := obligation_realizationFunctors_infty.id
      , dependent := obligation_structuredRealizationConsequence.id
      , reason := "The structured realization consequence is downstream of the infinity comparison / realization package."
      }
  , mkPrerequisiteDependencyEdgeIndexEntry
      { prerequisite := obligation_structuredRealizationConsequence.id
      , dependent := obligation_scalarShadowExtraction.id
      , reason := "Scalar-shadow extraction is a downstream consequence of structured realization faithfulness."
      }
  , mkPrerequisiteDependencyEdgeIndexEntry
      { prerequisite := obligation_scalarShadowExtraction.id
      , dependent := obligation_finalPeriodFaithfulnessConsequence.id
      , reason := "The final period-faithfulness consequence is assembled only after scalar-shadow extraction is available."
      }
  , mkAuditDependencyEdgeIndexEntry
      { source := obligation_finalPeriodFaithfulnessConsequence.id
      , target := ComparisonFactorizationReady.stageName
      , kind := .forbidden
      , reason := "The final period-faithfulness consequence cannot feed any factorization layer."
      }
  ]

theorem theorem_dependency_edge_index_registered :
    ∀ entry : DependencyEdgeIndexEntry,
      entry ∈ dependencyEdgeIndexMap ↔
        (∃ edge ∈ motivicObligationDependencies,
          mkPrerequisiteDependencyEdgeIndexEntry edge = entry) ∨
        (∃ edge ∈ targetRecognitionStageFeeds,
          mkStageBridgeDependencyEdgeIndexEntry edge = entry) ∨
        (∃ edge ∈ comparisonFactorizationStageFeeds,
          mkStageBridgeDependencyEdgeIndexEntry edge = entry) ∨
        (∃ edge ∈ targetRecognitionAuditEdges,
          mkAuditDependencyEdgeIndexEntry edge = entry) ∨
        ∃ edge ∈ comparisonFactorizationAuditEdges,
          mkAuditDependencyEdgeIndexEntry edge = entry := by
  intro entry
  simp [dependencyEdgeIndexMap]

theorem theorem_forbidden_flow_index_registered :
    ∀ entry : DependencyEdgeIndexEntry,
      entry ∈ forbiddenEdges ↔ entry ∈ dependencyEdgeIndexMap ∧ entry.edgeKind = .forbidden := by
  intro entry
  exact mem_forbiddenEdges_iff entry

theorem theorem_period_faithfulness_dependency_edges_indexed :
    ∀ edgeId : String,
      edgeId ∈ edgesBlockingPeriodFaithfulness.map DependencyEdgeIndexEntry.edgeId ↔
        edgeId ∈ periodFaithfulnessBlockingEdgeIds := by
  intro edgeId
  simp [edgesBlockingPeriodFaithfulness, dependencyEdgeIndexMap,
    periodFaithfulnessBlockingEdgeIds,
    mkPrerequisiteDependencyEdgeIndexEntry, mkStageBridgeDependencyEdgeIndexEntry,
    mkAuditDependencyEdgeIndexEntry, prerequisiteEdgeId, bridgeEdgeId, auditEdgeId]

theorem theorem_infinity_comparison_dependency_edges_indexed :
    ∀ edgeId : String,
      edgeId ∈ edgesBlockingInfinityComparison.map DependencyEdgeIndexEntry.edgeId ↔
        edgeId ∈ infinityComparisonBlockingEdgeIds := by
  intro edgeId
  simp [edgesBlockingInfinityComparison, dependencyEdgeIndexMap,
    infinityComparisonBlockingEdgeIds,
    mkPrerequisiteDependencyEdgeIndexEntry, mkStageBridgeDependencyEdgeIndexEntry,
    mkAuditDependencyEdgeIndexEntry, prerequisiteEdgeId, bridgeEdgeId, auditEdgeId]

end LayerD
end TraceCalc