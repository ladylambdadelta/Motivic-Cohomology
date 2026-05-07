import TraceCalc.LayerD.SourceTracePackage
import TraceCalc.LayerD.MotivicObligationMap

namespace TraceCalc
namespace LayerD

/-- Dependency edge in the classical comparison roadmap. The nodes are obligation ids,
including the frontier universal-property surfaces. -/
structure MotivicObligationDependency where
  prerequisite : MotivicObligationId
  dependent : MotivicObligationId
  reason : String
  deriving DecidableEq, Repr

/-- Registry of forbidden dependency directions used for the noncircularity audit. -/
structure NoncircularityConstraint where
  forbiddenFrom : TheoremRole
  forbiddenTo : TheoremRole
  reason : String
  deriving DecidableEq, Repr

inductive DependencyAuditKind
  | warning
  | forbidden
  deriving DecidableEq, Repr

/-- A target-recognition entry feeding a specific comparison stage. -/
structure TargetRecognitionStageFeed where
  prerequisite : MotivicObligationId
  dependentStage : String
  reason : String
  deriving DecidableEq, Repr

/-- A forbidden or warning edge used to keep the roadmap level-separated. -/
structure DependencyAuditEdge where
  source : MotivicObligationId
  target : String
  kind : DependencyAuditKind
  reason : String
  deriving DecidableEq, Repr

def noScalarToStructuredConstraint : NoncircularityConstraint where
  forbiddenFrom := .scalarShadowExtraction
  forbiddenTo := .structuredRealization
  reason := "Scalar-shadow extraction must not be used to prove structured realization or comparison-data faithfulness."

def noFinalAssemblyToComparisonConstraint : NoncircularityConstraint where
  forbiddenFrom := .finalAssembly
  forbiddenTo := .comparisonFactorization
  reason := "The final period-faithfulness consequence must not be used to prove motivic comparison or factorization."

def noDirectSourceToTargetRecognitionConstraint : NoncircularityConstraint where
  forbiddenFrom := .sourceConstruction
  forbiddenTo := .targetRecognition
  reason := "Target recognition must not depend directly on source construction except through comparison/factorization."

def noExternalAsSourceConstraint : NoncircularityConstraint where
  forbiddenFrom := .externalInputToInternalize
  forbiddenTo := .sourceConstruction
  reason := "External motivic inputs must not be silently treated as source-side trace facts."

def comparisonRoadmapNoncircularityConstraints : List NoncircularityConstraint :=
  [ noScalarToStructuredConstraint
  , noFinalAssemblyToComparisonConstraint
  , noDirectSourceToTargetRecognitionConstraint
  , noExternalAsSourceConstraint
  ]

def targetRecognitionStageFeeds : List TargetRecognitionStageFeed :=
  [ { prerequisite := obligation_targetCategoryRecognition_pi0.id
    , dependentStage := "PiZeroComparisonReady"
    , reason := "Pi0 target-category recognition feeds only the pi0 comparison readiness package."
    }
  , { prerequisite := obligation_targetCategoryRecognition_infty.id
    , dependentStage := "InfinityComparisonReady"
    , reason := "Infinity target-category recognition feeds the infinity comparison readiness package."
    }
  , { prerequisite := obligation_targetUniversalPropertyRecognition.id
    , dependentStage := "ComparisonFactorizationReady"
    , reason := "Infinity universal-property recognition feeds the comparison factorization surface rather than the pi0 shadow."
    }
  , { prerequisite := obligation_targetRealizationStructureRecognition.id
    , dependentStage := "StructuredRealizationBridgeReady"
    , reason := "Infinity realization-structure recognition feeds the structured realization bridge."
    }
  ]

def targetRecognitionAuditEdges : List DependencyAuditEdge :=
  [ { source := obligation_targetCategoryRecognition_pi0.id
    , target := "InfinityComparisonReady"
    , kind := .forbidden
    , reason := "Pi0 target recognition cannot substitute for infinity target recognition."
    }
  , { source := obligation_scalarShadowExtraction.id
    , target := "TargetRecognitionReady"
    , kind := .forbidden
    , reason := "Scalar-shadow extraction is downstream and cannot feed target recognition."
    }
  , { source := obligation_finalPeriodFaithfulnessConsequence.id
    , target := "ComparisonFactorizationReady"
    , kind := .forbidden
    , reason := "The final period-faithfulness consequence cannot feed comparison factorization."
    }
  ]

def motivicObligationDependencies : List MotivicObligationDependency :=
  [ { prerequisite := obligation_triangulatedStable_infty.id
    , dependent := obligation_localization_infty.id
    , reason := "Stable infinity structure is required before infinity-level localization can be stated honestly."
    }
  , { prerequisite := obligation_triangulatedStable_infty.id
    , dependent := obligation_nisnevichDescent_infty.id
    , reason := "Infinity-level descent depends on the ambient stable infinity-categorical structure."
    }
  , { prerequisite := obligation_triangulatedStable_infty.id
    , dependent := obligation_tateStabilization_infty.id
    , reason := "Stable infinity structure is required before Tate stabilization can be promoted beyond the pi0 shadow."
    }
  , { prerequisite := obligation_symmetricMonoidal_infty.id
    , dependent := obligation_tateStabilization_infty.id
    , reason := "Tate inversion at the infinity level uses coherently symmetric monoidal structure."
    }
  , { prerequisite := obligation_symmetricMonoidal_infty.id
    , dependent := obligation_realizationFunctors_infty.id
    , reason := "An infinity realization functor must preserve coherent symmetric monoidal structure."
    }
  , { prerequisite := obligation_triangulatedStable_pi0.id
    , dependent := obligation_localization_pi0.id
    , reason := "The pi0 localization theorem lives in the Verdier triangulated shadow."
    }
  , { prerequisite := obligation_triangulatedStable_pi0.id
    , dependent := obligation_nisnevichDescent_pi0.id
    , reason := "The pi0 descent theorem is stated in the triangulated shadow."
    }
  , { prerequisite := obligation_symmetricMonoidal_pi0.id
    , dependent := obligation_tateStabilization_pi0.id
    , reason := "Pi0 Tate invertibility is expressed in the monoidal triangulated shadow."
    }
  , { prerequisite := obligation_frontierUniversalProperty_pi0.id
    , dependent := obligation_realizationFunctors_pi0.id
    , reason := "The source-side pi0 universal property must be available before a pi0 comparison functor can factor through it."
    }
  , { prerequisite := obligation_targetCategoryRecognition_pi0.id
    , dependent := obligation_factorizationShadowExtraction.id
    , reason := "The pi0 comparison shadow is only meaningful after identifying the pi0 target category it lands in."
    }
  , { prerequisite := obligation_frontierUniversalProperty_infty.id
    , dependent := obligation_realizationFunctors_infty.id
    , reason := "The full infinity comparison functor needs the infinity-level frontier factorization contract."
    }
  , { prerequisite := obligation_frontierUniversalProperty_infty.id
    , dependent := obligation_factorizationShadowExtraction.id
    , reason := "Infinity factorization feeds the pi0 comparison shadow only through an explicit bridge obligation."
    }
  , { prerequisite := obligation_targetUniversalPropertyRecognition.id
    , dependent := obligation_realizationFunctors_infty.id
    , reason := "The target-side universal characterization is consumed by the infinity comparison / realization step."
    }
  , { prerequisite := obligation_targetCategoryRecognition_infty.id
    , dependent := obligation_realizationFunctors_infty.id
    , reason := "The infinity realization bridge must know which target stable category is being recognized."
    }
  , { prerequisite := obligation_targetRealizationStructureRecognition.id
    , dependent := obligation_structuredRealizationConsequence.id
    , reason := "Structured realization consequences depend on recognizing the target-side realization package."
    }
  , { prerequisite := obligation_factorizationShadowExtraction.id
    , dependent := obligation_realizationFunctors_pi0.id
    , reason := "The pi0 comparison shadow may only be claimed after the explicit infinity-to-pi0 factorization bridge is registered."
    }
  , { prerequisite := obligation_realizationFunctors_infty.id
    , dependent := obligation_structuredRealizationConsequence.id
    , reason := "The structured realization consequence is downstream of the infinity comparison / realization package."
    }
  , { prerequisite := obligation_structuredRealizationConsequence.id
    , dependent := obligation_realizationFunctors_pi0.id
    , reason := "The triangulated realization shadow is extracted after the structured realization consequence is available."
    }
  , { prerequisite := obligation_structuredRealizationConsequence.id
    , dependent := obligation_scalarShadowExtraction.id
    , reason := "Scalar-shadow extraction is a downstream consequence of structured realization faithfulness."
    }
  , { prerequisite := obligation_scalarShadowExtraction.id
    , dependent := obligation_finalPeriodFaithfulnessConsequence.id
    , reason := "The final period-faithfulness consequence is assembled only after scalar-shadow extraction is available."
    }
  ]

/-- Generic milestone bundle in the comparison roadmap. -/
structure ComparisonMilestone where
  stageName : String
  meaning : String
  requiredObligations : List MotivicObligationId
  upstreamMilestones : List String
  deriving Repr

def TraceSideReady : ComparisonMilestone where
  stageName := "TraceSideReady"
  meaning := "Source-side frontier factorization plus the split pi0/infinity trace-theoretic surfaces are registered."
  requiredObligations :=
    [ obligation_frontierUniversalProperty_pi0.id
    , obligation_frontierUniversalProperty_infty.id
    , obligation_triangulatedStable_pi0.id
    , obligation_triangulatedStable_infty.id
    , obligation_symmetricMonoidal_pi0.id
    , obligation_symmetricMonoidal_infty.id
    , obligation_a1Invariance_pi0.id
    , obligation_a1Invariance_infty.id
    , obligation_localization_pi0.id
    , obligation_localization_infty.id
    , obligation_nisnevichDescent_pi0.id
    , obligation_nisnevichDescent_infty.id
    , obligation_tateStabilization_pi0.id
    , obligation_tateStabilization_infty.id
    ]
  upstreamMilestones := []

def PiZeroComparisonReady : ComparisonMilestone where
  stageName := "PiZeroComparisonReady"
  meaning := "The triangulated / homotopy-category comparison shadow can be stated without overclaiming infinity coherence."
  requiredObligations :=
    [ obligation_frontierUniversalProperty_pi0.id
    , obligation_triangulatedStable_pi0.id
    , obligation_symmetricMonoidal_pi0.id
    , obligation_a1Invariance_pi0.id
    , obligation_localization_pi0.id
    , obligation_nisnevichDescent_pi0.id
    , obligation_tateStabilization_pi0.id
    , obligation_targetCategoryRecognition_pi0.id
    , obligation_realizationFunctors_pi0.id
    ]
  upstreamMilestones := [TraceSideReady.stageName]

def InfinityComparisonReady : ComparisonMilestone where
  stageName := "InfinityComparisonReady"
  meaning := "The full stable infinity comparison surface is registered, including source-side and target-side universal characterizations."
  requiredObligations :=
    [ obligation_frontierUniversalProperty_infty.id
    , obligation_triangulatedStable_infty.id
    , obligation_symmetricMonoidal_infty.id
    , obligation_a1Invariance_infty.id
    , obligation_localization_infty.id
    , obligation_nisnevichDescent_infty.id
    , obligation_tateStabilization_infty.id
    , obligation_targetCategoryRecognition_infty.id
    , obligation_targetUniversalPropertyRecognition.id
    ]
  upstreamMilestones := [TraceSideReady.stageName, PiZeroComparisonReady.stageName]

def RealizationBridgeReady : ComparisonMilestone where
  stageName := "RealizationBridgeReady"
  meaning := "The comparison/realization functor package is registered at both the infinity and pi0 surfaces."
  requiredObligations :=
    [ obligation_realizationFunctors_infty.id
    , obligation_realizationFunctors_pi0.id
    ]
  upstreamMilestones := [InfinityComparisonReady.stageName]

def SourceConstructionReady : ComparisonMilestone where
  stageName := "SourceConstructionReady"
  meaning := "All source-side construction obligations needed for comparison are registered."
  requiredObligations :=
    obligationsWithAuditClass MotivicObligationAuditClass.sourceConstruction |>.map MotivicComparisonObligation.id
  upstreamMilestones := []

def TargetRecognitionReady : ComparisonMilestone where
  stageName := "TargetRecognitionReady"
  meaning := "Target-side recognition obligations are registered, without yet claiming comparison."
  requiredObligations :=
    [ obligation_targetCategoryRecognition_pi0.id
    , obligation_targetCategoryRecognition_infty.id
    , obligation_targetUniversalPropertyRecognition.id
    , obligation_targetRealizationStructureRecognition.id
    ]
  upstreamMilestones := []

def PiZeroFactorizationReady : ComparisonMilestone where
  stageName := "PiZeroFactorizationReady"
  meaning := "Pi0 factorization is registered separately from the infinity factorization surface."
  requiredObligations :=
    [ obligation_frontierUniversalProperty_pi0.id
    , obligation_targetCategoryRecognition_pi0.id
    ]
  upstreamMilestones := [SourceConstructionReady.stageName, TargetRecognitionReady.stageName]

def InfinityFactorizationReady : ComparisonMilestone where
  stageName := "InfinityFactorizationReady"
  meaning := "Infinity factorization is registered separately from both the pi0 shadow and the downstream bridge."
  requiredObligations :=
    [ obligation_frontierUniversalProperty_infty.id
    , obligation_targetCategoryRecognition_infty.id
    , obligation_targetUniversalPropertyRecognition.id
    ]
  upstreamMilestones := [SourceConstructionReady.stageName, TargetRecognitionReady.stageName]

def FactorizationShadowExtractionReady : ComparisonMilestone where
  stageName := "FactorizationShadowExtractionReady"
  meaning := "The explicit infinity-to-pi0 factorization bridge is registered as a separate obligation."
  requiredObligations := [obligation_factorizationShadowExtraction.id]
  upstreamMilestones := [InfinityFactorizationReady.stageName]

def ComparisonFactorizationReady : ComparisonMilestone where
  stageName := "ComparisonFactorizationReady"
  meaning := "Source/target comparison factorization surfaces are registered at both pi0 and infinity levels."
  requiredObligations :=
    obligationsWithAuditClass MotivicObligationAuditClass.comparisonFactorization |>.map MotivicComparisonObligation.id
  upstreamMilestones :=
    [ PiZeroFactorizationReady.stageName
    , InfinityFactorizationReady.stageName
    , FactorizationShadowExtractionReady.stageName
    ]

def StructuredRealizationBridgeReady : ComparisonMilestone where
  stageName := "StructuredRealizationBridgeReady"
  meaning := "The structured realization bridge and comparison-data faithfulness consequences are registered."
  requiredObligations :=
    [ obligation_realizationFunctors_infty.id
    , obligation_realizationFunctors_pi0.id
    , obligation_structuredRealizationConsequence.id
    ]
  upstreamMilestones := [ComparisonFactorizationReady.stageName, InfinityComparisonReady.stageName]

def ScalarShadowConsequenceReady : ComparisonMilestone where
  stageName := "ScalarShadowConsequenceReady"
  meaning := "Scalar-shadow extraction from the structured realization bridge is registered."
  requiredObligations := [obligation_scalarShadowExtraction.id]
  upstreamMilestones := [StructuredRealizationBridgeReady.stageName]

def FinalComparisonEquivalenceAssemblyReady : ComparisonMilestone where
  stageName := "FinalComparisonEquivalenceAssemblyReady"
  meaning := "The assembly ladder separating source construction, target recognition, factorization, structured realization, and scalar-shadow extraction is registered."
  requiredObligations := [obligation_finalPeriodFaithfulnessConsequence.id]
  upstreamMilestones :=
    [ SourceConstructionReady.stageName
    , TargetRecognitionReady.stageName
    , ComparisonFactorizationReady.stageName
    , StructuredRealizationBridgeReady.stageName
    , ScalarShadowConsequenceReady.stageName
    ]

def PeriodFaithfulnessReady : ComparisonMilestone where
  stageName := "PeriodFaithfulnessReady"
  meaning := "The final period-faithfulness consequence is registered only after scalar-shadow extraction has been separated out."
  requiredObligations := [obligation_finalPeriodFaithfulnessConsequence.id]
  upstreamMilestones := [ScalarShadowConsequenceReady.stageName, FinalComparisonEquivalenceAssemblyReady.stageName]

def SourceStageRegistered : ComparisonMilestone := SourceConstructionReady

def TargetStageRegistered : ComparisonMilestone := TargetRecognitionReady

def ComparisonStageRegistered : ComparisonMilestone := ComparisonFactorizationReady

def StructuredRealizationStageRegistered : ComparisonMilestone := StructuredRealizationBridgeReady

def ScalarShadowStageRegistered : ComparisonMilestone := ScalarShadowConsequenceReady

def FinalAssemblyStageRegistered : ComparisonMilestone := FinalComparisonEquivalenceAssemblyReady

structure ComparisonProofFlow where
  sourceStage : ComparisonMilestone
  targetStage : ComparisonMilestone
  comparisonStage : ComparisonMilestone
  realizationStage : ComparisonMilestone
  scalarStage : ComparisonMilestone
  finalStage : ComparisonMilestone
  deriving Repr

def registeredComparisonProofFlow : ComparisonProofFlow where
  sourceStage := SourceStageRegistered
  targetStage := TargetStageRegistered
  comparisonStage := ComparisonStageRegistered
  realizationStage := StructuredRealizationStageRegistered
  scalarStage := ScalarShadowStageRegistered
  finalStage := FinalAssemblyStageRegistered

def comparisonFactorizationStageFeeds : List TargetRecognitionStageFeed :=
  [ { prerequisite := obligation_targetCategoryRecognition_pi0.id
    , dependentStage := PiZeroFactorizationReady.stageName
    , reason := "Pi0 target recognition feeds the pi0 factorization stage only."
    }
  , { prerequisite := obligation_frontierUniversalProperty_pi0.id
    , dependentStage := PiZeroFactorizationReady.stageName
    , reason := "Pi0 frontier universal property feeds the pi0 factorization stage."
    }
  , { prerequisite := obligation_targetCategoryRecognition_infty.id
    , dependentStage := InfinityFactorizationReady.stageName
    , reason := "Infinity target recognition feeds the infinity factorization stage."
    }
  , { prerequisite := obligation_targetUniversalPropertyRecognition.id
    , dependentStage := InfinityFactorizationReady.stageName
    , reason := "Infinity target universal-property recognition feeds the infinity factorization stage."
    }
  , { prerequisite := obligation_frontierUniversalProperty_infty.id
    , dependentStage := InfinityFactorizationReady.stageName
    , reason := "Infinity frontier universal property feeds the infinity factorization stage."
    }
  , { prerequisite := obligation_factorizationShadowExtraction.id
    , dependentStage := FactorizationShadowExtractionReady.stageName
    , reason := "The explicit bridge feeds the standalone factorization shadow-extraction stage."
    }
  , { prerequisite := obligation_factorizationShadowExtraction.id
    , dependentStage := PiZeroComparisonReady.stageName
    , reason := "The pi0 comparison shadow can only claim descent from infinity factorization through the explicit bridge."
    }
  ]

def comparisonFactorizationAuditEdges : List DependencyAuditEdge :=
  [ { source := obligation_frontierUniversalProperty_pi0.id
    , target := InfinityFactorizationReady.stageName
    , kind := .forbidden
    , reason := "Pi0 factorization cannot substitute for infinity factorization."
    }
  , { source := obligation_frontierUniversalProperty_pi0.id
    , target := InfinityComparisonReady.stageName
    , kind := .forbidden
    , reason := "Pi0 factorization must not feed infinity comparison readiness."
    }
  , { source := obligation_scalarShadowExtraction.id
    , target := PiZeroFactorizationReady.stageName
    , kind := .forbidden
    , reason := "Scalar-shadow extraction cannot feed the pi0 factorization layer."
    }
  , { source := obligation_scalarShadowExtraction.id
    , target := InfinityFactorizationReady.stageName
    , kind := .forbidden
    , reason := "Scalar-shadow extraction cannot feed the infinity factorization layer."
    }
  , { source := obligation_finalPeriodFaithfulnessConsequence.id
    , target := ComparisonFactorizationReady.stageName
    , kind := .forbidden
    , reason := "The final period-faithfulness consequence cannot feed any factorization layer."
    }
  ]

def comparisonMilestoneLadder : List ComparisonMilestone :=
  [TraceSideReady, PiZeroComparisonReady, InfinityComparisonReady,
    RealizationBridgeReady, SourceConstructionReady, TargetRecognitionReady,
    PiZeroFactorizationReady, InfinityFactorizationReady,
    FactorizationShadowExtractionReady, ComparisonFactorizationReady, StructuredRealizationBridgeReady,
    ScalarShadowConsequenceReady, FinalComparisonEquivalenceAssemblyReady,
    PeriodFaithfulnessReady]

def positiveStageFeeds : List TargetRecognitionStageFeed :=
  targetRecognitionStageFeeds ++ comparisonFactorizationStageFeeds

def forbiddenAuditEdges : List DependencyAuditEdge :=
  (targetRecognitionAuditEdges ++ comparisonFactorizationAuditEdges).filter
    fun edge => edge.kind = .forbidden

def HasPositiveDependency (source target : MotivicObligationId) : Prop :=
  ∃ edge ∈ motivicObligationDependencies,
    edge.prerequisite = source ∧ edge.dependent = target

def HasPositiveStageFeed (source : MotivicObligationId) (targetStage : String) : Prop :=
  ∃ edge ∈ positiveStageFeeds,
    edge.prerequisite = source ∧ edge.dependentStage = targetStage

def IsForbiddenFlow (source : MotivicObligationId) (targetStage : String) : Prop :=
  ∃ edge ∈ forbiddenAuditEdges,
    edge.source = source ∧ edge.target = targetStage

def MilestonePrerequisitesSatisfied (available : List String) (milestone : ComparisonMilestone) : Prop :=
  ∀ prerequisite ∈ milestone.upstreamMilestones, prerequisite ∈ available

theorem hasPositiveDependency_iff (source target : MotivicObligationId) :
    HasPositiveDependency source target ↔
      ∃ edge ∈ motivicObligationDependencies,
        edge.prerequisite = source ∧ edge.dependent = target := by
  rfl

theorem hasPositiveStageFeed_iff (source : MotivicObligationId) (targetStage : String) :
    HasPositiveStageFeed source targetStage ↔
      ∃ edge ∈ positiveStageFeeds,
        edge.prerequisite = source ∧ edge.dependentStage = targetStage := by
  rfl

theorem isForbiddenFlow_iff (source : MotivicObligationId) (targetStage : String) :
    IsForbiddenFlow source targetStage ↔
      ∃ edge ∈ forbiddenAuditEdges,
        edge.source = source ∧ edge.target = targetStage := by
  rfl

theorem scalar_shadow_extraction_downstream_of_structured_realization :
    HasPositiveDependency obligation_structuredRealizationConsequence.id
      obligation_scalarShadowExtraction.id := by
  refine ⟨{ prerequisite := obligation_structuredRealizationConsequence.id
          , dependent := obligation_scalarShadowExtraction.id
          , reason := "Scalar-shadow extraction is a downstream consequence of structured realization faithfulness."
          }, ?_, rfl, rfl⟩
  simp [motivicObligationDependencies]

theorem final_period_faithfulness_downstream_of_scalar_shadow :
    HasPositiveDependency obligation_scalarShadowExtraction.id
      obligation_finalPeriodFaithfulnessConsequence.id := by
  refine ⟨{ prerequisite := obligation_scalarShadowExtraction.id
          , dependent := obligation_finalPeriodFaithfulnessConsequence.id
          , reason := "The final period-faithfulness consequence is assembled only after scalar-shadow extraction is available."
          }, ?_, rfl, rfl⟩
  simp [motivicObligationDependencies]

theorem pi0_recognition_does_not_feed_infinity_comparison_readiness :
    ¬ HasPositiveStageFeed obligation_targetCategoryRecognition_pi0.id InfinityComparisonReady.stageName := by
  simp [HasPositiveStageFeed, positiveStageFeeds, targetRecognitionStageFeeds,
    comparisonFactorizationStageFeeds, InfinityComparisonReady]
  repeat' constructor <;> decide

theorem pi0_factorization_does_not_feed_infinity_factorization :
    ¬ HasPositiveStageFeed obligation_frontierUniversalProperty_pi0.id InfinityFactorizationReady.stageName := by
  simp [HasPositiveStageFeed, positiveStageFeeds, targetRecognitionStageFeeds,
    comparisonFactorizationStageFeeds, InfinityFactorizationReady]
  repeat' constructor <;> decide

theorem pi0_factorization_does_not_feed_infinity_comparison_readiness :
    ¬ HasPositiveStageFeed obligation_frontierUniversalProperty_pi0.id InfinityComparisonReady.stageName := by
  simp [HasPositiveStageFeed, positiveStageFeeds, targetRecognitionStageFeeds,
    comparisonFactorizationStageFeeds, InfinityComparisonReady]
  repeat' constructor <;> decide

theorem scalar_shadow_extraction_does_not_feed_target_recognition :
    ¬ HasPositiveStageFeed obligation_scalarShadowExtraction.id TargetRecognitionReady.stageName := by
  simp [HasPositiveStageFeed, positiveStageFeeds, targetRecognitionStageFeeds,
    comparisonFactorizationStageFeeds, TargetRecognitionReady]
  repeat' constructor <;> decide

theorem scalar_shadow_extraction_does_not_feed_pi0_factorization :
    ¬ HasPositiveStageFeed obligation_scalarShadowExtraction.id PiZeroFactorizationReady.stageName := by
  simp [HasPositiveStageFeed, positiveStageFeeds, targetRecognitionStageFeeds,
    comparisonFactorizationStageFeeds, PiZeroFactorizationReady]
  repeat' constructor <;> decide

theorem scalar_shadow_extraction_does_not_feed_infinity_factorization :
    ¬ HasPositiveStageFeed obligation_scalarShadowExtraction.id InfinityFactorizationReady.stageName := by
  simp [HasPositiveStageFeed, positiveStageFeeds, targetRecognitionStageFeeds,
    comparisonFactorizationStageFeeds, InfinityFactorizationReady]
  repeat' constructor <;> decide

theorem final_period_faithfulness_does_not_feed_comparison_factorization :
    ¬ HasPositiveStageFeed obligation_finalPeriodFaithfulnessConsequence.id ComparisonFactorizationReady.stageName := by
  simp [HasPositiveStageFeed, positiveStageFeeds, targetRecognitionStageFeeds,
    comparisonFactorizationStageFeeds, ComparisonFactorizationReady]
  repeat' constructor <;> decide

theorem forbidden_flows_absent_from_positive_stage_feeds :
    ∀ edge ∈ forbiddenAuditEdges,
      ¬ HasPositiveStageFeed edge.source edge.target := by
  intro edge hedge
  simp [forbiddenAuditEdges, targetRecognitionAuditEdges, comparisonFactorizationAuditEdges] at hedge
  rcases hedge with h | h | h | h | h | h | h | h
  · subst h
    exact pi0_recognition_does_not_feed_infinity_comparison_readiness
  · subst h
    exact scalar_shadow_extraction_does_not_feed_target_recognition
  · subst h
    exact final_period_faithfulness_does_not_feed_comparison_factorization
  · subst h
    exact pi0_factorization_does_not_feed_infinity_factorization
  · subst h
    exact pi0_factorization_does_not_feed_infinity_comparison_readiness
  · subst h
    exact scalar_shadow_extraction_does_not_feed_pi0_factorization
  · subst h
    exact scalar_shadow_extraction_does_not_feed_infinity_factorization
  · subst h
    exact final_period_faithfulness_does_not_feed_comparison_factorization

theorem every_forbidden_edge_absent_from_positive_dependency_lists :
    ∀ edge ∈ forbiddenAuditEdges,
      ¬ HasPositiveStageFeed edge.source edge.target :=
  forbidden_flows_absent_from_positive_stage_feeds

theorem piZeroFactorizationReady_prerequisites_satisfied :
    MilestonePrerequisitesSatisfied
      [SourceConstructionReady.stageName, TargetRecognitionReady.stageName]
      PiZeroFactorizationReady := by
  intro prerequisite hprereq
  simpa [PiZeroFactorizationReady, SourceConstructionReady, TargetRecognitionReady] using hprereq

theorem infinityFactorizationReady_prerequisites_satisfied :
    MilestonePrerequisitesSatisfied
      [SourceConstructionReady.stageName, TargetRecognitionReady.stageName]
      InfinityFactorizationReady := by
  intro prerequisite hprereq
  simpa [InfinityFactorizationReady, SourceConstructionReady, TargetRecognitionReady] using hprereq

theorem comparison_readiness_package_prerequisites_satisfied :
    MilestonePrerequisitesSatisfied
      [ PiZeroFactorizationReady.stageName
      , InfinityFactorizationReady.stageName
      , FactorizationShadowExtractionReady.stageName
      ]
      ComparisonFactorizationReady := by
  intro prerequisite hprereq
  simpa [ComparisonFactorizationReady] using hprereq

theorem structured_realization_stage_prerequisites_satisfied :
    MilestonePrerequisitesSatisfied
      [ComparisonFactorizationReady.stageName, InfinityComparisonReady.stageName]
      StructuredRealizationBridgeReady := by
  intro prerequisite hprereq
  simpa [StructuredRealizationBridgeReady] using hprereq

theorem periodFaithfulnessReady_prerequisites_satisfied :
    MilestonePrerequisitesSatisfied
      [ScalarShadowConsequenceReady.stageName, FinalComparisonEquivalenceAssemblyReady.stageName]
      PeriodFaithfulnessReady := by
  intro prerequisite hprereq
  simpa [PeriodFaithfulnessReady] using hprereq

theorem final_assembly_depends_only_on_upstream_structured_and_scalar_layers :
    MilestonePrerequisitesSatisfied
      [ SourceConstructionReady.stageName
      , TargetRecognitionReady.stageName
      , ComparisonFactorizationReady.stageName
      , StructuredRealizationBridgeReady.stageName
      , ScalarShadowConsequenceReady.stageName
      ]
      FinalComparisonEquivalenceAssemblyReady := by
  intro prerequisite hprereq
  simpa [FinalComparisonEquivalenceAssemblyReady] using hprereq

theorem structured_realization_and_scalar_shadow_support_period_faithfulness :
    MilestonePrerequisitesSatisfied
      [ ScalarShadowConsequenceReady.stageName
      , FinalComparisonEquivalenceAssemblyReady.stageName
      ]
      PeriodFaithfulnessReady :=
  periodFaithfulnessReady_prerequisites_satisfied

def SourceTracePackage.SourceConstructionWitness.SupportsObligationId
  {S : SourceTracePackage}
    (W : SourceTracePackage.SourceConstructionWitness S)
    (obligationId : MotivicObligationId) : Prop :=
  (obligationId = obligation_symmetricMonoidal_pi0.id ∧ W.symmetricMonoidalPiZero) ∨
    (obligationId = obligation_symmetricMonoidal_infty.id ∧ W.symmetricMonoidalInfinity) ∨
    (obligationId = obligation_triangulatedStable_pi0.id ∧ W.triangulatedStablePiZero) ∨
    (obligationId = obligation_triangulatedStable_infty.id ∧ W.triangulatedStableInfinity) ∨
    (obligationId = obligation_a1Invariance_pi0.id ∧ W.a1InvariancePiZero) ∨
    (obligationId = obligation_a1Invariance_infty.id ∧ W.a1InvarianceInfinity) ∨
    (obligationId = obligation_nisnevichDescent_pi0.id ∧ W.nisnevichDescentPiZero) ∨
    (obligationId = obligation_nisnevichDescent_infty.id ∧ W.nisnevichDescentInfinity) ∨
    (obligationId = obligation_localization_pi0.id ∧ W.localizationPiZero) ∨
    (obligationId = obligation_localization_infty.id ∧ W.localizationInfinity) ∨
    (obligationId = obligation_tateStabilization_pi0.id ∧ W.tateStabilizationPiZero) ∨
    (obligationId = obligation_tateStabilization_infty.id ∧ W.tateStabilizationInfinity)

theorem sourceTracePackage_supports_sourceConstructionReady
    (S : SourceTracePackage)
    (W : SourceTracePackage.SourceConstructionWitness S) :
    MilestonePrerequisitesSatisfied [] SourceConstructionReady ∧
      ∀ obligationId : MotivicObligationId,
        obligationId ∈ SourceConstructionReady.requiredObligations →
          W.SupportsObligationId obligationId := by
  refine ⟨?_, ?_⟩
  · intro prerequisite hpre
    simp [SourceConstructionReady] at hpre
  · intro obligationId hid
    have hsource :
        ∃ obligation : MotivicComparisonObligation,
          (obligation ∈ motivicComparisonObligationMap ∧
              obligation.auditClass = MotivicObligationAuditClass.sourceConstruction) ∧
            obligation.id = obligationId := by
      simpa [SourceConstructionReady, List.mem_map, mem_obligationsWithAuditClass_iff] using hid
    rcases hsource with ⟨obligation, ⟨hmem, haudit⟩, hid_eq⟩
    simp [motivicComparisonObligationMap] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso
      simp [obligation_frontierUniversalProperty_pi0] at haudit
    · exfalso
      simp [obligation_frontierUniversalProperty_infty] at haudit
    · exfalso
      simp [obligation_factorizationShadowExtraction] at haudit
    · exact Or.inl ⟨hid_eq.symm, W.symmetricMonoidalPiZero_holds⟩
    · exact Or.inr <| Or.inl ⟨hid_eq.symm, W.symmetricMonoidalInfinity_holds⟩
    · exact Or.inr <| Or.inr <| Or.inl ⟨hid_eq.symm, W.triangulatedStablePiZero_holds⟩
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨hid_eq.symm, W.triangulatedStableInfinity_holds⟩
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨hid_eq.symm, W.a1InvariancePiZero_holds⟩
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨hid_eq.symm, W.a1InvarianceInfinity_holds⟩
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨hid_eq.symm, W.nisnevichDescentPiZero_holds⟩
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨hid_eq.symm, W.nisnevichDescentInfinity_holds⟩
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨hid_eq.symm, W.localizationPiZero_holds⟩
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨hid_eq.symm, W.localizationInfinity_holds⟩
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨hid_eq.symm, W.tateStabilizationPiZero_holds⟩
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨hid_eq.symm, W.tateStabilizationInfinity_holds⟩
    · exfalso
      simp [obligation_targetCategoryRecognition_pi0] at haudit
    · exfalso
      simp [obligation_targetCategoryRecognition_infty] at haudit
    · exfalso
      simp [obligation_targetUniversalPropertyRecognition] at haudit
    · exfalso
      simp [obligation_targetRealizationStructureRecognition] at haudit
    · exfalso
      simp [obligation_realizationFunctors_pi0] at haudit
    · exfalso
      simp [obligation_realizationFunctors_infty] at haudit
    · exfalso
      simp [obligation_structuredRealizationConsequence] at haudit
    · exfalso
      simp [obligation_scalarShadowExtraction] at haudit
    · exfalso
      simp [obligation_finalPeriodFaithfulnessConsequence] at haudit

def piZeroComparisonRequiredObligationIds : List MotivicObligationId :=
  [ obligation_frontierUniversalProperty_pi0.id
  , obligation_triangulatedStable_pi0.id
  , obligation_symmetricMonoidal_pi0.id
  , obligation_a1Invariance_pi0.id
  , obligation_localization_pi0.id
  , obligation_nisnevichDescent_pi0.id
  , obligation_tateStabilization_pi0.id
  , obligation_targetCategoryRecognition_pi0.id
  , obligation_realizationFunctors_pi0.id
  ]

def infinityComparisonRequiredObligationIds : List MotivicObligationId :=
  [ obligation_frontierUniversalProperty_infty.id
  , obligation_triangulatedStable_infty.id
  , obligation_symmetricMonoidal_infty.id
  , obligation_a1Invariance_infty.id
  , obligation_localization_infty.id
  , obligation_nisnevichDescent_infty.id
  , obligation_tateStabilization_infty.id
  , obligation_targetCategoryRecognition_infty.id
  , obligation_targetUniversalPropertyRecognition.id
  ]

def realizationBridgeRequiredObligationIds : List MotivicObligationId :=
  [ obligation_realizationFunctors_infty.id
  , obligation_realizationFunctors_pi0.id
  ]

def structuredRealizationBridgeRequiredObligationIds : List MotivicObligationId :=
  [ obligation_realizationFunctors_infty.id
  , obligation_realizationFunctors_pi0.id
  , obligation_structuredRealizationConsequence.id
  ]

def scalarShadowConsequenceRequiredObligationIds : List MotivicObligationId :=
  [ obligation_scalarShadowExtraction.id ]

def periodFaithfulnessUpstreamMilestoneIds : List String :=
  [ ScalarShadowConsequenceReady.stageName
  , FinalComparisonEquivalenceAssemblyReady.stageName
  ]

def finalComparisonEquivalenceAssemblyUpstreamMilestoneIds : List String :=
  [ SourceConstructionReady.stageName
  , TargetRecognitionReady.stageName
  , ComparisonFactorizationReady.stageName
  , StructuredRealizationBridgeReady.stageName
  , ScalarShadowConsequenceReady.stageName
  ]

def HasTargetRecognitionStageFeed (source : MotivicObligationId) (targetStage : String) : Prop :=
  ∃ edge ∈ targetRecognitionStageFeeds,
    edge.prerequisite = source ∧ edge.dependentStage = targetStage

theorem hasTargetRecognitionStageFeed_iff (source : MotivicObligationId) (targetStage : String) :
    HasTargetRecognitionStageFeed source targetStage ↔
      ∃ edge ∈ targetRecognitionStageFeeds,
        edge.prerequisite = source ∧ edge.dependentStage = targetStage := by
  rfl

theorem theorem_pi0_comparison_obligations_registered :
    ∀ obligationId : MotivicObligationId,
      obligationId ∈ PiZeroComparisonReady.requiredObligations ↔
        obligationId ∈ piZeroComparisonRequiredObligationIds := by
  intro obligationId
  simp [PiZeroComparisonReady, piZeroComparisonRequiredObligationIds]

theorem theorem_infinity_comparison_obligations_registered :
    ∀ obligationId : MotivicObligationId,
      obligationId ∈ InfinityComparisonReady.requiredObligations ↔
        obligationId ∈ infinityComparisonRequiredObligationIds := by
  intro obligationId
  simp [InfinityComparisonReady, infinityComparisonRequiredObligationIds]

theorem theorem_realization_bridge_obligations_registered :
    ∀ obligationId : MotivicObligationId,
      obligationId ∈ RealizationBridgeReady.requiredObligations ↔
        obligationId ∈ realizationBridgeRequiredObligationIds := by
  intro obligationId
  simp [RealizationBridgeReady, realizationBridgeRequiredObligationIds]

theorem theorem_target_recognition_stage_feeds_registered :
    ∀ source : MotivicObligationId,
      ∀ targetStage : String,
        HasTargetRecognitionStageFeed source targetStage ↔
          (source = obligation_targetCategoryRecognition_pi0.id ∧
            targetStage = PiZeroComparisonReady.stageName) ∨
          (source = obligation_targetCategoryRecognition_infty.id ∧
            targetStage = InfinityComparisonReady.stageName) ∨
          (source = obligation_targetUniversalPropertyRecognition.id ∧
            targetStage = ComparisonFactorizationReady.stageName) ∨
          (source = obligation_targetRealizationStructureRecognition.id ∧
            targetStage = StructuredRealizationBridgeReady.stageName) := by
  intro source targetStage
  constructor <;> intro h
  · simpa [HasTargetRecognitionStageFeed, targetRecognitionStageFeeds,
      PiZeroComparisonReady, InfinityComparisonReady, ComparisonFactorizationReady,
      StructuredRealizationBridgeReady, eq_comm] using h
  · simpa [HasTargetRecognitionStageFeed, targetRecognitionStageFeeds,
      PiZeroComparisonReady, InfinityComparisonReady, ComparisonFactorizationReady,
      StructuredRealizationBridgeReady, eq_comm] using h

theorem theorem_structured_realization_bridge_obligations_registered :
    ∀ obligationId : MotivicObligationId,
      obligationId ∈ StructuredRealizationBridgeReady.requiredObligations ↔
        obligationId ∈ structuredRealizationBridgeRequiredObligationIds := by
  intro obligationId
  simp [StructuredRealizationBridgeReady,
    structuredRealizationBridgeRequiredObligationIds]

theorem theorem_scalar_shadow_consequence_obligations_registered :
    ∀ obligationId : MotivicObligationId,
      obligationId ∈ ScalarShadowConsequenceReady.requiredObligations ↔
        obligationId ∈ scalarShadowConsequenceRequiredObligationIds := by
  intro obligationId
  simp [ScalarShadowConsequenceReady, scalarShadowConsequenceRequiredObligationIds]

theorem theorem_no_scalar_shadow_used_in_structured_comparison_registered :
    noScalarToStructuredConstraint ∈ comparisonRoadmapNoncircularityConstraints := by
  simp [comparisonRoadmapNoncircularityConstraints, noScalarToStructuredConstraint]

theorem theorem_pi0_target_recognition_not_used_as_infinity_substitute_registered :
    { source := obligation_targetCategoryRecognition_pi0.id
    , target := InfinityComparisonReady.stageName
    , kind := DependencyAuditKind.forbidden
    , reason := "Pi0 target recognition cannot substitute for infinity target recognition."
    } ∈ targetRecognitionAuditEdges := by
  simp [targetRecognitionAuditEdges, InfinityComparisonReady]

theorem theorem_scalar_shadow_cannot_feed_target_recognition_registered :
    { source := obligation_scalarShadowExtraction.id
    , target := TargetRecognitionReady.stageName
    , kind := DependencyAuditKind.forbidden
    , reason := "Scalar-shadow extraction is downstream and cannot feed target recognition."
    } ∈ targetRecognitionAuditEdges := by
  simp [targetRecognitionAuditEdges, TargetRecognitionReady]

theorem theorem_period_faithfulness_cannot_feed_comparison_factorization_registered :
    { source := obligation_finalPeriodFaithfulnessConsequence.id
    , target := ComparisonFactorizationReady.stageName
    , kind := DependencyAuditKind.forbidden
    , reason := "The final period-faithfulness consequence cannot feed comparison factorization."
    } ∈ targetRecognitionAuditEdges := by
  simp [targetRecognitionAuditEdges, ComparisonFactorizationReady]

theorem theorem_period_faithfulness_chain_is_role_separated_registered :
    ∀ milestoneId : String,
      milestoneId ∈ PeriodFaithfulnessReady.upstreamMilestones ↔
        milestoneId ∈ periodFaithfulnessUpstreamMilestoneIds := by
  intro milestoneId
  simp [PeriodFaithfulnessReady, periodFaithfulnessUpstreamMilestoneIds]

theorem theorem_comparison_roadmap_noncircularity_audit_registered :
    ∀ constraint : NoncircularityConstraint,
      constraint ∈ comparisonRoadmapNoncircularityConstraints ↔
        constraint = noScalarToStructuredConstraint ∨
        constraint = noFinalAssemblyToComparisonConstraint ∨
        constraint = noDirectSourceToTargetRecognitionConstraint ∨
        constraint = noExternalAsSourceConstraint := by
  intro constraint
  simp [comparisonRoadmapNoncircularityConstraints]

theorem theorem_final_comparison_equivalence_assembly_registered :
    ∀ milestoneId : String,
      milestoneId ∈ FinalComparisonEquivalenceAssemblyReady.upstreamMilestones ↔
        milestoneId ∈ finalComparisonEquivalenceAssemblyUpstreamMilestoneIds := by
  intro milestoneId
  simp [FinalComparisonEquivalenceAssemblyReady,
    finalComparisonEquivalenceAssemblyUpstreamMilestoneIds]

theorem theorem_period_faithfulness_obligation_chain_registered :
    ∀ milestoneId : String,
      milestoneId ∈ PeriodFaithfulnessReady.upstreamMilestones ↔
        milestoneId ∈ periodFaithfulnessUpstreamMilestoneIds := by
  intro milestoneId
  simp [PeriodFaithfulnessReady, periodFaithfulnessUpstreamMilestoneIds]

end LayerD
end TraceCalc