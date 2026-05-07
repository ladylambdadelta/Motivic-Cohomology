import TraceCalc.LayerD.UniversalProperty

namespace TraceCalc
namespace LayerD

abbrev MotivicObligationId := String

/-- Provenance classification for comparison obligations.
`internalTraceCalculus` = source-side theorem expected from the trace formalization.
`externalMotivicTheorem` = external motivic input that must later be internalized.
`futureComparisonTheorem` = bridge statement connecting the two sides. -/
inductive MotivicObligationOrigin
  | internalTraceCalculus
  | externalMotivicTheorem
  | futureComparisonTheorem
  deriving DecidableEq, Repr

/-- Noncircularity audit classification for roadmap entries. -/
inductive MotivicObligationAuditClass
  | sourceConstruction
  | targetRecognition
  | comparisonFactorization
  | structuredRealization
  | scalarShadowExtraction
  | finalAssembly
  | externalInputToInternalize
  deriving DecidableEq, Repr

abbrev TheoremRole := MotivicObligationAuditClass

/-- Level classification for comparison obligations.
`pi0Only` = only the homotopy-category / triangulated-shadow statement is in scope.
`inftyOnly` = only the full stable `infty`-categorical statement is in scope.
`both` = the obligation must be kept visible at both levels.
`bridgeFromInfinityToPi0` = the obligation is part of the passage from higher semantics
to the classical / `pi_0` consequences. -/
inductive MotivicObligationLevel
  | pi0Only
  | inftyOnly
  | both
  | bridgeFromInfinityToPi0
  deriving DecidableEq, Repr

/-- How a target-recognition entry is allowed to feed the comparison roadmap. -/
inductive TargetRecognitionFeedLevel
  | pi0ComparisonOnly
  | infinityComparisonOnly
  | both
  | bridgeFromInfinityToPi0
  deriving DecidableEq, Repr

/-- How a comparison-factorization entry is allowed to feed the roadmap. -/
inductive ComparisonFactorizationFeedLevel
  | pi0FactorizationOnly
  | infinityFactorizationOnly
  | bridgeFromInfinityToPi0
  | both
  deriving DecidableEq, Repr

/-- Lean/Tex registry entry for one motivic comparison obligation. -/
structure MotivicComparisonObligation where
  key : String
  texAnchor : String
  leanAnchor : String
  origin : MotivicObligationOrigin
  level : MotivicObligationLevel
  auditClass : MotivicObligationAuditClass
  summary : String
  dependsOn : List String
  deriving Repr

/-- Registry entry recording where a target-recognition obligation may feed the roadmap. -/
structure TargetRecognitionFeed where
  obligation : MotivicObligationId
  feeds : TargetRecognitionFeedLevel
  reason : String
  deriving Repr

/-- Registry entry recording where a comparison-factorization obligation may feed the roadmap. -/
structure ComparisonFactorizationFeed where
  obligation : MotivicObligationId
  feeds : ComparisonFactorizationFeedLevel
  reason : String
  deriving Repr

namespace MotivicComparisonObligation

def id (obligation : MotivicComparisonObligation) : MotivicObligationId :=
  obligation.key

end MotivicComparisonObligation

def obligation_frontierUniversalProperty_pi0 : MotivicComparisonObligation where
  key := "frontier-universal-property-pi0"
  texAnchor := "thm:universal-trace-motivic-semantics"
  leanAnchor := "theorem_frontier_pi0_universal_property_surface"
  origin := .internalTraceCalculus
  level := .pi0Only
  auditClass := .comparisonFactorization
  summary := "Pi0-level frontier universal property: factorization and initiality only in the triangulated / homotopy-category shadow."
  dependsOn := ["thm:classical-universal-mapping"]

def obligation_frontierUniversalProperty_infty : MotivicComparisonObligation where
  key := "frontier-universal-property-infinity"
  texAnchor := "rem:infty-comparison"
  leanAnchor := "theorem_frontier_infinity_universal_property_surface"
  origin := .internalTraceCalculus
  level := .inftyOnly
  auditClass := .comparisonFactorization
  summary := "Infinity-level frontier universal property: higher coherent factorization into stable semantic targets."
  dependsOn := ["thm:universal-trace-motivic-semantics", "rem:infty-categorical-completion"]

def obligation_factorizationShadowExtraction : MotivicComparisonObligation where
  key := "factorization-shadow-extraction"
  texAnchor := "cor:comparison-shadow-extraction"
  leanAnchor := "motivicComparisonObligation_factorizationShadowExtraction"
  origin := .futureComparisonTheorem
  level := .bridgeFromInfinityToPi0
  auditClass := .comparisonFactorization
  summary := "Explicit bridge obligation stating that infinity-level factorization induces the pi0 comparison shadow only through a named descent step."
  dependsOn := ["cor:comparison-shadow-extraction", "thm:realization-comparison"]

def obligation_symmetricMonoidal_pi0 : MotivicComparisonObligation where
  key := "symmetric-monoidal-structure-pi0"
  texAnchor := "thm:symmetric-monoidal-from-envelope"
  leanAnchor := "motivicComparisonObligation_symmetricMonoidal_pi0"
  origin := .internalTraceCalculus
  level := .pi0Only
  auditClass := .sourceConstruction
  summary := "Pi0 shadow of symmetric monoidal structure for the completed trace category."
  dependsOn := ["const:stable-completion-model"]

def obligation_symmetricMonoidal_infty : MotivicComparisonObligation where
  key := "symmetric-monoidal-structure-infinity"
  texAnchor := "rem:infty-categorical-completion"
  leanAnchor := "motivicComparisonObligation_symmetricMonoidal_infty"
  origin := .internalTraceCalculus
  level := .inftyOnly
  auditClass := .sourceConstruction
  summary := "Infinity-level coherent symmetric monoidal structure for the stable semantic target."
  dependsOn := ["thm:symmetric-monoidal-from-envelope", "rem:infty-categorical-completion"]

def obligation_triangulatedStable_pi0 : MotivicComparisonObligation where
  key := "triangulated-stable-structure-pi0"
  texAnchor := "thm:verdier-axioms"
  leanAnchor := "motivicComparisonObligation_triangulatedStable_pi0"
  origin := .internalTraceCalculus
  level := .pi0Only
  auditClass := .sourceConstruction
  summary := "Pi0 shadow of triangulated/stable structure: Verdier triangulated data in the homotopy-category shadow."
  dependsOn := ["const:stable-completion-model", "rem:infty-categorical-completion"]

def obligation_triangulatedStable_infty : MotivicComparisonObligation where
  key := "triangulated-stable-structure-infinity"
  texAnchor := "rem:infty-categorical-completion"
  leanAnchor := "motivicComparisonObligation_triangulatedStable_infty"
  origin := .internalTraceCalculus
  level := .inftyOnly
  auditClass := .sourceConstruction
  summary := "Infinity-level stable-category structure, not merely its Verdier shadow."
  dependsOn := ["thm:verdier-axioms", "rem:infty-categorical-completion"]

def obligation_a1Invariance_pi0 : MotivicComparisonObligation where
  key := "a1-invariance-pi0"
  texAnchor := "thm:aone-rigidity"
  leanAnchor := "motivicComparisonObligation_a1Invariance_pi0"
  origin := .internalTraceCalculus
  level := .pi0Only
  auditClass := .sourceConstruction
  summary := "Pi0 shadow of A1-invariance: contraction/equivalence visible in the triangulated shadow."
  dependsOn := ["lem:join-desc-a1"]

def obligation_a1Invariance_infty : MotivicComparisonObligation where
  key := "a1-invariance-infinity"
  texAnchor := "rem:higher-reading-geometric-theorems"
  leanAnchor := "motivicComparisonObligation_a1Invariance_infty"
  origin := .internalTraceCalculus
  level := .inftyOnly
  auditClass := .sourceConstruction
  summary := "Infinity-level A1-localization at the stable semantic level, beyond the pi0 contraction shadow."
  dependsOn := ["thm:aone-rigidity", "rem:higher-reading-geometric-theorems", "rem:infty-categorical-completion"]

def obligation_nisnevichDescent_pi0 : MotivicComparisonObligation where
  key := "nisnevich-descent-pi0"
  texAnchor := "thm:internal-nisnevich-descent"
  leanAnchor := "motivicComparisonObligation_nisnevichDescent_pi0"
  origin := .internalTraceCalculus
  level := .pi0Only
  auditClass := .sourceConstruction
  summary := "Pi0 shadow of Nisnevich descent: Mayer-Vietoris / distinguished-square behavior in the triangulated shadow."
  dependsOn := ["lem:nisnevich-cone-model"]

def obligation_nisnevichDescent_infty : MotivicComparisonObligation where
  key := "nisnevich-descent-infinity"
  texAnchor := "prop:nisnevich-cech-exactness"
  leanAnchor := "motivicComparisonObligation_nisnevichDescent_infty"
  origin := .internalTraceCalculus
  level := .inftyOnly
  auditClass := .sourceConstruction
  summary := "Infinity-level Nisnevich descent: descent encoded as higher limit / sheaf data rather than only its triangulated shadow."
  dependsOn := ["thm:internal-nisnevich-descent", "prop:nisnevich-cech-exactness", "rem:higher-reading-geometric-theorems"]

def obligation_localization_pi0 : MotivicComparisonObligation where
  key := "localization-pi0"
  texAnchor := "thm:internal-localization"
  leanAnchor := "motivicComparisonObligation_localization_pi0"
  origin := .internalTraceCalculus
  level := .pi0Only
  auditClass := .sourceConstruction
  summary := "Pi0 shadow of localization: Verdier / distinguished-triangle localization in the homotopy-category shadow."
  dependsOn := ["thm:internal-localization"]

def obligation_localization_infty : MotivicComparisonObligation where
  key := "localization-infinity"
  texAnchor := "prop:localization-functoriality"
  leanAnchor := "motivicComparisonObligation_localization_infty"
  origin := .internalTraceCalculus
  level := .inftyOnly
  auditClass := .sourceConstruction
  summary := "Infinity-level localization: stable cofiber/fiber exactness and functorial localization data."
  dependsOn := ["thm:internal-localization", "prop:localization-functoriality", "rem:higher-reading-geometric-theorems"]

def obligation_tateStabilization_pi0 : MotivicComparisonObligation where
  key := "p1-tate-stabilization-pi0"
  texAnchor := "thm:internal-stabilization"
  leanAnchor := "motivicComparisonObligation_tateStabilization_pi0"
  origin := .internalTraceCalculus
  level := .pi0Only
  auditClass := .sourceConstruction
  summary := "Pi0 shadow of Tate/P1 stabilization: invertibility of the Tate object in the triangulated shadow."
  dependsOn := ["thm:internal-stabilization", "lem:tate-twist-exact-autoequivalence"]

def obligation_tateStabilization_infty : MotivicComparisonObligation where
  key := "p1-tate-stabilization-infinity"
  texAnchor := "lem:internal-presentation-package"
  leanAnchor := "motivicComparisonObligation_tateStabilization_infty"
  origin := .internalTraceCalculus
  level := .inftyOnly
  auditClass := .sourceConstruction
  summary := "Infinity-level Tate/P1 stabilization: symmetric monoidal stabilization and inversion at the stable semantic level."
  dependsOn := ["thm:internal-stabilization", "lem:internal-presentation-package", "rem:infty-categorical-completion"]

def obligation_targetCategoryRecognition_pi0 : MotivicComparisonObligation where
  key := "target-category-recognition-pi0"
  texAnchor := "cor:universal-property-identification"
  leanAnchor := "motivicComparisonObligation_targetCategoryRecognition_pi0"
  origin := .externalMotivicTheorem
  level := .pi0Only
  auditClass := .targetRecognition
  summary := "Target-category recognition at the pi0 level: identify the classical motivic target seen by the triangulated shadow."
  dependsOn := ["cor:universal-property-identification", "thm:mmlq-initiality"]

def obligation_targetCategoryRecognition_infty : MotivicComparisonObligation where
  key := "target-category-recognition-infinity"
  texAnchor := "rem:infty-comparison"
  leanAnchor := "motivicComparisonObligation_targetCategoryRecognition_infty"
  origin := .externalMotivicTheorem
  level := .inftyOnly
  auditClass := .targetRecognition
  summary := "Target-category recognition at the infinity level: identify the stable motivic target category, not merely its pi0 shadow."
  dependsOn := ["rem:infty-comparison", "rem:infty-categorical-completion"]

def obligation_targetUniversalPropertyRecognition : MotivicComparisonObligation where
  key := "target-universal-property-recognition"
  texAnchor := "rem:infty-comparison"
  leanAnchor := "motivicComparisonObligation_targetUniversalPropertyRecognition"
  origin := .externalMotivicTheorem
  level := .inftyOnly
  auditClass := .externalInputToInternalize
  summary := "External target universal-property recognition that must be internalized or kept explicitly external."
  dependsOn := ["Robalo2015", "rem:infty-comparison"]

def obligation_targetRealizationStructureRecognition : MotivicComparisonObligation where
  key := "target-realization-structure-recognition"
  texAnchor := "rem:infty-realization"
  leanAnchor := "motivicComparisonObligation_targetRealizationStructureRecognition"
  origin := .externalMotivicTheorem
  level := .inftyOnly
  auditClass := .targetRecognition
  summary := "Recognition of the target-side realization structure needed before the structured realization bridge can be stated honestly."
  dependsOn := ["rem:infty-realization", "cor:internal-period-faithfulness"]

def obligation_realizationFunctors_pi0 : MotivicComparisonObligation where
  key := "realization-functors-pi0"
  texAnchor := "thm:realization-comparison"
  leanAnchor := "motivicComparisonObligation_realizationFunctors_pi0"
  origin := .futureComparisonTheorem
  level := .pi0Only
  auditClass := .structuredRealization
  summary := "Pi0 shadow of realization: induced triangulated functor and scalar shadow on the homotopy-category side."
  dependsOn := ["thm:internal-realization-functor", "thm:realization-comparison"]

def obligation_realizationFunctors_infty : MotivicComparisonObligation where
  key := "realization-functors-infinity"
  texAnchor := "rem:infty-realization"
  leanAnchor := "motivicComparisonObligation_realizationFunctors_infty"
  origin := .futureComparisonTheorem
  level := .inftyOnly
  auditClass := .structuredRealization
  summary := "Infinity-level realization: exact symmetric monoidal realization functor preserving coherent stable structure."
  dependsOn := ["thm:internal-realization-functor", "rem:infty-realization"]

def obligation_structuredRealizationConsequence : MotivicComparisonObligation where
  key := "structured-realization-consequence"
  texAnchor := "cor:internal-period-faithfulness"
  leanAnchor := "motivicComparisonObligation_structuredRealizationConsequence"
  origin := .futureComparisonTheorem
  level := .bridgeFromInfinityToPi0
  auditClass := .structuredRealization
  summary := "Structured realization consequence: comparison-data faithfulness and internal period-faithfulness consequences extracted from the realization package."
  dependsOn := ["cor:internal-period-faithfulness", "thm:internal-evaluation-faithfulness"]

def obligation_scalarShadowExtraction : MotivicComparisonObligation where
  key := "scalar-shadow-extraction"
  texAnchor := "cor:classical-period-conjecture"
  leanAnchor := "motivicComparisonObligation_scalarShadowExtraction"
  origin := .futureComparisonTheorem
  level := .bridgeFromInfinityToPi0
  auditClass := .scalarShadowExtraction
  summary := "Scalar-shadow extraction: classical period consequence obtained from the structured realization bridge."
  dependsOn := ["cor:classical-period-conjecture", "cor:period-conjecture-via-realization"]

def obligation_finalPeriodFaithfulnessConsequence : MotivicComparisonObligation where
  key := "final-period-faithfulness-consequence"
  texAnchor := "cor:classical-period-faithfulness-assembly"
  leanAnchor := "motivicComparisonObligation_finalPeriodFaithfulnessConsequence"
  origin := .futureComparisonTheorem
  level := .bridgeFromInfinityToPi0
  auditClass := .finalAssembly
  summary := "Final period-faithfulness consequence assembled only after scalar-shadow extraction has been registered."
  dependsOn := ["cor:classical-period-faithfulness-assembly", "cor:period-faithfulness"]

def targetRecognitionFeed_pi0Category : TargetRecognitionFeed where
  obligation := obligation_targetCategoryRecognition_pi0.id
  feeds := .pi0ComparisonOnly
  reason := "Pi0 target-category recognition feeds only the triangulated / homotopy-category comparison shadow."

def targetRecognitionFeed_inftyCategory : TargetRecognitionFeed where
  obligation := obligation_targetCategoryRecognition_infty.id
  feeds := .infinityComparisonOnly
  reason := "Infinity target-category recognition feeds only the stable infinity comparison surface."

def targetRecognitionFeed_inftyUniversalProperty : TargetRecognitionFeed where
  obligation := obligation_targetUniversalPropertyRecognition.id
  feeds := .infinityComparisonOnly
  reason := "Target universal-property recognition is used only in the infinity comparison factorization lane."

def targetRecognitionFeed_inftyRealizationStructure : TargetRecognitionFeed where
  obligation := obligation_targetRealizationStructureRecognition.id
  feeds := .bridgeFromInfinityToPi0
  reason := "Target realization-structure recognition feeds the structured realization bridge from the infinity package down toward classical consequences."

def targetRecognitionFeedMap : List TargetRecognitionFeed :=
  [ targetRecognitionFeed_pi0Category
  , targetRecognitionFeed_inftyCategory
  , targetRecognitionFeed_inftyUniversalProperty
  , targetRecognitionFeed_inftyRealizationStructure
  ]

def comparisonFactorizationFeed_pi0 : ComparisonFactorizationFeed where
  obligation := obligation_frontierUniversalProperty_pi0.id
  feeds := .pi0FactorizationOnly
  reason := "Pi0 frontier factorization feeds only the triangulated-shadow factorization lane."

def comparisonFactorizationFeed_infty : ComparisonFactorizationFeed where
  obligation := obligation_frontierUniversalProperty_infty.id
  feeds := .infinityFactorizationOnly
  reason := "Infinity frontier factorization feeds only the stable coherent factorization lane."

def comparisonFactorizationFeed_shadowExtraction : ComparisonFactorizationFeed where
  obligation := obligation_factorizationShadowExtraction.id
  feeds := .bridgeFromInfinityToPi0
  reason := "The explicit factorization-shadow bridge is the only registered route from infinity factorization to the pi0 comparison shadow."

def comparisonFactorizationFeedMap : List ComparisonFactorizationFeed :=
  [ comparisonFactorizationFeed_pi0
  , comparisonFactorizationFeed_infty
  , comparisonFactorizationFeed_shadowExtraction
  ]

/-- Registry used by the classical-scaffold lane. -/
def motivicComparisonObligationMap : List MotivicComparisonObligation :=
  [ obligation_frontierUniversalProperty_pi0
  , obligation_frontierUniversalProperty_infty
  , obligation_factorizationShadowExtraction
  , obligation_symmetricMonoidal_pi0
  , obligation_symmetricMonoidal_infty
  , obligation_triangulatedStable_pi0
  , obligation_triangulatedStable_infty
  , obligation_a1Invariance_pi0
  , obligation_a1Invariance_infty
  , obligation_nisnevichDescent_pi0
  , obligation_nisnevichDescent_infty
  , obligation_localization_pi0
  , obligation_localization_infty
  , obligation_tateStabilization_pi0
  , obligation_tateStabilization_infty
  , obligation_targetCategoryRecognition_pi0
  , obligation_targetCategoryRecognition_infty
  , obligation_targetUniversalPropertyRecognition
  , obligation_targetRealizationStructureRecognition
  , obligation_realizationFunctors_pi0
  , obligation_realizationFunctors_infty
  , obligation_structuredRealizationConsequence
  , obligation_scalarShadowExtraction
  , obligation_finalPeriodFaithfulnessConsequence
  ]

def obligationsWithOrigin (origin : MotivicObligationOrigin) : List MotivicComparisonObligation :=
  motivicComparisonObligationMap.filter fun obligation => obligation.origin = origin

def obligationsWithLevel (level : MotivicObligationLevel) : List MotivicComparisonObligation :=
  motivicComparisonObligationMap.filter fun obligation => obligation.level = level

def obligationsWithAuditClass
    (auditClass : MotivicObligationAuditClass) : List MotivicComparisonObligation :=
  motivicComparisonObligationMap.filter fun obligation => obligation.auditClass = auditClass

def targetRecognitionFeedsWithLevel
    (feeds : TargetRecognitionFeedLevel) : List TargetRecognitionFeed :=
  targetRecognitionFeedMap.filter fun entry => entry.feeds = feeds

def comparisonFactorizationFeedsWithLevel
    (feeds : ComparisonFactorizationFeedLevel) : List ComparisonFactorizationFeed :=
  comparisonFactorizationFeedMap.filter fun entry => entry.feeds = feeds

theorem mem_obligationsWithOrigin_iff
    (obligation : MotivicComparisonObligation) (origin : MotivicObligationOrigin) :
    obligation ∈ obligationsWithOrigin origin ↔
      obligation ∈ motivicComparisonObligationMap ∧ obligation.origin = origin := by
  simp [obligationsWithOrigin]

theorem mem_obligationsWithLevel_iff
    (obligation : MotivicComparisonObligation) (level : MotivicObligationLevel) :
    obligation ∈ obligationsWithLevel level ↔
      obligation ∈ motivicComparisonObligationMap ∧ obligation.level = level := by
  simp [obligationsWithLevel]

theorem mem_obligationsWithAuditClass_iff
    (obligation : MotivicComparisonObligation) (auditClass : MotivicObligationAuditClass) :
    obligation ∈ obligationsWithAuditClass auditClass ↔
      obligation ∈ motivicComparisonObligationMap ∧ obligation.auditClass = auditClass := by
  simp [obligationsWithAuditClass]

theorem mem_targetRecognitionFeedsWithLevel_iff
    (entry : TargetRecognitionFeed) (feeds : TargetRecognitionFeedLevel) :
    entry ∈ targetRecognitionFeedsWithLevel feeds ↔
      entry ∈ targetRecognitionFeedMap ∧ entry.feeds = feeds := by
  simp [targetRecognitionFeedsWithLevel]

theorem mem_comparisonFactorizationFeedsWithLevel_iff
    (entry : ComparisonFactorizationFeed) (feeds : ComparisonFactorizationFeedLevel) :
    entry ∈ comparisonFactorizationFeedsWithLevel feeds ↔
      entry ∈ comparisonFactorizationFeedMap ∧ entry.feeds = feeds := by
  simp [comparisonFactorizationFeedsWithLevel]

theorem targetRecognitionFeedMap_exact :
    ∀ obligation : MotivicObligationId,
      ∀ feeds : TargetRecognitionFeedLevel,
        (∃ entry ∈ targetRecognitionFeedMap,
          entry.obligation = obligation ∧ entry.feeds = feeds) ↔
          (obligation = obligation_targetCategoryRecognition_pi0.id ∧
            feeds = TargetRecognitionFeedLevel.pi0ComparisonOnly) ∨
          (obligation = obligation_targetCategoryRecognition_infty.id ∧
            feeds = TargetRecognitionFeedLevel.infinityComparisonOnly) ∨
          (obligation = obligation_targetUniversalPropertyRecognition.id ∧
            feeds = TargetRecognitionFeedLevel.infinityComparisonOnly) ∨
          (obligation = obligation_targetRealizationStructureRecognition.id ∧
            feeds = TargetRecognitionFeedLevel.bridgeFromInfinityToPi0) := by
  intro obligation feeds
  simp [targetRecognitionFeedMap, targetRecognitionFeed_pi0Category,
    targetRecognitionFeed_inftyCategory, targetRecognitionFeed_inftyUniversalProperty,
    targetRecognitionFeed_inftyRealizationStructure, eq_comm]

theorem comparisonFactorizationFeedMap_exact :
    ∀ obligation : MotivicObligationId,
      ∀ feeds : ComparisonFactorizationFeedLevel,
        (∃ entry ∈ comparisonFactorizationFeedMap,
          entry.obligation = obligation ∧ entry.feeds = feeds) ↔
          (obligation = obligation_frontierUniversalProperty_pi0.id ∧
            feeds = ComparisonFactorizationFeedLevel.pi0FactorizationOnly) ∨
          (obligation = obligation_frontierUniversalProperty_infty.id ∧
            feeds = ComparisonFactorizationFeedLevel.infinityFactorizationOnly) ∨
          (obligation = obligation_factorizationShadowExtraction.id ∧
            feeds = ComparisonFactorizationFeedLevel.bridgeFromInfinityToPi0) := by
  intro obligation feeds
  simp [comparisonFactorizationFeedMap, comparisonFactorizationFeed_pi0,
    comparisonFactorizationFeed_infty, comparisonFactorizationFeed_shadowExtraction,
    eq_comm]

theorem requested_obligation_count :
    ∀ obligationId : MotivicObligationId,
      obligationId ∈ motivicComparisonObligationMap.map MotivicComparisonObligation.id ↔
        obligationId = obligation_frontierUniversalProperty_pi0.id ∨
        obligationId = obligation_frontierUniversalProperty_infty.id ∨
        obligationId = obligation_factorizationShadowExtraction.id ∨
        obligationId = obligation_symmetricMonoidal_pi0.id ∨
        obligationId = obligation_symmetricMonoidal_infty.id ∨
        obligationId = obligation_triangulatedStable_pi0.id ∨
        obligationId = obligation_triangulatedStable_infty.id ∨
        obligationId = obligation_a1Invariance_pi0.id ∨
        obligationId = obligation_a1Invariance_infty.id ∨
        obligationId = obligation_nisnevichDescent_pi0.id ∨
        obligationId = obligation_nisnevichDescent_infty.id ∨
        obligationId = obligation_localization_pi0.id ∨
        obligationId = obligation_localization_infty.id ∨
        obligationId = obligation_tateStabilization_pi0.id ∨
        obligationId = obligation_tateStabilization_infty.id ∨
        obligationId = obligation_targetCategoryRecognition_pi0.id ∨
        obligationId = obligation_targetCategoryRecognition_infty.id ∨
        obligationId = obligation_targetUniversalPropertyRecognition.id ∨
        obligationId = obligation_targetRealizationStructureRecognition.id ∨
        obligationId = obligation_realizationFunctors_pi0.id ∨
        obligationId = obligation_realizationFunctors_infty.id ∨
        obligationId = obligation_structuredRealizationConsequence.id ∨
        obligationId = obligation_scalarShadowExtraction.id ∨
        obligationId = obligation_finalPeriodFaithfulnessConsequence.id := by
  intro obligationId
  simp [motivicComparisonObligationMap]

theorem target_universal_property_recognition_is_external :
    obligation_targetUniversalPropertyRecognition.origin = MotivicObligationOrigin.externalMotivicTheorem := by
  rfl

theorem target_universal_property_recognition_is_infty_only :
    obligation_targetUniversalPropertyRecognition.level = MotivicObligationLevel.inftyOnly := by
  rfl

theorem frontier_universal_property_pi0_is_factorization_audit :
    obligation_frontierUniversalProperty_pi0.auditClass =
      MotivicObligationAuditClass.comparisonFactorization := by
  rfl

theorem frontier_universal_property_infty_is_factorization_audit :
    obligation_frontierUniversalProperty_infty.auditClass =
      MotivicObligationAuditClass.comparisonFactorization := by
  rfl

theorem factorization_shadow_extraction_is_factorization_audit :
    obligation_factorizationShadowExtraction.auditClass =
      MotivicObligationAuditClass.comparisonFactorization := by
  rfl

theorem target_category_recognition_pi0_role :
    obligation_targetCategoryRecognition_pi0.auditClass =
      MotivicObligationAuditClass.targetRecognition := by
  rfl

theorem target_category_recognition_infty_role :
    obligation_targetCategoryRecognition_infty.auditClass =
      MotivicObligationAuditClass.targetRecognition := by
  rfl

theorem target_universal_property_recognition_role :
    obligation_targetUniversalPropertyRecognition.auditClass =
      MotivicObligationAuditClass.externalInputToInternalize := by
  rfl

theorem target_realization_structure_recognition_role :
    obligation_targetRealizationStructureRecognition.auditClass =
      MotivicObligationAuditClass.targetRecognition := by
  rfl

theorem symmetric_monoidal_pi0_surface_tag :
    obligation_symmetricMonoidal_pi0.level = MotivicObligationLevel.pi0Only := by
  rfl

theorem symmetric_monoidal_infty_surface_tag :
    obligation_symmetricMonoidal_infty.level = MotivicObligationLevel.inftyOnly := by
  rfl

theorem triangulated_pi0_surface_tag :
    obligation_triangulatedStable_pi0.level = MotivicObligationLevel.pi0Only := by
  rfl

theorem triangulated_infty_surface_tag :
    obligation_triangulatedStable_infty.level = MotivicObligationLevel.inftyOnly := by
  rfl

theorem a1_pi0_surface_tag :
    obligation_a1Invariance_pi0.level = MotivicObligationLevel.pi0Only := by
  rfl

theorem a1_infty_surface_tag :
    obligation_a1Invariance_infty.level = MotivicObligationLevel.inftyOnly := by
  rfl

theorem localization_pi0_surface_tag :
    obligation_localization_pi0.level = MotivicObligationLevel.pi0Only := by
  rfl

theorem localization_infty_surface_tag :
    obligation_localization_infty.level = MotivicObligationLevel.inftyOnly := by
  rfl

theorem nisnevich_pi0_surface_tag :
    obligation_nisnevichDescent_pi0.level = MotivicObligationLevel.pi0Only := by
  rfl

theorem nisnevich_infty_surface_tag :
    obligation_nisnevichDescent_infty.level = MotivicObligationLevel.inftyOnly := by
  rfl

theorem tate_pi0_surface_tag :
    obligation_tateStabilization_pi0.level = MotivicObligationLevel.pi0Only := by
  rfl

theorem tate_infty_surface_tag :
    obligation_tateStabilization_infty.level = MotivicObligationLevel.inftyOnly := by
  rfl

theorem realization_pi0_surface_tag :
    obligation_realizationFunctors_pi0.level = MotivicObligationLevel.pi0Only := by
  rfl

theorem realization_infty_surface_tag :
    obligation_realizationFunctors_infty.level = MotivicObligationLevel.inftyOnly := by
  rfl

theorem structured_realization_consequence_is_future_bridge :
    obligation_structuredRealizationConsequence.origin = MotivicObligationOrigin.futureComparisonTheorem := by
  rfl

theorem structured_realization_consequence_is_bridge_from_infty_to_pi0 :
    obligation_structuredRealizationConsequence.level = MotivicObligationLevel.bridgeFromInfinityToPi0 := by
  rfl

theorem scalar_shadow_extraction_is_future_bridge :
    obligation_scalarShadowExtraction.origin = MotivicObligationOrigin.futureComparisonTheorem := by
  rfl

theorem scalar_shadow_extraction_is_bridge_from_infty_to_pi0 :
    obligation_scalarShadowExtraction.level = MotivicObligationLevel.bridgeFromInfinityToPi0 := by
  rfl

theorem final_period_faithfulness_consequence_is_final_assembly :
    obligation_finalPeriodFaithfulnessConsequence.auditClass =
      MotivicObligationAuditClass.finalAssembly := by
  rfl

theorem no_inseparable_both_entries_registered :
    ∀ obligation : MotivicComparisonObligation,
      obligation ∈ obligationsWithLevel MotivicObligationLevel.both ↔ False := by
  intro obligation
  simp [obligationsWithLevel, motivicComparisonObligationMap,
    obligation_frontierUniversalProperty_pi0, obligation_frontierUniversalProperty_infty,
    obligation_factorizationShadowExtraction, obligation_symmetricMonoidal_pi0,
    obligation_symmetricMonoidal_infty, obligation_triangulatedStable_pi0,
    obligation_triangulatedStable_infty, obligation_a1Invariance_pi0,
    obligation_a1Invariance_infty, obligation_nisnevichDescent_pi0,
    obligation_nisnevichDescent_infty, obligation_localization_pi0,
    obligation_localization_infty, obligation_tateStabilization_pi0,
    obligation_tateStabilization_infty, obligation_targetCategoryRecognition_pi0,
    obligation_targetCategoryRecognition_infty, obligation_targetUniversalPropertyRecognition,
    obligation_targetRealizationStructureRecognition, obligation_realizationFunctors_pi0,
    obligation_realizationFunctors_infty, obligation_structuredRealizationConsequence,
    obligation_scalarShadowExtraction, obligation_finalPeriodFaithfulnessConsequence]

end LayerD
end TraceCalc