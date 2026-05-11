import TraceCalc.LayerD.Roadmap.ComparisonRoadmap

universe u v w

namespace TraceCalc
namespace LayerD

/-- A proof-carrying realization of one roadmap milestone: it records which upstream stage
names are available and how the milestone's required obligation ids are supported. -/
def SupportsRequiredObligations
    (milestone : ComparisonMilestone)
    (supports : MotivicObligationId → Prop) : Prop :=
  ∀ obligationId : MotivicObligationId,
    obligationId ∈ milestone.requiredObligations → supports obligationId

structure MilestoneRealization (milestone : ComparisonMilestone) where
  availableStages : List String
  prerequisitesSatisfied : MilestonePrerequisitesSatisfied availableStages milestone
  supportsObligationId : MotivicObligationId → Prop
  requiredObligationsCovered : SupportsRequiredObligations milestone supportsObligationId

namespace MilestoneRealization

def stageName {milestone : ComparisonMilestone} (_ : MilestoneRealization milestone) : String :=
  milestone.stageName

theorem stageName_eq
    {milestone : ComparisonMilestone} (R : MilestoneRealization milestone) :
    R.stageName = milestone.stageName := rfl

end MilestoneRealization

/-- Abstract shape of the downstream period-faithfulness argument:
scalar equality reflects structured equality, and structured equality is faithful for the
ambient morphism relation. -/
structure PeriodFaithfulnessContext where
  Morph : Type u
  StructuredRealization : Morph → Type v
  ScalarShadow : Morph → Type w
  EqMorph : Morph → Morph → Prop
  structuredFaithful :
    ∀ {f g : Morph}, StructuredRealization f = StructuredRealization g → EqMorph f g
  scalarReflectsStructured :
    ∀ {f g : Morph}, ScalarShadow f = ScalarShadow g →
      StructuredRealization f = StructuredRealization g

namespace PeriodFaithfulnessContext

theorem scalar_period_faithfulness
    (C : PeriodFaithfulnessContext.{u, v, w}) :
    ∀ f g : C.Morph, C.ScalarShadow f = C.ScalarShadow g → C.EqMorph f g := by
  intro f g hscalar
  exact C.structuredFaithful (C.scalarReflectsStructured hscalar)

def AssemblyConsequence (C : PeriodFaithfulnessContext.{u, v, w}) : Prop :=
  ∀ f g : C.Morph, C.ScalarShadow f = C.ScalarShadow g → C.EqMorph f g

theorem assemblyConsequence_holds (C : PeriodFaithfulnessContext.{u, v, w}) :
    C.AssemblyConsequence :=
  C.scalar_period_faithfulness

end PeriodFaithfulnessContext

/-- Wrapper definition exposing the existing Layer B -> Layer D seam as a proof-carrying
realization of `SourceConstructionReady`. -/
def sourceTracePackage_gives_sourceConstructionReady
    (S : SourceTracePackage)
    (W : SourceTracePackage.SourceConstructionWitness S) :
    MilestoneRealization SourceConstructionReady where
  availableStages := []
  prerequisitesSatisfied :=
    (sourceTracePackage_supports_sourceConstructionReady S W).1
  supportsObligationId := W.SupportsObligationId
  requiredObligationsCovered :=
    (sourceTracePackage_supports_sourceConstructionReady S W).2

/-
TEX ref: `our_paper_draft.tex`, Sections 8–9 (DM recognition), Proposition `prop:transport-api`.
Paper role: package discharging T_can ≃ DM_gm(Q) at π_0-level and ∞-level recognition.
Lean status: TARGET-ONLY. All four Prop fields are unproved obligations.
TODO(theorem thm:comparison-by-double-representability): requires DM_gm(Q) type and comparison functor.
-/
/-- External theorem package discharging the target-recognition milestone. -/
structure TargetMotivicRecognitionPackage where
  targetCategoryRecognitionPiZero : Prop
  targetCategoryRecognitionPiZero_holds : targetCategoryRecognitionPiZero
  targetCategoryRecognitionInfinity : Prop
  targetCategoryRecognitionInfinity_holds : targetCategoryRecognitionInfinity
  targetUniversalPropertyRecognition : Prop
  targetUniversalPropertyRecognition_holds : targetUniversalPropertyRecognition
  targetRealizationStructureRecognition : Prop
  targetRealizationStructureRecognition_holds : targetRealizationStructureRecognition
namespace TargetMotivicRecognitionPackage

def SupportsObligationId
    (P : TargetMotivicRecognitionPackage)
    (obligationId : MotivicObligationId) : Prop :=
  (obligationId = obligation_targetCategoryRecognition_pi0.id ∧
      P.targetCategoryRecognitionPiZero) ∨
    (obligationId = obligation_targetCategoryRecognition_infty.id ∧
      P.targetCategoryRecognitionInfinity) ∨
    (obligationId = obligation_targetUniversalPropertyRecognition.id ∧
      P.targetUniversalPropertyRecognition) ∨
    (obligationId = obligation_targetRealizationStructureRecognition.id ∧
      P.targetRealizationStructureRecognition)

def package_gives_targetRecognitionReady
    (P : TargetMotivicRecognitionPackage) :
    MilestoneRealization TargetRecognitionReady where
  availableStages := []
  prerequisitesSatisfied := by
    intro prerequisite hpre
    simp [TargetRecognitionReady] at hpre
  supportsObligationId := P.SupportsObligationId
  requiredObligationsCovered := by
    intro obligationId hid
    simp [TargetRecognitionReady] at hid
    rcases hid with h | h | h | h
    · subst h
      exact Or.inl ⟨rfl, P.targetCategoryRecognitionPiZero_holds⟩
    · subst h
      exact Or.inr <| Or.inl ⟨rfl, P.targetCategoryRecognitionInfinity_holds⟩
    · subst h
      exact Or.inr <| Or.inr <| Or.inl ⟨rfl, P.targetUniversalPropertyRecognition_holds⟩
    · subst h
      exact Or.inr <| Or.inr <| Or.inr ⟨rfl, P.targetRealizationStructureRecognition_holds⟩

theorem targetPackage_realizes_exactly_targetRecognition
    (P : TargetMotivicRecognitionPackage) :
    (P.package_gives_targetRecognitionReady).stageName = TargetRecognitionReady.stageName ∧
      (P.package_gives_targetRecognitionReady).availableStages = [] ∧
      ∀ obligationId : MotivicObligationId,
        (P.package_gives_targetRecognitionReady).supportsObligationId obligationId ↔
          P.SupportsObligationId obligationId := by
  refine ⟨rfl, rfl, ?_⟩
  intro obligationId
  rfl

end TargetMotivicRecognitionPackage

/-
TEX ref: `our_paper_draft.tex`, Theorem `thm:infty-comparison` (Sections 8–9),
         Theorem `thm:full-infty-conservativity` (Section 10).
Paper role: \u221e-categorical comparison T^∞_can ≃ DM^∞_gm(Q) via Robalo universal property;
            conservativity of R^∞ : T^∞ → Ch(Q)_∞.
Lean status: TARGET-ONLY. Package collects Prop obligation fields; none are proved.
TODO(theorem thm:infty-comparison): requires DM^∞_gm(Q) definition and Robalo universal property.
TODO(theorem thm:full-infty-conservativity): requires higher boundary rigidity for each witness family.
-/
/-- External theorem package discharging the comparison-factorization milestone. -/
structure InfinityComparisonPackage where
  frontierUniversalPropertyPiZero : Prop
  frontierUniversalPropertyPiZero_holds : frontierUniversalPropertyPiZero
  frontierUniversalPropertyInfinity : Prop
  frontierUniversalPropertyInfinity_holds : frontierUniversalPropertyInfinity
  factorizationShadowExtraction : Prop
  factorizationShadowExtraction_holds : factorizationShadowExtraction

namespace InfinityComparisonPackage

def SupportsObligationId
    (P : InfinityComparisonPackage)
    (obligationId : MotivicObligationId) : Prop :=
  (obligationId = obligation_frontierUniversalProperty_pi0.id ∧
      P.frontierUniversalPropertyPiZero) ∨
    (obligationId = obligation_frontierUniversalProperty_infty.id ∧
      P.frontierUniversalPropertyInfinity) ∨
    (obligationId = obligation_factorizationShadowExtraction.id ∧
      P.factorizationShadowExtraction)

def package_gives_comparisonFactorizationReady
    (P : InfinityComparisonPackage) :
    MilestoneRealization ComparisonFactorizationReady where
  availableStages :=
    [ PiZeroFactorizationReady.stageName
    , InfinityFactorizationReady.stageName
    , FactorizationShadowExtractionReady.stageName
    ]
  prerequisitesSatisfied := comparison_readiness_package_prerequisites_satisfied
  supportsObligationId := P.SupportsObligationId
  requiredObligationsCovered := by
    intro obligationId hid
    have hcomparison :
        ∃ obligation : MotivicComparisonObligation,
          (obligation ∈ motivicComparisonObligationMap ∧
              obligation.auditClass = MotivicObligationAuditClass.comparisonFactorization) ∧
            obligation.id = obligationId := by
      simpa [ComparisonFactorizationReady, List.mem_map, mem_obligationsWithAuditClass_iff] using hid
    rcases hcomparison with ⟨obligation, ⟨hmem, haudit⟩, hid_eq⟩
    simp [motivicComparisonObligationMap] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨hid_eq.symm, P.frontierUniversalPropertyPiZero_holds⟩
    · exact Or.inr <| Or.inl ⟨hid_eq.symm, P.frontierUniversalPropertyInfinity_holds⟩
    · exact Or.inr <| Or.inr ⟨hid_eq.symm, P.factorizationShadowExtraction_holds⟩
    · exfalso
      simp [obligation_symmetricMonoidal_pi0] at haudit
    · exfalso
      simp [obligation_symmetricMonoidal_infty] at haudit
    · exfalso
      simp [obligation_triangulatedStable_pi0] at haudit
    · exfalso
      simp [obligation_triangulatedStable_infty] at haudit
    · exfalso
      simp [obligation_a1Invariance_pi0] at haudit
    · exfalso
      simp [obligation_a1Invariance_infty] at haudit
    · exfalso
      simp [obligation_nisnevichDescent_pi0] at haudit
    · exfalso
      simp [obligation_nisnevichDescent_infty] at haudit
    · exfalso
      simp [obligation_localization_pi0] at haudit
    · exfalso
      simp [obligation_localization_infty] at haudit
    · exfalso
      simp [obligation_tateStabilization_pi0] at haudit
    · exfalso
      simp [obligation_tateStabilization_infty] at haudit
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

theorem comparisonPackage_realizes_exactly_comparisonFactorization
    (P : InfinityComparisonPackage) :
    (P.package_gives_comparisonFactorizationReady).stageName = ComparisonFactorizationReady.stageName ∧
      (P.package_gives_comparisonFactorizationReady).availableStages =
        [ PiZeroFactorizationReady.stageName
        , InfinityFactorizationReady.stageName
        , FactorizationShadowExtractionReady.stageName
        ] ∧
      ∀ obligationId : MotivicObligationId,
        (P.package_gives_comparisonFactorizationReady).supportsObligationId obligationId ↔
          P.SupportsObligationId obligationId := by
  refine ⟨rfl, rfl, ?_⟩
  intro obligationId
  rfl

end InfinityComparisonPackage

/-- External theorem package discharging the structured realization bridge milestone. -/
structure StructuredRealizationPackage where
  realizationFunctorsPiZero : Prop
  realizationFunctorsPiZero_holds : realizationFunctorsPiZero
  realizationFunctorsInfinity : Prop
  realizationFunctorsInfinity_holds : realizationFunctorsInfinity
  structuredRealizationConsequence : Prop
  structuredRealizationConsequence_holds : structuredRealizationConsequence

namespace StructuredRealizationPackage

def SupportsObligationId
    (P : StructuredRealizationPackage)
    (obligationId : MotivicObligationId) : Prop :=
  (obligationId = obligation_realizationFunctors_infty.id ∧ P.realizationFunctorsInfinity) ∨
    (obligationId = obligation_realizationFunctors_pi0.id ∧ P.realizationFunctorsPiZero) ∨
    (obligationId = obligation_structuredRealizationConsequence.id ∧
      P.structuredRealizationConsequence)

def package_gives_structuredRealizationBridgeReady
    (P : StructuredRealizationPackage) :
    MilestoneRealization StructuredRealizationBridgeReady where
  availableStages :=
    [ComparisonFactorizationReady.stageName, InfinityComparisonReady.stageName]
  prerequisitesSatisfied := structured_realization_stage_prerequisites_satisfied
  supportsObligationId := P.SupportsObligationId
  requiredObligationsCovered := by
    intro obligationId hid
    simp [StructuredRealizationBridgeReady] at hid
    rcases hid with h | h | h
    · subst h
      exact Or.inl ⟨rfl, P.realizationFunctorsInfinity_holds⟩
    · subst h
      exact Or.inr <| Or.inl ⟨rfl, P.realizationFunctorsPiZero_holds⟩
    · subst h
      exact Or.inr <| Or.inr ⟨rfl, P.structuredRealizationConsequence_holds⟩

theorem structuredPackage_realizes_exactly_structuredBridge
    (P : StructuredRealizationPackage) :
    (P.package_gives_structuredRealizationBridgeReady).stageName = StructuredRealizationBridgeReady.stageName ∧
      (P.package_gives_structuredRealizationBridgeReady).availableStages =
        [ComparisonFactorizationReady.stageName, InfinityComparisonReady.stageName] ∧
      ∀ obligationId : MotivicObligationId,
        (P.package_gives_structuredRealizationBridgeReady).supportsObligationId obligationId ↔
          P.SupportsObligationId obligationId := by
  refine ⟨rfl, rfl, ?_⟩
  intro obligationId
  rfl

end StructuredRealizationPackage

/-- External theorem package discharging the scalar-shadow extraction milestone. -/
structure ScalarShadowExtractionPackage where
  scalarShadowExtraction : Prop
  scalarShadowExtraction_holds : scalarShadowExtraction

namespace ScalarShadowExtractionPackage

def SupportsObligationId
    (P : ScalarShadowExtractionPackage)
    (obligationId : MotivicObligationId) : Prop :=
  obligationId = obligation_scalarShadowExtraction.id ∧ P.scalarShadowExtraction

def package_gives_scalarShadowConsequenceReady
    (P : ScalarShadowExtractionPackage) :
    MilestoneRealization ScalarShadowConsequenceReady where
  availableStages := [StructuredRealizationBridgeReady.stageName]
  prerequisitesSatisfied := by
    intro prerequisite hpre
    simpa [ScalarShadowConsequenceReady, StructuredRealizationBridgeReady] using hpre
  supportsObligationId := P.SupportsObligationId
  requiredObligationsCovered := by
    intro obligationId hid
    simp [ScalarShadowConsequenceReady] at hid
    subst obligationId
    exact ⟨rfl, P.scalarShadowExtraction_holds⟩

theorem scalarPackage_realizes_exactly_scalarShadow
    (P : ScalarShadowExtractionPackage) :
    (P.package_gives_scalarShadowConsequenceReady).stageName = ScalarShadowConsequenceReady.stageName ∧
      (P.package_gives_scalarShadowConsequenceReady).availableStages =
        [StructuredRealizationBridgeReady.stageName] ∧
      ∀ obligationId : MotivicObligationId,
        (P.package_gives_scalarShadowConsequenceReady).supportsObligationId obligationId ↔
          P.SupportsObligationId obligationId := by
  refine ⟨rfl, rfl, ?_⟩
  intro obligationId
  rfl

end ScalarShadowExtractionPackage

/-- Assembly data for the final abstract period-faithfulness argument.  The readiness fields
are proof-carrying milestone realizations, not bare milestone names. -/
structure PeriodFaithfulnessAssemblyData where
  sourceReady : MilestoneRealization SourceConstructionReady
  targetReady : MilestoneRealization TargetRecognitionReady
  comparisonReady : MilestoneRealization ComparisonFactorizationReady
  structuredBridgeReady : MilestoneRealization StructuredRealizationBridgeReady
  scalarShadowReady : MilestoneRealization ScalarShadowConsequenceReady
  context : PeriodFaithfulnessContext.{u, v, w}

namespace PeriodFaithfulnessAssemblyData

def SupportsObligationId
    (A : PeriodFaithfulnessAssemblyData.{u, v, w})
    (obligationId : MotivicObligationId) : Prop :=
  obligationId = obligation_finalPeriodFaithfulnessConsequence.id ∧ A.context.AssemblyConsequence

def gives_finalComparisonEquivalenceAssemblyReady
    (A : PeriodFaithfulnessAssemblyData.{u, v, w}) :
    MilestoneRealization FinalComparisonEquivalenceAssemblyReady where
  availableStages :=
    [ A.sourceReady.stageName
    , A.targetReady.stageName
    , A.comparisonReady.stageName
    , A.structuredBridgeReady.stageName
    , A.scalarShadowReady.stageName
    ]
  prerequisitesSatisfied := by
    simpa [MilestoneRealization.stageName] using
      final_assembly_depends_only_on_upstream_structured_and_scalar_layers
  supportsObligationId := A.SupportsObligationId
  requiredObligationsCovered := by
    intro obligationId hid
    simp [FinalComparisonEquivalenceAssemblyReady] at hid
    subst obligationId
    exact ⟨rfl, PeriodFaithfulnessContext.assemblyConsequence_holds A.context⟩

def gives_periodFaithfulnessReady
    (A : PeriodFaithfulnessAssemblyData.{u, v, w}) :
    MilestoneRealization PeriodFaithfulnessReady where
  availableStages :=
    [ A.scalarShadowReady.stageName
    , (A.gives_finalComparisonEquivalenceAssemblyReady).stageName
    ]
  prerequisitesSatisfied := by
    simpa [MilestoneRealization.stageName] using periodFaithfulnessReady_prerequisites_satisfied
  supportsObligationId := A.SupportsObligationId
  requiredObligationsCovered := by
    intro obligationId hid
    simp [PeriodFaithfulnessReady] at hid
    subst obligationId
    exact ⟨rfl, PeriodFaithfulnessContext.assemblyConsequence_holds A.context⟩

end PeriodFaithfulnessAssemblyData

/-- Final proof package exported by the isolated Layer D assembly lane.  It contains both
the roadmap-facing readiness witness and the actual abstract scalar-faithfulness theorem. -/
structure AbstractPeriodFaithfulnessTheorem where
  context : PeriodFaithfulnessContext.{u, v, w}
  assemblyData : PeriodFaithfulnessAssemblyData.{u, v, w}
  assemblyData_context : assemblyData.context = context
  periodFaithfulnessReady : MilestoneRealization PeriodFaithfulnessReady
  scalarFaithful :
    ∀ f g : context.Morph,
      context.ScalarShadow f = context.ScalarShadow g → context.EqMorph f g

/-- Aggregate input surface for future Layer B / motivic instantiations of the final abstract
period-faithfulness theorem package. -/
structure PeriodFaithfulnessInputPackages where
  sourcePkg : SourceTracePackage
  sourceWit : SourceTracePackage.SourceConstructionWitness sourcePkg
  targetPkg : TargetMotivicRecognitionPackage
  comparisonPkg : InfinityComparisonPackage
  structuredPkg : StructuredRealizationPackage
  scalarPkg : ScalarShadowExtractionPackage
  context : PeriodFaithfulnessContext.{u, v, w}

namespace PeriodFaithfulnessInputPackages

end PeriodFaithfulnessInputPackages

end LayerD
end TraceCalc