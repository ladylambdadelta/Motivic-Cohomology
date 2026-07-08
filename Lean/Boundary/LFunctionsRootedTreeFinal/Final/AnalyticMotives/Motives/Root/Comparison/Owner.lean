import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Summary.Owner

/-!
# Motive-root comparison facade

This file exposes the current motive-level analytic/algebraic generator
comparison surface through the `TraceAnalyticMotive` root namespace.
-/

universe u

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

variable {k : Type u} [Field k] [PerfectField k]

variable (composition : Boundary.CanonicalCompositionData (k := k))
variable [FiniteCorrespondence.CanonicalExternalProductFamily (k := k)]
variable [Abelian (LinearPST (Boundary.canonicalCategory composition))]
variable [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
variable [Abelian (canonicalA1NisLocalization composition)]
variable [HasDerivedCategory (canonicalA1NisLocalization composition)]
variable [(canonicalA1NisLocalizationFunctor composition).Additive]
variable [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
variable [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]

/-- The motive-root comparison source is the stable analytic motive category. -/
abbrev TraceAnalyticMotive.comparisonSource :=
  TraceAnalyticDMgmComparisonSource

/-- The motive-root comparison target is the concrete Boundary `DM_gm(Q)_Q`. -/
abbrev TraceAnalyticMotive.comparisonTarget :=
  TraceAnalyticDMgmComparisonTarget (composition := composition)

/-- The motive-root comparison source is the stable analytic Verdier quotient. -/
theorem TraceAnalyticMotive.comparisonSource_eq_stable :
    TraceAnalyticMotive.comparisonSource =
      TraceAnalyticStableMotiveCategory :=
  TraceAnalyticDMgmComparisonSource_eq_stable

/-- The motive-root comparison source is the stable homotopy comparison source. -/
theorem TraceAnalyticMotive.comparisonSource_eq_stableHomotopy :
    TraceAnalyticMotive.comparisonSource =
      TraceAnalyticStableHomotopyComparisonSource :=
  rfl

/-- The motive-root comparison source is triangulated. -/
def TraceAnalyticMotive.comparisonSource_triangulatedStructure :
    IsTriangulated TraceAnalyticMotive.comparisonSource :=
  TraceAnalyticDMgmComparisonSource.triangulatedStructure

/-- The motive-root comparison target is the Boundary `VoevodskyDMgmQ_Q`. -/
theorem TraceAnalyticMotive.comparisonTarget_eq_boundary :
    TraceAnalyticMotive.comparisonTarget (composition := composition) =
      Boundary.VoevodskyDMgmQ_Q (composition := composition) :=
  TraceAnalyticDMgmComparisonTarget_eq_boundary
    (composition := composition)

/-- The motive-root comparison target has the Boundary effective embedding. -/
def TraceAnalyticMotive.comparisonTarget_effectiveEmbedding :
    canonicalEffectiveMotives composition ⥤
      TraceAnalyticMotive.comparisonTarget (composition := composition) :=
  TraceAnalyticDMgmComparisonTarget.effectiveEmbedding
    (composition := composition)

/-- Effective geometric motives entering the motive-root comparison target. -/
abbrev TraceAnalyticMotive.comparisonTarget_effectiveGeometricMotives :=
  TraceAnalyticDMgmComparisonTarget.effectiveGeometricMotives
    (composition := composition)

/-- The motive-root comparison target's effective geometric motives are the
canonical Boundary geometric effective motives. -/
theorem TraceAnalyticMotive.comparisonTarget_effectiveGeometricMotives_eq_canonical :
    TraceAnalyticMotive.comparisonTarget_effectiveGeometricMotives
        (composition := composition) =
      canonicalGeometricEffectiveMotives composition :=
  TraceAnalyticDMgmComparisonTarget.effectiveGeometricMotives_eq_canonical
    (composition := composition)

/-- Effective tensor geometry entering the motive-root comparison target. -/
abbrev TraceAnalyticMotive.comparisonTarget_effectiveTensorGeometry
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition) :=
  TraceAnalyticDMgmComparisonTarget.effectiveTensorGeometry
    (composition := composition) hgraph

/-- The motive-root comparison target's effective tensor geometry is the
canonical Boundary effective-motive tensor geometry. -/
theorem TraceAnalyticMotive.comparisonTarget_effectiveTensorGeometry_eq_canonical
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition) :
    TraceAnalyticMotive.comparisonTarget_effectiveTensorGeometry
        (composition := composition) hgraph =
      canonicalEffectiveMotives_tensorGeometry
        (composition := composition) hgraph :=
  TraceAnalyticDMgmComparisonTarget.effectiveTensorGeometry_eq_canonical
    (composition := composition) hgraph

/-- The motive-root comparison target has the Boundary Tate-shift equivalence. -/
def TraceAnalyticMotive.comparisonTarget_tateShiftEquivalence :
    TraceAnalyticMotive.comparisonTarget (composition := composition) ≌
      TraceAnalyticMotive.comparisonTarget (composition := composition) :=
  TraceAnalyticDMgmComparisonTarget.tateShiftEquivalence
    (composition := composition)

/-- The motive-root comparison target's Tate-stabilization extension data. -/
abbrev TraceAnalyticMotive.comparisonTarget_TateStabilizationExtension
    (D : Type (u + 2)) [Category D] :=
  TraceAnalyticDMgmComparisonTarget.TateStabilizationExtension
    (composition := composition) D

/-- Lift extension data out of the motive-root comparison target. -/
def TraceAnalyticMotive.comparisonTarget_TateStabilizationExtension_lift
    {D : Type (u + 2)} [Category D]
    (extension :
      TraceAnalyticMotive.comparisonTarget_TateStabilizationExtension
        (composition := composition) D) :
    TraceAnalyticMotive.comparisonTarget (composition := composition) ⥤ D :=
  TraceAnalyticDMgmComparisonTarget.TateStabilizationExtension.lift
    (composition := composition) extension

/-- The motive-root comparison target carries the Boundary DMgm
Tate-stabilization universal-property package. -/
def TraceAnalyticMotive.comparisonTarget_tateStabilizationUniversalProperty :
    Boundary.VoevodskyDMgmTateStabilizationUniversalProperty
      (composition := composition) :=
  TraceAnalyticDMgmComparisonTarget.tateStabilizationUniversalProperty
    (composition := composition)

/-- The motive-root comparison target formally inverts the Boundary effective
Tate object. -/
theorem TraceAnalyticMotive.comparisonTarget_formallyInvertsTateObject :
    (Boundary.Motives.inverseTateShift
        (boundaryEffectiveTateObject (composition := composition))).obj
      ((TraceAnalyticMotive.comparisonTarget_effectiveEmbedding
          (composition := composition)).obj
        (boundaryEffectiveTateObject (composition := composition))) =
      ⟨boundaryEffectiveTateObject (composition := composition), -1⟩ :=
  TraceAnalyticDMgmComparisonTarget.formallyInvertsTateObject
    (composition := composition)

/-- The motive-root comparison functor obtained by descending a null-inverting
additive-homotopy functor to the concrete Boundary DMgm target. -/
def TraceAnalyticMotive.comparisonTarget_descendInvertingFunctor
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticMotive.comparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor) :
    TraceAnalyticMotive.comparisonSource ⥤
      TraceAnalyticMotive.comparisonTarget (composition := composition) :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
    (composition := composition)
    functor
    inverts

/-- The motive-root descended comparison functor factors the original functor
through the stable analytic quotient. -/
def TraceAnalyticMotive.comparisonTarget_descendInvertingFunctorFac
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticMotive.comparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor) :
    TraceAnalyticStableHomotopyComparisonSource.quotientFunctor ⋙
      TraceAnalyticMotive.comparisonTarget_descendInvertingFunctor
        (composition := composition)
        functor
        inverts ≅
      functor :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorFac
    (composition := composition)
    functor
    inverts

/-- Natural transformations between null-inverting additive-homotopy functors
descend to the motive-root Boundary-DMgm comparison target. -/
def TraceAnalyticMotive.comparisonTarget_descendInvertingFunctorNatTrans
    (first second :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticMotive.comparisonTarget (composition := composition))
    (firstInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        first)
    (secondInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        second)
    (transformation : first ⟶ second) :
    TraceAnalyticMotive.comparisonTarget_descendInvertingFunctor
      (composition := composition)
      first
      firstInverts ⟶
    TraceAnalyticMotive.comparisonTarget_descendInvertingFunctor
      (composition := composition)
      second
      secondInverts :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans
    (composition := composition)
    first
    second
    firstInverts
    secondInverts
    transformation

/-- The motive-root descended comparison functor sends quotient-represented
stable analytic objects to objects isomorphic to the original functor value. -/
def TraceAnalyticMotive.comparisonTarget_descendInvertingFunctorObjectIso
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticMotive.comparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (object : TraceAnalyticAdditiveHomotopyCategory) :
    (TraceAnalyticMotive.comparisonTarget_descendInvertingFunctor
      (composition := composition)
      functor
      inverts).obj
        (TraceAnalyticStableHomotopyComparisonSource.objectOf object) ≅
      functor.obj object :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
    (composition := composition)
    functor
    inverts
    object

/-- The motive-root descended comparison functor's morphism action on represented
quotient morphisms is compatible with the original functor. -/
theorem TraceAnalyticMotive.comparisonTarget_descendInvertingFunctor_mapOf_naturality
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticMotive.comparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    {source targetObject : TraceAnalyticAdditiveHomotopyCategory}
    (hom : source ⟶ targetObject) :
    (TraceAnalyticMotive.comparisonTarget_descendInvertingFunctor
      (composition := composition)
      functor
      inverts).map
        (TraceAnalyticStableHomotopyComparisonSource.mapOf hom) ≫
      (TraceAnalyticMotive.comparisonTarget_descendInvertingFunctorObjectIso
        (composition := composition)
        functor
        inverts
        targetObject).hom =
      (TraceAnalyticMotive.comparisonTarget_descendInvertingFunctorObjectIso
        (composition := composition)
        functor
        inverts
        source).hom ≫
        functor.map hom :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor_mapOf_naturality
    (composition := composition)
    functor
    inverts
    hom

/-- At quotient-represented analytic objects, a descended motive-root natural
transformation is the original transformation conjugated by the descent
factorization isomorphisms. -/
theorem TraceAnalyticMotive.comparisonTarget_descendInvertingFunctorNatTrans_app_objectOf
    (first second :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticMotive.comparisonTarget (composition := composition))
    (firstInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        first)
    (secondInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        second)
    (transformation : first ⟶ second)
    (object : TraceAnalyticAdditiveHomotopyCategory) :
    (TraceAnalyticMotive.comparisonTarget_descendInvertingFunctorNatTrans
      (composition := composition)
      first
      second
      firstInverts
      secondInverts
      transformation).app
        (TraceAnalyticStableHomotopyComparisonSource.objectOf object) =
      (TraceAnalyticMotive.comparisonTarget_descendInvertingFunctorObjectIso
        (composition := composition)
        first
        firstInverts
        object).hom ≫
      transformation.app object ≫
      (TraceAnalyticMotive.comparisonTarget_descendInvertingFunctorObjectIso
        (composition := composition)
        second
        secondInverts
        object).inv :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_app_objectOf
    (composition := composition)
    first
    second
    firstInverts
    secondInverts
    transformation
    object

/-- Descended motive-root natural transformations are natural on represented
stable analytic morphisms. -/
theorem TraceAnalyticMotive.comparisonTarget_descendInvertingFunctorNatTrans_mapOf_naturality
    (first second :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticMotive.comparisonTarget (composition := composition))
    (firstInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        first)
    (secondInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        second)
    (transformation : first ⟶ second)
    {source targetObject : TraceAnalyticAdditiveHomotopyCategory}
    (hom : source ⟶ targetObject) :
    (TraceAnalyticMotive.comparisonTarget_descendInvertingFunctorNatTrans
      (composition := composition)
      first
      second
      firstInverts
      secondInverts
      transformation).app
        (TraceAnalyticStableHomotopyComparisonSource.objectOf source) ≫
      (TraceAnalyticMotive.comparisonTarget_descendInvertingFunctor
        (composition := composition)
        second
        secondInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf hom) =
      (TraceAnalyticMotive.comparisonTarget_descendInvertingFunctor
        (composition := composition)
        first
        firstInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf hom) ≫
      (TraceAnalyticMotive.comparisonTarget_descendInvertingFunctorNatTrans
        (composition := composition)
        first
        second
        firstInverts
        secondInverts
        transformation).app
          (TraceAnalyticStableHomotopyComparisonSource.objectOf targetObject) :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_mapOf_naturality
    (composition := composition)
    first
    second
    firstInverts
    secondInverts
    transformation
    hom

/-- A motive-root Boundary-DMgm comparison functor that inverts stable null
morphisms sends every stable acyclic generator first map to an isomorphism. -/
theorem TraceAnalyticMotive.comparisonTarget_functor_inverts_generator_firstMap
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticMotive.comparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (generator : TraceAnalyticStableAcyclicGenerator) :
    IsIso (functor.map generator.firstMap) :=
  TraceAnalyticDMgmComparisonTarget.functor_inverts_generator_firstMap
    (composition := composition)
    functor
    inverts
    generator

/-- The motive-root descended comparison functor satisfies the projection formula
on every stable acyclic generator first map. -/
theorem TraceAnalyticMotive.comparisonTarget_descendInvertingFunctor_generator_firstMap_naturality
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticMotive.comparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (generator : TraceAnalyticStableAcyclicGenerator) :
    (TraceAnalyticMotive.comparisonTarget_descendInvertingFunctor
      (composition := composition)
      functor
      inverts).map
        (TraceAnalyticStableHomotopyComparisonSource.mapOf generator.firstMap) ≫
      (TraceAnalyticMotive.comparisonTarget_descendInvertingFunctorObjectIso
        (composition := composition)
        functor
        inverts
        generator.target).hom =
      (TraceAnalyticMotive.comparisonTarget_descendInvertingFunctorObjectIso
        (composition := composition)
        functor
        inverts
        generator.source).hom ≫
        functor.map generator.firstMap :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor_generator_firstMap_naturality
    (composition := composition)
    functor
    inverts
    generator

/-- Descended motive-root natural transformations are natural on every stable
acyclic generator first map. -/
theorem TraceAnalyticMotive.comparisonTarget_descendInvertingFunctorNatTrans_generator_firstMap_naturality
    (first second :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticMotive.comparisonTarget (composition := composition))
    (firstInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        first)
    (secondInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        second)
    (transformation : first ⟶ second)
    (generator : TraceAnalyticStableAcyclicGenerator) :
    (TraceAnalyticMotive.comparisonTarget_descendInvertingFunctorNatTrans
      (composition := composition)
      first
      second
      firstInverts
      secondInverts
      transformation).app
        (TraceAnalyticStableHomotopyComparisonSource.objectOf generator.source) ≫
      (TraceAnalyticMotive.comparisonTarget_descendInvertingFunctor
        (composition := composition)
        second
        secondInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf generator.firstMap) =
      (TraceAnalyticMotive.comparisonTarget_descendInvertingFunctor
        (composition := composition)
        first
        firstInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf generator.firstMap) ≫
      (TraceAnalyticMotive.comparisonTarget_descendInvertingFunctorNatTrans
        (composition := composition)
        first
        second
        firstInverts
        secondInverts
        transformation).app
          (TraceAnalyticStableHomotopyComparisonSource.objectOf generator.target) :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_generator_firstMap_naturality
    (composition := composition)
    first
    second
    firstInverts
    secondInverts
    transformation
    generator

/-- A motive-root Boundary-DMgm comparison functor that inverts stable null
morphisms sends every analytic localization-input stable map to an isomorphism. -/
theorem TraceAnalyticMotive.comparisonTarget_functor_inverts_localizationInput_stableMap
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticMotive.comparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (input : TraceLocalizationInput) :
    IsIso (functor.map input.stableMap) :=
  TraceAnalyticDMgmComparisonTarget.functor_inverts_localizationInput_stableMap
    (composition := composition)
    functor
    inverts
    input

/-- The motive-root descended comparison functor satisfies the projection formula
on every analytic localization-input stable map. -/
theorem TraceAnalyticMotive.comparisonTarget_descendInvertingFunctor_localizationInput_stableMap_naturality
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticMotive.comparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (input : TraceLocalizationInput) :
    (TraceAnalyticMotive.comparisonTarget_descendInvertingFunctor
      (composition := composition)
      functor
      inverts).map
        (TraceAnalyticStableHomotopyComparisonSource.mapOf input.stableMap) ≫
      (TraceAnalyticMotive.comparisonTarget_descendInvertingFunctorObjectIso
        (composition := composition)
        functor
        inverts
        input.stableTarget).hom =
      (TraceAnalyticMotive.comparisonTarget_descendInvertingFunctorObjectIso
        (composition := composition)
        functor
        inverts
        input.stableSource).hom ≫
        functor.map input.stableMap :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor_localizationInput_stableMap_naturality
    (composition := composition)
    functor
    inverts
    input

/-- The motive root exposes Stokes realization agreement. -/
theorem TraceAnalyticMotive.comparisonStokesGenerator_agreement
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.stokesMap source target =
      TraceAlgebraicRealizationGenerator.stokesMap source target :=
  TraceAnalyticMotiveComparison.stokesGenerator_agreement
    source
    target

/-- The motive root exposes residue realization agreement. -/
theorem TraceAnalyticMotive.comparisonResidueGenerator_agreement
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.residueMap source target =
      TraceAlgebraicRealizationGenerator.residueMap source target :=
  TraceAnalyticMotiveComparison.residueGenerator_agreement
    source
    target

/-- The motive root exposes channel realization agreement. -/
theorem TraceAnalyticMotive.comparisonChannelGenerator_agreement
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.channelMap source target =
      TraceAlgebraicRealizationGenerator.channelMap source target :=
  TraceAnalyticMotiveComparison.channelGenerator_agreement
    source
    target

/-- The motive root exposes refinement realization agreement. -/
theorem TraceAnalyticMotive.comparisonRefinementGenerator_agreement
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.refinementMap source target =
      TraceAlgebraicRealizationGenerator.refinementMap source target :=
  TraceAnalyticMotiveComparison.refinementGenerator_agreement
    source
    target

/-- The motive root exposes schedule realization agreement. -/
theorem TraceAnalyticMotive.comparisonScheduleGenerator_agreement
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.scheduleMap source target =
      TraceAlgebraicRealizationGenerator.scheduleMap source target :=
  TraceAnalyticMotiveComparison.scheduleGenerator_agreement
    source
    target

/-- The motive root exposes weight-drop realization agreement. -/
theorem TraceAnalyticMotive.comparisonWeightDropGenerator_agreement
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.weightDropMap source target =
      TraceAlgebraicRealizationGenerator.weightDropMap source target :=
  TraceAnalyticMotiveComparison.weightDropGenerator_agreement
    source
    target

/-- The motive root exposes Fubini realization agreement. -/
theorem TraceAnalyticMotive.comparisonFubiniGenerator_agreement
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.fubiniMap source target =
      TraceAlgebraicRealizationGenerator.fubiniMap source target :=
  TraceAnalyticMotiveComparison.fubiniGenerator_agreement
    source
    target

/-- The motive root exposes the common Stokes by-kind map. -/
theorem TraceAnalyticMotive.comparisonStokesGenerator_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.stokesMap source target =
      TraceRewriteGenerator.stokesRepresentableMap source target :=
  TraceAnalyticMotiveComparison.stokesGenerator_eq_byKind
    source
    target

/-- The motive root exposes the common residue by-kind map. -/
theorem TraceAnalyticMotive.comparisonResidueGenerator_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.residueMap source target =
      TraceRewriteGenerator.residueRepresentableMap source target :=
  TraceAnalyticMotiveComparison.residueGenerator_eq_byKind
    source
    target

/-- The motive root exposes the common channel by-kind map. -/
theorem TraceAnalyticMotive.comparisonChannelGenerator_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.channelMap source target =
      TraceRewriteGenerator.channelRepresentableMap source target :=
  TraceAnalyticMotiveComparison.channelGenerator_eq_byKind
    source
    target

/-- The motive root exposes the common refinement by-kind map. -/
theorem TraceAnalyticMotive.comparisonRefinementGenerator_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.refinementMap source target =
      TraceRewriteGenerator.refinementRepresentableMap source target :=
  TraceAnalyticMotiveComparison.refinementGenerator_eq_byKind
    source
    target

/-- The motive root exposes the common schedule by-kind map. -/
theorem TraceAnalyticMotive.comparisonScheduleGenerator_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.scheduleMap source target =
      TraceRewriteGenerator.scheduleRepresentableMap source target :=
  TraceAnalyticMotiveComparison.scheduleGenerator_eq_byKind
    source
    target

/-- The motive root exposes the common weight-drop by-kind map. -/
theorem TraceAnalyticMotive.comparisonWeightDropGenerator_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.weightDropMap source target =
      TraceRewriteGenerator.weightDropRepresentableMap source target :=
  TraceAnalyticMotiveComparison.weightDropGenerator_eq_byKind
    source
    target

/-- The motive root exposes the common Fubini by-kind map. -/
theorem TraceAnalyticMotive.comparisonFubiniGenerator_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.fubiniMap source target =
      TraceRewriteGenerator.fubiniRepresentableMap source target :=
  TraceAnalyticMotiveComparison.fubiniGenerator_eq_byKind
    source
    target

/-- The motive root exposes the Stokes trace-hom preimage. -/
theorem TraceAnalyticMotive.comparisonStokesGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.stokesMap source target) =
      (TraceRewriteGenerator.stokes source target).traceHom :=
  TraceAnalyticMotiveComparison.stokesGenerator_preimage
    source
    target

/-- The motive root exposes the residue trace-hom preimage. -/
theorem TraceAnalyticMotive.comparisonResidueGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.residueMap source target) =
      (TraceRewriteGenerator.residue source target).traceHom :=
  TraceAnalyticMotiveComparison.residueGenerator_preimage
    source
    target

/-- The motive root exposes the channel trace-hom preimage. -/
theorem TraceAnalyticMotive.comparisonChannelGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.channelMap source target) =
      (TraceRewriteGenerator.channel source target).traceHom :=
  TraceAnalyticMotiveComparison.channelGenerator_preimage
    source
    target

/-- The motive root exposes the refinement trace-hom preimage. -/
theorem TraceAnalyticMotive.comparisonRefinementGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.refinementMap source target) =
      (TraceRewriteGenerator.refinement source target).traceHom :=
  TraceAnalyticMotiveComparison.refinementGenerator_preimage
    source
    target

/-- The motive root exposes the schedule trace-hom preimage. -/
theorem TraceAnalyticMotive.comparisonScheduleGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.scheduleMap source target) =
      (TraceRewriteGenerator.schedule source target).traceHom :=
  TraceAnalyticMotiveComparison.scheduleGenerator_preimage
    source
    target

/-- The motive root exposes the weight-drop trace-hom preimage. -/
theorem TraceAnalyticMotive.comparisonWeightDropGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.weightDropMap source target) =
      (TraceRewriteGenerator.weightDrop source target).traceHom :=
  TraceAnalyticMotiveComparison.weightDropGenerator_preimage
    source
    target

/-- The motive root exposes the Fubini trace-hom preimage. -/
theorem TraceAnalyticMotive.comparisonFubiniGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.fubiniMap source target) =
      (TraceRewriteGenerator.fubini source target).traceHom :=
  TraceAnalyticMotiveComparison.fubiniGenerator_preimage
    source
    target

/-- The motive root exposes Stokes algebraic-vs-analytic preimage agreement. -/
theorem TraceAnalyticMotive.comparisonAlgebraicStokesPreimage_eq_analytic
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.stokesMap source target) =
      TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.stokesMap source target) :=
  TraceAnalyticMotiveComparison.algebraicStokesPreimage_eq_analytic
    source
    target

/-- The motive root exposes residue algebraic-vs-analytic preimage agreement. -/
theorem TraceAnalyticMotive.comparisonAlgebraicResiduePreimage_eq_analytic
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.residueMap source target) =
      TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.residueMap source target) :=
  TraceAnalyticMotiveComparison.algebraicResiduePreimage_eq_analytic
    source
    target

/-- The motive root exposes channel algebraic-vs-analytic preimage agreement. -/
theorem TraceAnalyticMotive.comparisonAlgebraicChannelPreimage_eq_analytic
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.channelMap source target) =
      TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.channelMap source target) :=
  TraceAnalyticMotiveComparison.algebraicChannelPreimage_eq_analytic
    source
    target

/-- The motive root exposes refinement algebraic-vs-analytic preimage agreement. -/
theorem TraceAnalyticMotive.comparisonAlgebraicRefinementPreimage_eq_analytic
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.refinementMap source target) =
      TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.refinementMap source target) :=
  TraceAnalyticMotiveComparison.algebraicRefinementPreimage_eq_analytic
    source
    target

/-- The motive root exposes schedule algebraic-vs-analytic preimage agreement. -/
theorem TraceAnalyticMotive.comparisonAlgebraicSchedulePreimage_eq_analytic
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.scheduleMap source target) =
      TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.scheduleMap source target) :=
  TraceAnalyticMotiveComparison.algebraicSchedulePreimage_eq_analytic
    source
    target

/-- The motive root exposes weight-drop algebraic-vs-analytic preimage agreement. -/
theorem TraceAnalyticMotive.comparisonAlgebraicWeightDropPreimage_eq_analytic
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.weightDropMap source target) =
      TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.weightDropMap source target) :=
  TraceAnalyticMotiveComparison.algebraicWeightDropPreimage_eq_analytic
    source
    target

/-- The motive root exposes Fubini algebraic-vs-analytic preimage agreement. -/
theorem TraceAnalyticMotive.comparisonAlgebraicFubiniPreimage_eq_analytic
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.fubiniMap source target) =
      TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.fubiniMap source target) :=
  TraceAnalyticMotiveComparison.algebraicFubiniPreimage_eq_analytic
    source
    target

/-- The motive root exposes the algebraic Stokes trace-hom preimage. -/
theorem TraceAnalyticMotive.comparisonAlgebraicStokesGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.stokesMap source target) =
      (TraceRewriteGenerator.stokes source target).traceHom :=
  TraceAnalyticMotiveComparison.algebraicStokesGenerator_preimage
    source
    target

/-- The motive root exposes the algebraic residue trace-hom preimage. -/
theorem TraceAnalyticMotive.comparisonAlgebraicResidueGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.residueMap source target) =
      (TraceRewriteGenerator.residue source target).traceHom :=
  TraceAnalyticMotiveComparison.algebraicResidueGenerator_preimage
    source
    target

/-- The motive root exposes the algebraic channel trace-hom preimage. -/
theorem TraceAnalyticMotive.comparisonAlgebraicChannelGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.channelMap source target) =
      (TraceRewriteGenerator.channel source target).traceHom :=
  TraceAnalyticMotiveComparison.algebraicChannelGenerator_preimage
    source
    target

/-- The motive root exposes the algebraic refinement trace-hom preimage. -/
theorem TraceAnalyticMotive.comparisonAlgebraicRefinementGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.refinementMap source target) =
      (TraceRewriteGenerator.refinement source target).traceHom :=
  TraceAnalyticMotiveComparison.algebraicRefinementGenerator_preimage
    source
    target

/-- The motive root exposes the algebraic schedule trace-hom preimage. -/
theorem TraceAnalyticMotive.comparisonAlgebraicScheduleGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.scheduleMap source target) =
      (TraceRewriteGenerator.schedule source target).traceHom :=
  TraceAnalyticMotiveComparison.algebraicScheduleGenerator_preimage
    source
    target

/-- The motive root exposes the algebraic weight-drop trace-hom preimage. -/
theorem TraceAnalyticMotive.comparisonAlgebraicWeightDropGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.weightDropMap source target) =
      (TraceRewriteGenerator.weightDrop source target).traceHom :=
  TraceAnalyticMotiveComparison.algebraicWeightDropGenerator_preimage
    source
    target

/-- The motive root exposes the algebraic Fubini trace-hom preimage. -/
theorem TraceAnalyticMotive.comparisonAlgebraicFubiniGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.fubiniMap source target) =
      (TraceRewriteGenerator.fubini source target).traceHom :=
  TraceAnalyticMotiveComparison.algebraicFubiniGenerator_preimage
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
