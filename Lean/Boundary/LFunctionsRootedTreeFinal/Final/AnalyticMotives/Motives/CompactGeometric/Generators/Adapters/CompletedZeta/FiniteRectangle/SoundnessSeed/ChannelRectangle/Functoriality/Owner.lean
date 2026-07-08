import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ChannelRectangle.Core.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Functors.Presheaf.Embedding.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Functors.Yoneda.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Representable.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pullback.Representable.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pushforward.Representable.Owner

/-!
# Functoriality for the scheduled-channel compact generator

This file owns the representable, Yoneda, pullback, pushforward, and
pullback-pushforward interaction facts for the scheduled-channel compact
generator morphism.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Forgetting the scheduled-channel compact morphism gives the pipeline trace hom. -/
theorem completedZetaZeroPoleChannelRectangleGeneratorHom_forgetfulFunctor_map
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    TraceAnalyticGeometricGenerator.forgetfulFunctor.map
        (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u) =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_hom f F h u :=
  rfl

/-- The scheduled-channel compact morphism induces the pipeline representable map. -/
theorem completedZetaZeroPoleChannelRectangleGeneratorHom_representableMap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).representableMap =
      TraceCorQPresheaf.representableMap
        (completedZetaZeroPoleChannelScheduledRectanglePipeline_hom f F h u) :=
  rfl

/-- The scheduled-channel presheaf preimage recovers the compact morphism. -/
theorem completedZetaZeroPoleChannelRectangleGeneratorHom_presheafPreimage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    TraceAnalyticGeometricGenerator.presheafPreimage
        (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).representableMap =
      completedZetaZeroPoleChannelRectangleGeneratorHom f F h u :=
  TraceAnalyticGeometricGenerator.presheafPreimage_representableMap
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u)

/-- The chosen scheduled-channel presheaf lift maps back to the representable map. -/
theorem completedZetaZeroPoleChannelRectangleGeneratorHom_liftRepresentableMap_spec
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (TraceAnalyticGeometricGenerator.liftRepresentableMap
        (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).representableMap).representableMap =
      (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).representableMap :=
  TraceAnalyticGeometricGenerator.liftRepresentableMap_spec
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).representableMap

/-- Every scheduled-channel ambient presheaf morphism has a compact-generator lift. -/
theorem completedZetaZeroPoleChannelRectangleGeneratorHom_exists_representableMap_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (morphism :
      (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u).presheaf ⟶
        completedZetaZeroPoleChannelRectangleTargetGenerator.presheaf) :
    ∃ traceMorphism :
      (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u) ⟶
        completedZetaZeroPoleChannelRectangleTargetGenerator,
      traceMorphism.representableMap =
        morphism :=
  TraceAnalyticGeometricGenerator.exists_representableMap_eq morphism

/-- Equality of scheduled-channel representable maps reflects equality of compact morphisms. -/
theorem completedZetaZeroPoleChannelRectangleGeneratorHom_eq_of_representableMap_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    {left right :
      (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u) ⟶
        completedZetaZeroPoleChannelRectangleTargetGenerator}
    (map_eq : left.representableMap = right.representableMap) :
    left = right :=
  TraceAnalyticGeometricGenerator.eq_of_representableMap_eq map_eq

/-- The scheduled-channel compact morphism induces the lifted pipeline representable map. -/
theorem completedZetaZeroPoleChannelRectangleGeneratorHom_representableObjectMap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).representableObjectMap =
      (TraceCorQRepresentablePresheaf.yoneda).map
        (completedZetaZeroPoleChannelScheduledRectanglePipeline_hom f F h u) :=
  rfl

/-- The scheduled-channel compact Yoneda equivalence sends the morphism to its lifted map. -/
theorem completedZetaZeroPoleChannelRectangleGeneratorHom_yonedaHomEquiv
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    TraceAnalyticGeometricGenerator.yonedaHomEquiv
        (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u)
        completedZetaZeroPoleChannelRectangleTargetGenerator
        (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u) =
      (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).representableObjectMap :=
  TraceAnalyticGeometricGenerator.yonedaHomEquiv_apply
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u)

/-- The scheduled-channel compact Yoneda preimage recovers the compact morphism. -/
theorem completedZetaZeroPoleChannelRectangleGeneratorHom_yonedaPreimage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    TraceAnalyticGeometricGenerator.yonedaPreimage
        (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).representableObjectMap =
      completedZetaZeroPoleChannelRectangleGeneratorHom f F h u :=
  TraceAnalyticGeometricGenerator.yonedaPreimage_representableObjectMap
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u)

/-- Every lifted scheduled-channel representable morphism is induced by its Yoneda preimage. -/
theorem completedZetaZeroPoleChannelRectangleGeneratorHom_representableObjectMap_yonedaPreimage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (morphism :
      (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u).representableObject ⟶
        completedZetaZeroPoleChannelRectangleTargetGenerator.representableObject) :
    (TraceAnalyticGeometricGenerator.yonedaPreimage morphism).representableObjectMap =
      morphism :=
  TraceAnalyticGeometricGenerator.representableObjectMap_yonedaPreimage
    morphism

/-- The inverse scheduled-channel Yoneda equivalence is compact Yoneda preimage. -/
theorem completedZetaZeroPoleChannelRectangleGeneratorHom_yonedaHomEquiv_symm_apply
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (morphism :
      (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u).representableObject ⟶
        completedZetaZeroPoleChannelRectangleTargetGenerator.representableObject) :
    (TraceAnalyticGeometricGenerator.yonedaHomEquiv
        (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u)
        completedZetaZeroPoleChannelRectangleTargetGenerator).symm morphism =
      TraceAnalyticGeometricGenerator.yonedaPreimage morphism :=
  TraceAnalyticGeometricGenerator.yonedaHomEquiv_symm_apply
    morphism

/-- Pullback along the scheduled-channel compact morphism is pullback along the pipeline hom. -/
theorem completedZetaZeroPoleChannelRectangleGeneratorHom_pullback
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (presheaf : TraceCorQPresheaf) :
    TraceAnalyticGeometricGenerator.pullback
        presheaf
        (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u) =
      presheaf.pullback
        (completedZetaZeroPoleChannelScheduledRectanglePipeline_hom f F h u) :=
  rfl

/-- Pullback of a representable along the scheduled-channel compact morphism is precomposition. -/
theorem completedZetaZeroPoleChannelRectangleGeneratorHom_representablePrecomposition
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (target : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullback.compactGeneratorComponent
        target.presheaf
        (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u) =
      TraceSixFunctorPullback.representablePrecompositionOperator
        target
        (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u) :=
  TraceSixFunctorPullback.compactGeneratorComponent_representable
    target
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u)

/-- Pushforward along the scheduled-channel compact morphism is postcomposition at any probe. -/
theorem completedZetaZeroPoleChannelRectangleGeneratorHom_representablePostcomposition
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPushforward.compactGeneratorComponent
        probe
        (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u) =
      TraceSixFunctorPushforward.representablePostcompositionOperator
        probe
        (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u) :=
  TraceSixFunctorPushforward.compactGeneratorComponent_representable
    probe
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u)

/-- Pullback-precomposition commutes with scheduled-channel pushforward-postcomposition. -/
theorem completedZetaZeroPoleChannelRectangleGeneratorHom_pullbackPushforward_naturality
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullback.representablePrecompositionOperator
        (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u)
        probe ≫
        TraceSixFunctorPushforward.representablePostcompositionOperator
          probeSource
          (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u) =
      TraceSixFunctorPushforward.representablePostcompositionOperator
          probeTarget
          (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u) ≫
        TraceSixFunctorPullback.representablePrecompositionOperator
          completedZetaZeroPoleChannelRectangleTargetGenerator
          probe :=
  TraceSixFunctorPullbackPushforward.representableOperator_naturality
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u)
    probe

end AnalyticMotives
end LFunctions
end Boundary
