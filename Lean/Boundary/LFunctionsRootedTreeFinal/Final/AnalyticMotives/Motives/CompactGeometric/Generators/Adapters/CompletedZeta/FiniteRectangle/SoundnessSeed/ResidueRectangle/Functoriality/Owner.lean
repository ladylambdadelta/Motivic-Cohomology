import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ResidueRectangle.Core.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Functors.Presheaf.Embedding.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Functors.Yoneda.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Representable.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pullback.Representable.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pushforward.Representable.Owner

/-!
# Functoriality of the zero-pole residue rectangle compact morphism

This file owns the representable, Yoneda, pullback, pushforward, and
pullback-pushforward interaction facts for the completed-zeta residue rectangle
compact-generator morphism.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Forgetting the residue rectangle compact morphism gives the pipeline trace hom. -/
theorem completedZetaZeroPoleResidueRectangleGeneratorHom_forgetfulFunctor_map
    (R : ℝ) :
    TraceAnalyticGeometricGenerator.forgetfulFunctor.map
        (completedZetaZeroPoleResidueRectangleGeneratorHom R) =
      completedZetaZeroPoleResidueRectanglePipeline_hom R :=
  rfl

/-- The residue rectangle compact morphism induces the pipeline representable map. -/
theorem completedZetaZeroPoleResidueRectangleGeneratorHom_representableMap
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).representableMap =
      TraceCorQPresheaf.representableMap
        (completedZetaZeroPoleResidueRectanglePipeline_hom R) :=
  rfl

/-- The residue rectangle presheaf preimage recovers the compact morphism. -/
theorem completedZetaZeroPoleResidueRectangleGeneratorHom_presheafPreimage
    (R : ℝ) :
    TraceAnalyticGeometricGenerator.presheafPreimage
        (completedZetaZeroPoleResidueRectangleGeneratorHom R).representableMap =
      completedZetaZeroPoleResidueRectangleGeneratorHom R :=
  TraceAnalyticGeometricGenerator.presheafPreimage_representableMap
    (completedZetaZeroPoleResidueRectangleGeneratorHom R)

/-- The chosen residue rectangle presheaf lift maps back to the representable map. -/
theorem completedZetaZeroPoleResidueRectangleGeneratorHom_liftRepresentableMap_spec
    (R : ℝ) :
    (TraceAnalyticGeometricGenerator.liftRepresentableMap
        (completedZetaZeroPoleResidueRectangleGeneratorHom R).representableMap).representableMap =
      (completedZetaZeroPoleResidueRectangleGeneratorHom R).representableMap :=
  TraceAnalyticGeometricGenerator.liftRepresentableMap_spec
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).representableMap

/-- Every residue rectangle ambient presheaf morphism has a compact-generator lift. -/
theorem completedZetaZeroPoleResidueRectangleGeneratorHom_exists_representableMap_eq
    (R : ℝ)
    (morphism :
      (completedZetaZeroPoleResidueRectangleSourceGenerator R).presheaf ⟶
        completedZetaZeroPoleResidueRectangleTargetGenerator.presheaf) :
    ∃ traceMorphism :
      (completedZetaZeroPoleResidueRectangleSourceGenerator R) ⟶
        completedZetaZeroPoleResidueRectangleTargetGenerator,
      traceMorphism.representableMap =
        morphism :=
  TraceAnalyticGeometricGenerator.exists_representableMap_eq morphism

/-- Equality of residue rectangle representable maps reflects equality of compact morphisms. -/
theorem completedZetaZeroPoleResidueRectangleGeneratorHom_eq_of_representableMap_eq
    (R : ℝ)
    {left right :
      (completedZetaZeroPoleResidueRectangleSourceGenerator R) ⟶
        completedZetaZeroPoleResidueRectangleTargetGenerator}
    (map_eq : left.representableMap = right.representableMap) :
    left = right :=
  TraceAnalyticGeometricGenerator.eq_of_representableMap_eq map_eq

/-- The residue rectangle compact morphism induces the lifted pipeline representable map. -/
theorem completedZetaZeroPoleResidueRectangleGeneratorHom_representableObjectMap
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).representableObjectMap =
      (TraceCorQRepresentablePresheaf.yoneda).map
        (completedZetaZeroPoleResidueRectanglePipeline_hom R) :=
  rfl

/-- The residue rectangle compact Yoneda equivalence sends the morphism to its lifted map. -/
theorem completedZetaZeroPoleResidueRectangleGeneratorHom_yonedaHomEquiv
    (R : ℝ) :
    TraceAnalyticGeometricGenerator.yonedaHomEquiv
        (completedZetaZeroPoleResidueRectangleSourceGenerator R)
        completedZetaZeroPoleResidueRectangleTargetGenerator
        (completedZetaZeroPoleResidueRectangleGeneratorHom R) =
      (completedZetaZeroPoleResidueRectangleGeneratorHom R).representableObjectMap :=
  TraceAnalyticGeometricGenerator.yonedaHomEquiv_apply
    (completedZetaZeroPoleResidueRectangleGeneratorHom R)

/-- The residue rectangle compact Yoneda preimage recovers the compact morphism. -/
theorem completedZetaZeroPoleResidueRectangleGeneratorHom_yonedaPreimage
    (R : ℝ) :
    TraceAnalyticGeometricGenerator.yonedaPreimage
        (completedZetaZeroPoleResidueRectangleGeneratorHom R).representableObjectMap =
      completedZetaZeroPoleResidueRectangleGeneratorHom R :=
  TraceAnalyticGeometricGenerator.yonedaPreimage_representableObjectMap
    (completedZetaZeroPoleResidueRectangleGeneratorHom R)

/-- Every lifted residue rectangle representable morphism is induced by its Yoneda preimage. -/
theorem completedZetaZeroPoleResidueRectangleGeneratorHom_representableObjectMap_yonedaPreimage
    (R : ℝ)
    (morphism :
      (completedZetaZeroPoleResidueRectangleSourceGenerator R).representableObject ⟶
        completedZetaZeroPoleResidueRectangleTargetGenerator.representableObject) :
    (TraceAnalyticGeometricGenerator.yonedaPreimage morphism).representableObjectMap =
      morphism :=
  TraceAnalyticGeometricGenerator.representableObjectMap_yonedaPreimage
    morphism

/-- The inverse residue rectangle Yoneda equivalence is compact Yoneda preimage. -/
theorem completedZetaZeroPoleResidueRectangleGeneratorHom_yonedaHomEquiv_symm_apply
    (R : ℝ)
    (morphism :
      (completedZetaZeroPoleResidueRectangleSourceGenerator R).representableObject ⟶
        completedZetaZeroPoleResidueRectangleTargetGenerator.representableObject) :
    (TraceAnalyticGeometricGenerator.yonedaHomEquiv
        (completedZetaZeroPoleResidueRectangleSourceGenerator R)
        completedZetaZeroPoleResidueRectangleTargetGenerator).symm morphism =
      TraceAnalyticGeometricGenerator.yonedaPreimage morphism :=
  TraceAnalyticGeometricGenerator.yonedaHomEquiv_symm_apply
    morphism

/-- Pullback along the residue rectangle compact morphism is pullback along the pipeline hom. -/
theorem completedZetaZeroPoleResidueRectangleGeneratorHom_pullback
    (R : ℝ) (presheaf : TraceCorQPresheaf) :
    TraceAnalyticGeometricGenerator.pullback
        presheaf
        (completedZetaZeroPoleResidueRectangleGeneratorHom R) =
      presheaf.pullback
        (completedZetaZeroPoleResidueRectanglePipeline_hom R) :=
  rfl

/-- Pullback of a representable along the residue rectangle compact morphism is precomposition. -/
theorem completedZetaZeroPoleResidueRectangleGeneratorHom_representablePrecomposition
    (R : ℝ) (target : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullback.compactGeneratorComponent
        target.presheaf
        (completedZetaZeroPoleResidueRectangleGeneratorHom R) =
      TraceSixFunctorPullback.representablePrecompositionOperator
        target
        (completedZetaZeroPoleResidueRectangleGeneratorHom R) :=
  TraceSixFunctorPullback.compactGeneratorComponent_representable
    target
    (completedZetaZeroPoleResidueRectangleGeneratorHom R)

/-- Pushforward along the residue rectangle compact morphism is postcomposition at any probe. -/
theorem completedZetaZeroPoleResidueRectangleGeneratorHom_representablePostcomposition
    (R : ℝ) (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPushforward.compactGeneratorComponent
        probe
        (completedZetaZeroPoleResidueRectangleGeneratorHom R) =
      TraceSixFunctorPushforward.representablePostcompositionOperator
        probe
        (completedZetaZeroPoleResidueRectangleGeneratorHom R) :=
  TraceSixFunctorPushforward.compactGeneratorComponent_representable
    probe
    (completedZetaZeroPoleResidueRectangleGeneratorHom R)

/-- Pullback-precomposition commutes with residue-rectangle pushforward-postcomposition. -/
theorem completedZetaZeroPoleResidueRectangleGeneratorHom_pullbackPushforward_naturality
    (R : ℝ)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullback.representablePrecompositionOperator
        (completedZetaZeroPoleResidueRectangleSourceGenerator R)
        probe ≫
        TraceSixFunctorPushforward.representablePostcompositionOperator
          probeSource
          (completedZetaZeroPoleResidueRectangleGeneratorHom R) =
      TraceSixFunctorPushforward.representablePostcompositionOperator
          probeTarget
          (completedZetaZeroPoleResidueRectangleGeneratorHom R) ≫
        TraceSixFunctorPullback.representablePrecompositionOperator
          completedZetaZeroPoleResidueRectangleTargetGenerator
          probe :=
  TraceSixFunctorPullbackPushforward.representableOperator_naturality
    (completedZetaZeroPoleResidueRectangleGeneratorHom R)
    probe

end AnalyticMotives
end LFunctions
end Boundary
