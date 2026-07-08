import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Unstable.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Localization.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.LocalizationInput.AcyclicGenerators.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.LocalizationInput.InversionAcyclicBridge.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.LocalizationInput.ShortComplex.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.LocalizationInput.ShortComplex.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.LocalizationInput.NamedExactness.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.LocalizationInput.NamedProjections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.LocalizationInput.NamedRotationExactness.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.LocalizationInput.NamedRotationProjections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.LocalizationInput.NamedShortComplex.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.LocalizationInput.NamedTriangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.LocalizationInput.Triangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.LocalizationInput.Triangles.NamedMaps.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.LocalizationInput.Triangles.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.LocalizationInput.Triangles.RotationProjections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Localization.Representatives.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Unstable.Inputs.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceExpressions.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.RewriteGenerators.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.RewritePaths.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.RewriteMaps.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.RewriteMaps.ByKind.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.RewriteRelations.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.RewriteCertificates.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceTransport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.ResidueChannelPresentation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Presheaves.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CalculusGenerators.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Comparison.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Realizations.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Examples.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Motives.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TateStabilization.RotationExactness.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TateStabilization.ShortComplex.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TateStabilization.RotationShortComplex.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Facade.TateWeightDrop.Owner

/-!
# Top analytic-motives root facade

This file owns the top-level public root facade.  It collects the public
unstable, localization, localization-input short-complex, named
analytic-generator short-complex, cone triangle, acyclic generators, inversion-acyclic bridges,
projections, exactness, and rotated
exactness and projections, and cone-triangle named-map exactness/rotation projections,
localization-representative, unstable-input,
trace-expression, rewrite-map, by-kind rewrite-map, rewrite-certificate,
rewrite-generator, rewrite-path, rewrite-relation, trace-transport,
residue-channel presentation, Q-linear trace-correspondence, trace-presheaf,
calculus-generator, compact-geometric, comparison, realization, and example
root surfaces, plus the motive-facing aggregate root and Tate short-complex
public surfaces, under the
`AnalyticMotivesRoot` namespace.  The summary theorems below expose a compact
cross-section of the concrete analytic, Q-linear, realization, and example
facts available from the split root surface.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public root summary: certified presentations count imported rectangles by payload length. -/
theorem AnalyticMotivesRoot.rootFacade_residueChannel_importedRectangleCount_eq_length
    (presentation : CertifiedResidueChannelPresentation) :
    presentation.importedRectangleCount =
      presentation.importedRectangles.length :=
  AnalyticMotivesRoot.residueChannelSummary_importedRectangleCount_eq_length
    presentation

/-- Public root summary: trace-correspondence compact composition is trace-hom composition. -/
theorem AnalyticMotivesRoot.rootFacade_compactGenerator_comp_traceHom
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    (left ≫ right).traceHom =
      left.traceHom ≫ right.traceHom :=
  AnalyticMotivesRoot.rootSummary_compactGenerator_comp_traceHom
    left
    right

/-- Public root summary: representable presheaf sections recover trace correspondences. -/
theorem AnalyticMotivesRoot.rootFacade_representable_sections
    (source target : TraceCorQObject) :
    (TraceCorQPresheaf.representable target).sections source =
      ModuleCat.of Rat (source ⟶ target) :=
  AnalyticMotivesRoot.tracePresheafSummary_representable_sections
    source
    target

/-- Public root summary: analytic and algebraic Stokes realizations share the same preimage. -/
theorem AnalyticMotivesRoot.rootFacade_stokes_realization_preimage_agreement
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.stokesMap source target) =
      TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.stokesMap source target) :=
  AnalyticMotivesRoot.realizationSummary_stokes_preimage_agreement
    source
    target

/-- Public root summary: completed-zeta residue rectangle soundness is available at the root. -/
theorem AnalyticMotivesRoot.rootFacade_completedZeta_residueGenerator_sound
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {R : ℝ} (hR : 0 < R) :
    completedZetaZeroPoleFiniteSquareBoundaryTrace f R =
      completedZetaZeroPoleFiniteSquareResidueTrace f :=
  AnalyticMotivesRoot.examples_completedZeta_residueGenerator_sound
    f
    hPhi
    hR

/-- Public root summary: the additive analytic homotopy category is triangulated. -/
def AnalyticMotivesRoot.rootFacade_triangulatedStructure :
    IsTriangulated TraceAnalyticAdditiveHomotopyCategory :=
  AnalyticMotivesRoot.rootSummary_triangulatedStructure

/-- Public root summary: the additive analytic homotopy category is pretriangulated. -/
def AnalyticMotivesRoot.rootFacade_pretriangulatedStructure :
    Pretriangulated TraceAnalyticAdditiveHomotopyCategory :=
  AnalyticMotivesRoot.rootSummary_pretriangulatedStructure

/-- Public root summary: root distinguished triangles are Mathlib's distinguished
triangles. -/
theorem AnalyticMotivesRoot.rootFacade_distinguishedTriangles_eq :
    TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles =
      Pretriangulated.distTriang TraceAnalyticAdditiveHomotopyCategory :=
  AnalyticMotivesRoot.rootSummary_distinguishedTriangles_eq

/-- Public root summary: additive analytic mapping-cone triangles are distinguished. -/
theorem AnalyticMotivesRoot.rootFacade_mappingCone_triangle_distinguished
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target) :
    CochainComplex.mappingCone.triangleh hom ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  AnalyticMotivesRoot.rootSummary_mappingCone_triangle_distinguished
    hom

/-- Public root summary: shifted bounded analytic maps have full iso-bounded cone packages. -/
def AnalyticMotivesRoot.rootFacade_shiftedBoundedConePackage
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded
      bound :=
  AnalyticMotivesRoot.rootSummary_shiftedBoundedConePackage
    hom
    shift

/-- Public root summary: shifted bounded cone short complexes have zero composite. -/
theorem AnalyticMotivesRoot.rootFacade_shiftedBoundedConeShortComplex_zero
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage_shortComplex
      hom
      shift).f ≫
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage_shortComplex
          hom
          shift).g =
      0 :=
  AnalyticMotivesRoot.rootSummary_shiftedBoundedConeShortComplex_zero
    hom
    shift

/-- Public root summary: rotated bounded cone triangles are distinguished. -/
theorem AnalyticMotivesRoot.rootFacade_rotatedBoundedConeTriangle_distinguished
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    AnalyticMotivesRoot.rootSummary_rotatedBoundedConeTriangle hom ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  AnalyticMotivesRoot.rootSummary_rotatedBoundedConeTriangle_distinguished
    hom

/-- Public root summary: inverse-rotated bounded cone triangles are distinguished. -/
theorem AnalyticMotivesRoot.rootFacade_inverseRotatedBoundedConeTriangle_distinguished
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    AnalyticMotivesRoot.rootSummary_inverseRotatedBoundedConeTriangle hom ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  AnalyticMotivesRoot.rootSummary_inverseRotatedBoundedConeTriangle_distinguished
    hom

/-- Public root summary: the first two morphisms of the rotated bounded cone compose to
zero. -/
theorem AnalyticMotivesRoot.rootFacade_rotatedBoundedConeTriangle_first_comp_second
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (AnalyticMotivesRoot.rootSummary_rotatedBoundedConeTriangle
      hom).mor₁ ≫
        (AnalyticMotivesRoot.rootSummary_rotatedBoundedConeTriangle
          hom).mor₂ =
      0 :=
  AnalyticMotivesRoot.rootSummary_rotatedBoundedConeTriangle_first_comp_second
    hom

/-- Public root summary: the second and third morphisms of the rotated bounded cone
compose to zero. -/
theorem AnalyticMotivesRoot.rootFacade_rotatedBoundedConeTriangle_second_comp_third
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (AnalyticMotivesRoot.rootSummary_rotatedBoundedConeTriangle
      hom).mor₂ ≫
        (AnalyticMotivesRoot.rootSummary_rotatedBoundedConeTriangle
          hom).mor₃ =
      0 :=
  AnalyticMotivesRoot.rootSummary_rotatedBoundedConeTriangle_second_comp_third
    hom

/-- Public root summary: the third morphism followed by the shifted first morphism of the
rotated bounded cone is zero. -/
theorem AnalyticMotivesRoot.rootFacade_rotatedBoundedConeTriangle_third_comp_shifted_first
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (AnalyticMotivesRoot.rootSummary_rotatedBoundedConeTriangle
      hom).mor₃ ≫
        (AnalyticMotivesRoot.rootSummary_rotatedBoundedConeTriangle
          hom).mor₁⟦(1 : ℤ)⟧' =
      0 :=
  AnalyticMotivesRoot.rootSummary_rotatedBoundedConeTriangle_third_comp_shifted_first
    hom

/-- Public root summary: the first two morphisms of the inverse-rotated bounded cone
compose to zero. -/
theorem AnalyticMotivesRoot.rootFacade_inverseRotatedBoundedConeTriangle_first_comp_second
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (AnalyticMotivesRoot.rootSummary_inverseRotatedBoundedConeTriangle
      hom).mor₁ ≫
        (AnalyticMotivesRoot.rootSummary_inverseRotatedBoundedConeTriangle
          hom).mor₂ =
      0 :=
  AnalyticMotivesRoot.rootSummary_inverseRotatedBoundedConeTriangle_first_comp_second
    hom

/-- Public root summary: the second and third morphisms of the inverse-rotated bounded cone
compose to zero. -/
theorem AnalyticMotivesRoot.rootFacade_inverseRotatedBoundedConeTriangle_second_comp_third
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (AnalyticMotivesRoot.rootSummary_inverseRotatedBoundedConeTriangle
      hom).mor₂ ≫
        (AnalyticMotivesRoot.rootSummary_inverseRotatedBoundedConeTriangle
          hom).mor₃ =
      0 :=
  AnalyticMotivesRoot.rootSummary_inverseRotatedBoundedConeTriangle_second_comp_third
    hom

/-- Public root summary: the third morphism followed by the shifted first morphism of the
inverse-rotated bounded cone is zero. -/
theorem AnalyticMotivesRoot.rootFacade_inverseRotatedBoundedConeTriangle_third_comp_shifted_first
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (AnalyticMotivesRoot.rootSummary_inverseRotatedBoundedConeTriangle
      hom).mor₃ ≫
        (AnalyticMotivesRoot.rootSummary_inverseRotatedBoundedConeTriangle
          hom).mor₁⟦(1 : ℤ)⟧' =
      0 :=
  AnalyticMotivesRoot.rootSummary_inverseRotatedBoundedConeTriangle_third_comp_shifted_first
    hom

/-- Public root summary: shifted rotated bounded cone triangles are distinguished. -/
theorem AnalyticMotivesRoot.rootFacade_shiftedRotatedBoundedConeTriangle_distinguished
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    AnalyticMotivesRoot.rootSummary_shiftedRotatedBoundedConeTriangle hom shift ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  AnalyticMotivesRoot.rootSummary_shiftedRotatedBoundedConeTriangle_distinguished
    hom
    shift

/-- Public root summary: shifted inverse-rotated bounded cone triangles are distinguished. -/
theorem AnalyticMotivesRoot.rootFacade_shiftedInverseRotatedBoundedConeTriangle_distinguished
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    AnalyticMotivesRoot.rootSummary_shiftedInverseRotatedBoundedConeTriangle hom shift ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  AnalyticMotivesRoot.rootSummary_shiftedInverseRotatedBoundedConeTriangle_distinguished
    hom
    shift

/-- Public root summary: the first two morphisms of the shifted rotated bounded cone
compose to zero. -/
theorem AnalyticMotivesRoot.rootFacade_shiftedRotatedBoundedConeTriangle_first_comp_second
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (AnalyticMotivesRoot.rootSummary_shiftedRotatedBoundedConeTriangle
      hom
      shift).mor₁ ≫
        (AnalyticMotivesRoot.rootSummary_shiftedRotatedBoundedConeTriangle
          hom
          shift).mor₂ =
      0 :=
  AnalyticMotivesRoot.rootSummary_shiftedRotatedBoundedConeTriangle_first_comp_second
    hom
    shift

/-- Public root summary: the second and third morphisms of the shifted rotated bounded
cone compose to zero. -/
theorem AnalyticMotivesRoot.rootFacade_shiftedRotatedBoundedConeTriangle_second_comp_third
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (AnalyticMotivesRoot.rootSummary_shiftedRotatedBoundedConeTriangle
      hom
      shift).mor₂ ≫
        (AnalyticMotivesRoot.rootSummary_shiftedRotatedBoundedConeTriangle
          hom
          shift).mor₃ =
      0 :=
  AnalyticMotivesRoot.rootSummary_shiftedRotatedBoundedConeTriangle_second_comp_third
    hom
    shift

/-- Public root summary: the third morphism followed by the shifted first morphism of the
shifted rotated bounded cone is zero. -/
theorem AnalyticMotivesRoot.rootFacade_shiftedRotatedBoundedConeTriangle_third_comp_shifted_first
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (AnalyticMotivesRoot.rootSummary_shiftedRotatedBoundedConeTriangle
      hom
      shift).mor₃ ≫
        (AnalyticMotivesRoot.rootSummary_shiftedRotatedBoundedConeTriangle
          hom
          shift).mor₁⟦(1 : ℤ)⟧' =
      0 :=
  AnalyticMotivesRoot.rootSummary_shiftedRotatedBoundedConeTriangle_third_comp_shifted_first
    hom
    shift

/-- Public root summary: the first two morphisms of the shifted inverse-rotated bounded
cone compose to zero. -/
theorem AnalyticMotivesRoot.rootFacade_shiftedInverseRotatedBoundedConeTriangle_first_comp_second
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (AnalyticMotivesRoot.rootSummary_shiftedInverseRotatedBoundedConeTriangle
      hom
      shift).mor₁ ≫
        (AnalyticMotivesRoot.rootSummary_shiftedInverseRotatedBoundedConeTriangle
          hom
          shift).mor₂ =
      0 :=
  AnalyticMotivesRoot.rootSummary_shiftedInverseRotatedBoundedConeTriangle_first_comp_second
    hom
    shift

/-- Public root summary: the second and third morphisms of the shifted inverse-rotated
bounded cone compose to zero. -/
theorem AnalyticMotivesRoot.rootFacade_shiftedInverseRotatedBoundedConeTriangle_second_comp_third
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (AnalyticMotivesRoot.rootSummary_shiftedInverseRotatedBoundedConeTriangle
      hom
      shift).mor₂ ≫
        (AnalyticMotivesRoot.rootSummary_shiftedInverseRotatedBoundedConeTriangle
          hom
          shift).mor₃ =
      0 :=
  AnalyticMotivesRoot.rootSummary_shiftedInverseRotatedBoundedConeTriangle_second_comp_third
    hom
    shift

/-- Public root summary: the third morphism followed by the shifted first morphism of the
shifted inverse-rotated bounded cone is zero. -/
theorem AnalyticMotivesRoot.rootFacade_shiftedInverseRotatedBoundedConeTriangle_third_comp_shifted_first
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (AnalyticMotivesRoot.rootSummary_shiftedInverseRotatedBoundedConeTriangle
      hom
      shift).mor₃ ≫
        (AnalyticMotivesRoot.rootSummary_shiftedInverseRotatedBoundedConeTriangle
          hom
          shift).mor₁⟦(1 : ℤ)⟧' =
      0 :=
  AnalyticMotivesRoot.rootSummary_shiftedInverseRotatedBoundedConeTriangle_third_comp_shifted_first
    hom
    shift

/-- Public root summary: in a shifted rotated cone, cone inclusion followed by
connecting map is zero. -/
theorem AnalyticMotivesRoot.rootFacade_shiftedRotatedCone_secondMap_comp_connectingMap
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap
          (hom.shift shift) ≫
        TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
          (hom.shift shift) =
      0 :=
  AnalyticMotivesRoot.rootSummary_shiftedRotatedCone_secondMap_comp_connectingMap
    hom
    shift

/-- Public root summary: in a shifted rotated cone, connecting map followed by the
negative shifted bounded map is zero. -/
theorem AnalyticMotivesRoot.rootFacade_shiftedRotatedCone_connectingMap_comp_negative_shifted_firstMap
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
          (hom.shift shift) ≫
        -((TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
          (hom.shift shift))⟦(1 : ℤ)⟧') =
      0 :=
  AnalyticMotivesRoot.rootSummary_shiftedRotatedCone_connectingMap_comp_negative_shifted_firstMap
    hom
    shift

/-- Public root summary: in a shifted inverse-rotated cone, shifted negative connecting
map followed by the shifted bounded map is zero. -/
theorem AnalyticMotivesRoot.rootFacade_shiftedInverseRotatedCone_negative_shifted_connectingMap_comp_firstMap
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (-(TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        (hom.shift shift))⟦(-1 : ℤ)⟧' ≫
        (shiftEquiv TraceAnalyticAdditiveHomotopyCategory
          (1 : ℤ)).unitIso.inv.app _) ≫
        TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
          (hom.shift shift) =
      0 :=
  AnalyticMotivesRoot.rootSummary_shiftedInverseRotatedCone_negative_shifted_connectingMap_comp_firstMap
    hom
    shift

/-- Public root summary: in a shifted inverse-rotated cone, shifted bounded map followed
by transported cone inclusion is zero. -/
theorem AnalyticMotivesRoot.rootFacade_shiftedInverseRotatedCone_firstMap_comp_transport_secondMap
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
          (hom.shift shift) ≫
        TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap
          (hom.shift shift) ≫
        (shiftEquiv TraceAnalyticAdditiveHomotopyCategory
          (1 : ℤ)).counitIso.inv.app _ =
      0 :=
  AnalyticMotivesRoot.rootSummary_shiftedInverseRotatedCone_firstMap_comp_transport_secondMap
    hom
    shift

end AnalyticMotives
end LFunctions
end Boundary
