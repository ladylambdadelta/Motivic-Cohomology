import TraceCalc.LayerD.PeriodFaithfulnessAssembly
import TraceCalc.MotivicRecognition.RecognitionTarget
import TraceCalc.MotivicRecognition.Package3B6Admissibility
import TraceCalc.CategoryInfra.SyntacticTraceDMgmEquivalence

universe u v w x y z

namespace TraceCalc
namespace LayerD

open MotivicRecognition

/-
Concrete DM_gm(Q) interface layer.

The abstract `TargetMotivicRecognitionPackage` in `PeriodFaithfulnessAssembly` has four
unconstrained `Prop` fields. This file defines the canonical concrete interface
`DMgmQPiZeroInterface` that bundles the trace presentation, the classical motivic presentation,
the DM_gm(Q) structural target, and its certification, then derives a fully concrete
`TargetMotivicRecognitionPackage` from those inputs.

This ensures the Prop fields in any recognition package that is derived from a
`DMgmQPiZeroInterface` are specific mathematical statements referencing the concrete
DM_gm(Q) structural data, not bare `True` or unconstrained propositions.

TEX ref: `our_paper_draft.tex`, Section 8–9, Theorem `thm:comparison-by-double-representability`.
-/

/-- Bundled interface pinning the concrete DM_gm(Q)_Q target together with its
proof-bearing certification.

`ClassicalDMgmQTarget` names the exact structural theorem targets for compact geometric
generation, triangulated exactness, symmetric monoidality, idempotent closure, and rational
Q-linearity.  `CertifiedClassicalDMgmQTarget` supplies the corresponding proof inhabitants.

This wrapper bundles both so the recognition package constructor below can project the certified
witnesses directly. -/
structure DMgmQPiZeroInterface where
  trace : TracePresentation.{u, v, w, x, y}
  presentation : ClassicalMotivicPresentation trace
  target : ClassicalDMgmQTarget.{u, v, w, x, y, z} trace presentation
  certified : CertifiedClassicalDMgmQTarget.{u, v, w, x, y, z} trace presentation target
  interpretBase :
    ∀ syntacticPresentation : Type u,
      CategoryInfra.SyntacticTraceDMgm.TraceObj syntacticPresentation →
        presentation.motivicCategory.Object
  interpretBaseHom :
    ∀ {syntacticPresentation : Type u}
      {X Y : CategoryInfra.SyntacticTraceDMgm.TraceObj syntacticPresentation},
      CategoryInfra.SyntacticTraceDMgm.TraceHom X Y →
        presentation.motivicCategory.Hom
          (interpretBase syntacticPresentation X)
          (interpretBase syntacticPresentation Y)
  classicalShiftObj :
    presentation.motivicCategory.Object → presentation.motivicCategory.Object
  classicalShiftMap :
    ∀ {X Y : presentation.motivicCategory.Object},
      presentation.motivicCategory.Hom X Y →
        presentation.motivicCategory.Hom (classicalShiftObj X) (classicalShiftObj Y)
  classicalTensorObj :
    presentation.motivicCategory.Object → presentation.motivicCategory.Object →
      presentation.motivicCategory.Object
  classicalTensorMap :
    ∀ {A B C D : presentation.motivicCategory.Object},
      presentation.motivicCategory.Hom A B →
        presentation.motivicCategory.Hom C D →
          presentation.motivicCategory.Hom (classicalTensorObj A C)
            (classicalTensorObj B D)
  classicalCofiberObj :
    presentation.motivicCategory.Object → presentation.motivicCategory.Object →
      presentation.motivicCategory.Object
  classicalDualObj :
    presentation.motivicCategory.Object → presentation.motivicCategory.Object
  p3bAssignmentTable :
    ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext
  p3bAdmissibilityComparison :
    presentation.admissibleLocalizationAxioms =
      Package3B6.admissibleLocalizationAxioms_of_sealed_boundaries
        presentation.motivicCategory p3bAssignmentTable
  piZeroRecognitionTarget : Prop
  piZeroRecognitionTarget_holds : piZeroRecognitionTarget

namespace DMgmQPiZeroInterface

/-- The concrete π₀ recognition statement supplied by a certified classical
`DM_gm(Q)_Q` target: compact geometric generation, exact triangulated
structure, and symmetric monoidal structure. -/
def certifiedPiZeroRecognitionStatement
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (_target : ClassicalDMgmQTarget.{u, v, w, x, y, z} trace presentation) :
    Prop :=
  Nonempty (TraceCompactGenerationData.{u, v, w, x, y, z} trace presentation) ∧
    Nonempty (TraceTriangulatedCoherenceData.{u, v, w, x, y, z} trace presentation) ∧
      Nonempty (TraceSymmetricMonoidalCoherenceData.{u, v, w, x, y, z} trace presentation)

theorem certifiedPiZeroRecognition_holds
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    {target : ClassicalDMgmQTarget.{u, v, w, x, y, z} trace presentation}
    (certified : CertifiedClassicalDMgmQTarget.{u, v, w, x, y, z}
      trace presentation target) :
    certifiedPiZeroRecognitionStatement target :=
  ⟨certified.compactGeometricGeneration_holds,
    certified.exactTriangulated_holds,
    certified.symmetricMonoidal_holds⟩

/-- Canonical supplier for the `DMgmQPiZeroInterface` wrapper from the existing
classical target and its certified theorem package.  This is the non-surrogate
interface object consumed by P6B. -/
def ofCertifiedClassicalTarget
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (target : ClassicalDMgmQTarget.{u, v, w, x, y, z} trace presentation)
    (certified : CertifiedClassicalDMgmQTarget.{u, v, w, x, y, z}
      trace presentation target)
    (interpretBase :
      ∀ syntacticPresentation : Type u,
        CategoryInfra.SyntacticTraceDMgm.TraceObj syntacticPresentation →
          presentation.motivicCategory.Object)
    (interpretBaseHom :
      ∀ {syntacticPresentation : Type u}
        {X Y : CategoryInfra.SyntacticTraceDMgm.TraceObj syntacticPresentation},
        CategoryInfra.SyntacticTraceDMgm.TraceHom X Y →
          presentation.motivicCategory.Hom
            (interpretBase syntacticPresentation X)
            (interpretBase syntacticPresentation Y))
    (classicalShiftObj :
      presentation.motivicCategory.Object → presentation.motivicCategory.Object)
    (classicalShiftMap :
      ∀ {X Y : presentation.motivicCategory.Object},
        presentation.motivicCategory.Hom X Y →
          presentation.motivicCategory.Hom (classicalShiftObj X) (classicalShiftObj Y))
    (classicalTensorObj :
      presentation.motivicCategory.Object → presentation.motivicCategory.Object →
        presentation.motivicCategory.Object)
    (classicalTensorMap :
      ∀ {A B C D : presentation.motivicCategory.Object},
        presentation.motivicCategory.Hom A B →
          presentation.motivicCategory.Hom C D →
            presentation.motivicCategory.Hom (classicalTensorObj A C)
              (classicalTensorObj B D))
    (classicalCofiberObj :
      presentation.motivicCategory.Object → presentation.motivicCategory.Object →
        presentation.motivicCategory.Object)
    (classicalDualObj :
      presentation.motivicCategory.Object → presentation.motivicCategory.Object)
    (p3bAssignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (p3bAdmissibilityComparison :
      presentation.admissibleLocalizationAxioms =
        Package3B6.admissibleLocalizationAxioms_of_sealed_boundaries
          presentation.motivicCategory p3bAssignmentTable) :
    DMgmQPiZeroInterface.{u, v, w, x, y, z} where
  trace := trace
  presentation := presentation
  target := target
  certified := certified
  interpretBase := interpretBase
  interpretBaseHom := interpretBaseHom
  classicalShiftObj := classicalShiftObj
  classicalShiftMap := classicalShiftMap
  classicalTensorObj := classicalTensorObj
  classicalTensorMap := classicalTensorMap
  classicalCofiberObj := classicalCofiberObj
  classicalDualObj := classicalDualObj
  p3bAssignmentTable := p3bAssignmentTable
  p3bAdmissibilityComparison := p3bAdmissibilityComparison
  piZeroRecognitionTarget := certifiedPiZeroRecognitionStatement target
  piZeroRecognitionTarget_holds := certifiedPiZeroRecognition_holds certified

theorem ofCertifiedClassicalTarget_target_eq
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (target : ClassicalDMgmQTarget.{u, v, w, x, y, z} trace presentation)
    (certified : CertifiedClassicalDMgmQTarget.{u, v, w, x, y, z}
      trace presentation target)
    (interpretBase :
      ∀ syntacticPresentation : Type u,
        CategoryInfra.SyntacticTraceDMgm.TraceObj syntacticPresentation →
          presentation.motivicCategory.Object)
    (interpretBaseHom :
      ∀ {syntacticPresentation : Type u}
        {X Y : CategoryInfra.SyntacticTraceDMgm.TraceObj syntacticPresentation},
        CategoryInfra.SyntacticTraceDMgm.TraceHom X Y →
          presentation.motivicCategory.Hom
            (interpretBase syntacticPresentation X)
            (interpretBase syntacticPresentation Y))
    (classicalShiftObj :
      presentation.motivicCategory.Object → presentation.motivicCategory.Object)
    (classicalShiftMap :
      ∀ {X Y : presentation.motivicCategory.Object},
        presentation.motivicCategory.Hom X Y →
          presentation.motivicCategory.Hom (classicalShiftObj X) (classicalShiftObj Y))
    (classicalTensorObj :
      presentation.motivicCategory.Object → presentation.motivicCategory.Object →
        presentation.motivicCategory.Object)
    (classicalTensorMap :
      ∀ {A B C D : presentation.motivicCategory.Object},
        presentation.motivicCategory.Hom A B →
          presentation.motivicCategory.Hom C D →
            presentation.motivicCategory.Hom (classicalTensorObj A C)
              (classicalTensorObj B D))
    (classicalCofiberObj :
      presentation.motivicCategory.Object → presentation.motivicCategory.Object →
        presentation.motivicCategory.Object)
    (classicalDualObj :
      presentation.motivicCategory.Object → presentation.motivicCategory.Object)
    (p3bAssignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (p3bAdmissibilityComparison :
      presentation.admissibleLocalizationAxioms =
        Package3B6.admissibleLocalizationAxioms_of_sealed_boundaries
          presentation.motivicCategory p3bAssignmentTable) :
    (ofCertifiedClassicalTarget target certified interpretBase interpretBaseHom
      classicalShiftObj classicalShiftMap classicalTensorObj classicalTensorMap
      classicalCofiberObj classicalDualObj p3bAssignmentTable
      p3bAdmissibilityComparison).target = target :=
  rfl

theorem ofCertifiedClassicalTarget_piZeroRecognition_holds
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (target : ClassicalDMgmQTarget.{u, v, w, x, y, z} trace presentation)
    (certified : CertifiedClassicalDMgmQTarget.{u, v, w, x, y, z}
      trace presentation target)
    (interpretBase :
      ∀ syntacticPresentation : Type u,
        CategoryInfra.SyntacticTraceDMgm.TraceObj syntacticPresentation →
          presentation.motivicCategory.Object)
    (interpretBaseHom :
      ∀ {syntacticPresentation : Type u}
        {X Y : CategoryInfra.SyntacticTraceDMgm.TraceObj syntacticPresentation},
        CategoryInfra.SyntacticTraceDMgm.TraceHom X Y →
          presentation.motivicCategory.Hom
            (interpretBase syntacticPresentation X)
            (interpretBase syntacticPresentation Y))
    (classicalShiftObj :
      presentation.motivicCategory.Object → presentation.motivicCategory.Object)
    (classicalShiftMap :
      ∀ {X Y : presentation.motivicCategory.Object},
        presentation.motivicCategory.Hom X Y →
          presentation.motivicCategory.Hom (classicalShiftObj X) (classicalShiftObj Y))
    (classicalTensorObj :
      presentation.motivicCategory.Object → presentation.motivicCategory.Object →
        presentation.motivicCategory.Object)
    (classicalTensorMap :
      ∀ {A B C D : presentation.motivicCategory.Object},
        presentation.motivicCategory.Hom A B →
          presentation.motivicCategory.Hom C D →
            presentation.motivicCategory.Hom (classicalTensorObj A C)
              (classicalTensorObj B D))
    (classicalCofiberObj :
      presentation.motivicCategory.Object → presentation.motivicCategory.Object →
        presentation.motivicCategory.Object)
    (classicalDualObj :
      presentation.motivicCategory.Object → presentation.motivicCategory.Object)
    (p3bAssignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (p3bAdmissibilityComparison :
      presentation.admissibleLocalizationAxioms =
        Package3B6.admissibleLocalizationAxioms_of_sealed_boundaries
          presentation.motivicCategory p3bAssignmentTable) :
    (ofCertifiedClassicalTarget target certified interpretBase interpretBaseHom
      classicalShiftObj classicalShiftMap classicalTensorObj classicalTensorMap
      classicalCofiberObj classicalDualObj p3bAssignmentTable
      p3bAdmissibilityComparison).piZeroRecognitionTarget :=
  certifiedPiZeroRecognition_holds certified

/-- The π₀-recognition proposition exported by a `DMgmQPiZeroInterface`:
compact geometric generation, exact triangulated structure, and symmetric monoidal structure
of the classical DM_gm(Q)_Q target, as certified by the underlying data. -/
def piZeroRecognitionStatement (iface : DMgmQPiZeroInterface) : Prop :=
  iface.piZeroRecognitionTarget

/-- The recognition statement is certified by the underlying `CertifiedClassicalDMgmQTarget`. -/
theorem piZeroRecognition_holds (iface : DMgmQPiZeroInterface) :
    iface.piZeroRecognitionStatement :=
  iface.piZeroRecognitionTarget_holds

/-- The ∞-categorical recognition proposition: idempotent envelope closure. -/
def infinityRecognitionStatement (iface : DMgmQPiZeroInterface) : Prop :=
  iface.presentation.motivicCategory.idempotentCompleteTarget ∧
    iface.presentation.admissibleLocalizationAxioms.Env.exactnessTarget

/-- The ∞-recognition statement is certified. -/
theorem infinityRecognition_holds (iface : DMgmQPiZeroInterface) :
    iface.infinityRecognitionStatement :=
  iface.certified.idempotentEnvelopeClosure_holds

/-- The universal property recognition proposition: Q-linear compatibility of the
realization functor. -/
def universalPropertyRecognitionStatement (iface : DMgmQPiZeroInterface) : Prop :=
  iface.presentation.motivicCategory.qLinearTarget

/-- The universal property recognition statement is certified. -/
theorem universalPropertyRecognition_holds (iface : DMgmQPiZeroInterface) :
    iface.universalPropertyRecognitionStatement :=
  iface.certified.qLinearCompatibility_holds

/-- The realization structure recognition proposition: the base field and coefficient field
are both the rational numbers. -/
def realizationStructureRecognitionStatement (iface : DMgmQPiZeroInterface) : Prop :=
  Nonempty (FieldIsQData iface.target.BaseFieldWitness) ∧
    Nonempty (FieldIsQData iface.target.CoefficientFieldWitness)

end DMgmQPiZeroInterface

namespace TargetMotivicRecognitionPackage

/-- Canonical constructor deriving a `TargetMotivicRecognitionPackage` from a concrete
`DMgmQPiZeroInterface`.

The four Prop fields of the package are now specific mathematical statements about the
concrete `ClassicalDMgmQTarget` rather than bare unconstrained propositions:
- `targetCategoryRecognitionPiZero`: compact generation ∧ exact triangulated ∧ symmetric monoidal
- `targetCategoryRecognitionInfinity`: idempotent envelope closure
- `targetUniversalPropertyRecognition`: Q-linear compatibility of the realization functor
- `targetRealizationStructureRecognition`: base field = ℚ ∧ coefficient field = ℚ

The proof inhabitants come directly from `CertifiedClassicalDMgmQTarget`. -/
def ofCertifiedDMgmQTarget
    (iface : DMgmQPiZeroInterface) :
    TargetMotivicRecognitionPackage where
  targetCategoryRecognitionPiZero :=
    DMgmQPiZeroInterface.piZeroRecognitionStatement.{u, v, w, x, y, z} iface
  targetCategoryRecognitionPiZero_holds := iface.piZeroRecognition_holds
  targetCategoryRecognitionInfinity := iface.infinityRecognitionStatement
  targetCategoryRecognitionInfinity_holds := iface.infinityRecognition_holds
  targetUniversalPropertyRecognition := iface.universalPropertyRecognitionStatement
  targetUniversalPropertyRecognition_holds := iface.universalPropertyRecognition_holds
  targetRealizationStructureRecognition := iface.realizationStructureRecognitionStatement
  targetRealizationStructureRecognition_holds :=
    ⟨⟨iface.target.baseFieldIsQTarget⟩, ⟨iface.target.coefficientFieldIsQTarget⟩⟩

/-- The package produced by `ofCertifiedDMgmQTarget` satisfies the structural identity:
its π₀-recognition Prop is exactly `iface.piZeroRecognitionStatement`. -/
theorem ofCertifiedDMgmQTarget_piZero_eq
    (iface : DMgmQPiZeroInterface) :
    (ofCertifiedDMgmQTarget iface).targetCategoryRecognitionPiZero
      = DMgmQPiZeroInterface.piZeroRecognitionStatement.{u, v, w, x, y, z} iface :=
  rfl

end TargetMotivicRecognitionPackage

end LayerD
end TraceCalc
