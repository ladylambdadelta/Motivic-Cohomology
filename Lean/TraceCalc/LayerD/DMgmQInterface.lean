import TraceCalc.LayerD.MotivicRecognition.AdmissibleLocalizationAssembly
import TraceCalc.LayerD.MotivicRecognition.RecognitionSurface
import TraceCalc.LayerALegacy.Extensions.SyntacticTraceDMgmEquivalence

universe u v w x y z

namespace TraceCalc
namespace LayerD

open MotivicRecognition

def canonicalTraceToDMgmComparisonTarget (syntacticPresentation : Type u)
    [CategoryInfra.PresentationQuiver syntacticPresentation] :
    CategoryInfra.SyntacticTraceDMgm.TraceToDMgmComparisonTarget syntacticPresentation :=
  CategoryInfra.SyntacticTraceDMgm.TraceToDMgmComparisonTarget.syntactic
    syntacticPresentation

/-
Concrete DM_gm(Q) interface layer.

This file defines the canonical concrete interface `DMgmQPiZeroInterface` that bundles the trace
presentation, the classical motivic presentation, the DM_gm(Q) structural target, and its
certification, then derives the target-recognition milestone realization directly from those
inputs.

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
    ∀ (syntacticPresentation : Type u) [CategoryInfra.PresentationQuiver syntacticPresentation],
      (canonicalTraceToDMgmComparisonTarget syntacticPresentation).enhancement.Obj →
        presentation.motivicCategory.Object
  interpretBaseHom :
    ∀ {syntacticPresentation : Type u} [CategoryInfra.PresentationQuiver syntacticPresentation]
      {X Y : (canonicalTraceToDMgmComparisonTarget syntacticPresentation).enhancement.Obj},
      (canonicalTraceToDMgmComparisonTarget syntacticPresentation).enhancement.category.Pi0Hom X Y →
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
    (target : ClassicalDMgmQTarget.{u, v, w, x, y, z} trace presentation)
    (certified : CertifiedClassicalDMgmQTarget.{u, v, w, x, y, z}
      trace presentation target) :
    Prop :=
  target.compactGeometricGenerationTarget = certified.compactGeometricGeneration_holds ∧
    (target.exactTriangulatedStructureTarget = certified.exactTriangulated_holds ∧
      target.symmetricMonoidalStructureTarget = certified.symmetricMonoidal_holds)

theorem certifiedPiZeroRecognition_holds
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    {target : ClassicalDMgmQTarget.{u, v, w, x, y, z} trace presentation}
    (certified : CertifiedClassicalDMgmQTarget.{u, v, w, x, y, z}
      trace presentation target) :
    certifiedPiZeroRecognitionStatement target certified :=
  ⟨Subsingleton.elim _ _,
    ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩

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
      ∀ (syntacticPresentation : Type u) [CategoryInfra.PresentationQuiver syntacticPresentation],
        (canonicalTraceToDMgmComparisonTarget syntacticPresentation).enhancement.Obj →
          presentation.motivicCategory.Object)
    (interpretBaseHom :
      ∀ {syntacticPresentation : Type u} [CategoryInfra.PresentationQuiver syntacticPresentation]
        {X Y : (canonicalTraceToDMgmComparisonTarget syntacticPresentation).enhancement.Obj},
        (canonicalTraceToDMgmComparisonTarget syntacticPresentation).enhancement.category.Pi0Hom X Y →
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
  piZeroRecognitionTarget := certifiedPiZeroRecognitionStatement target certified
  piZeroRecognitionTarget_holds := certifiedPiZeroRecognition_holds certified

theorem ofCertifiedClassicalTarget_target_eq
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (target : ClassicalDMgmQTarget.{u, v, w, x, y, z} trace presentation)
    (certified : CertifiedClassicalDMgmQTarget.{u, v, w, x, y, z}
      trace presentation target)
    (interpretBase :
      ∀ (syntacticPresentation : Type u) [CategoryInfra.PresentationQuiver syntacticPresentation],
        (canonicalTraceToDMgmComparisonTarget syntacticPresentation).enhancement.Obj →
          presentation.motivicCategory.Object)
    (interpretBaseHom :
      ∀ {syntacticPresentation : Type u} [CategoryInfra.PresentationQuiver syntacticPresentation]
        {X Y : (canonicalTraceToDMgmComparisonTarget syntacticPresentation).enhancement.Obj},
        (canonicalTraceToDMgmComparisonTarget syntacticPresentation).enhancement.category.Pi0Hom X Y →
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
      ∀ (syntacticPresentation : Type u) [CategoryInfra.PresentationQuiver syntacticPresentation],
        (canonicalTraceToDMgmComparisonTarget syntacticPresentation).enhancement.Obj →
          presentation.motivicCategory.Object)
    (interpretBaseHom :
      ∀ {syntacticPresentation : Type u} [CategoryInfra.PresentationQuiver syntacticPresentation]
        {X Y : (canonicalTraceToDMgmComparisonTarget syntacticPresentation).enhancement.Obj},
        (canonicalTraceToDMgmComparisonTarget syntacticPresentation).enhancement.category.Pi0Hom X Y →
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

end LayerD
end TraceCalc
