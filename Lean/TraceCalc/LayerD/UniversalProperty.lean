import TraceCalc.LayerBNonCore.Interfaces.TraceEnvelope
import TraceCalc.LayerE.RealizableImage

universe u v

open CategoryTheory

namespace TraceCalc
namespace LayerD

/-- Scope marker for how much of the source presentation a realization has committed to.
The universal-property contract starts at the generator/envelope layer and factors to
all localized objects only after the contract is supplied. -/
inductive FrontierRealizationScope
  | generatorsOnly
  | envelopeLevel
  | allLocalizedObjects
  deriving DecidableEq, Repr

/-- Abstract admissible realization datum for the frontier/localization presentation.
This is the Lean skeleton corresponding to the manuscript's admissible geometric data:
it records target-side assignments and the named proof obligations they must satisfy,
without instantiating any motivic category or proving any comparison theorem. -/
structure AdmissibleFrontierRealization (ML : LayerB.MotivicLocalization.{u, v}) where
  Tgt : Type u
  [catTgt : Category.{v} Tgt]
  scope : FrontierRealizationScope
  realizeSyntaxObj : ML.F.Syntax -> Tgt
  realizeEnvelopeObj : ML.F.Envelope -> Tgt
  generatorCompatibility : Prop
  relationSoundness : Prop
  exactnessCompatibility : Prop
  monoidalCompatibility : Prop
  idempotentCompletionCompatibility : Prop
  weakEquivalenceInverted : Prop
  nisnevichCompatibility : Prop
  a1Compatibility : Prop
  tateCompatibility : Prop

attribute [instance] AdmissibleFrontierRealization.catTgt

/-- A factorization through the localized frontier source after passage to the homotopy
category / triangulated shadow.
This is the `pi_0`-level contract target of the universal property: once the datum above
is supplied, the realization should extend on objects and named exact/monoidal structure
without yet claiming higher coherent comparison data. -/
structure FrontierPiZeroFactorization (ML : LayerB.MotivicLocalization.{u, v})
    (R : AdmissibleFrontierRealization ML) where
  realizeLocalizedObj : ML.Loc -> R.Tgt
  factorsEnvelopeAssignment : Prop
  factorsGeneratorAssignment : Prop
  preservesExactTriangles : Prop
  preservesTensor : Prop
  preservesIdempotentCompletion : Prop

/-- Full stable `infty`-categorical factorization contract.
This strictly refines the `pi_0`-level factorization by recording the higher-coherence
obligations that a later `infty`-comparison theorem must consume. -/
structure FrontierInfinityFactorization (ML : LayerB.MotivicLocalization.{u, v})
    (R : AdmissibleFrontierRealization ML) extends FrontierPiZeroFactorization ML R where
  preservesMappingSpectra : Prop
  preservesHigherCoherence : Prop
  preservesStableInfinityStructure : Prop
  preservesSymmetricMonoidalInfinityStructure : Prop

/-- Explicit bridge contract explaining how an `infty`-factorization produces a `pi_0`
shadow and when every `pi_0` factorization arises that way. This is the minimal data
needed to prove that `pi_0` initiality is a shadow of `infty` initiality, rather than a
separate assumption. -/
structure FrontierInfinityToPiZeroShadowContract
    (ML : LayerB.MotivicLocalization.{u, v}) where
  shadow : forall {R : AdmissibleFrontierRealization ML},
    FrontierInfinityFactorization ML R -> FrontierPiZeroFactorization ML R
  liftsPiZero : forall {R : AdmissibleFrontierRealization ML}
    (F : FrontierPiZeroFactorization ML R),
      Nonempty { FInf : FrontierInfinityFactorization ML R // shadow FInf = F }

namespace FrontierPiZeroFactorization

variable {ML : LayerB.MotivicLocalization.{u, v}}
variable {R : AdmissibleFrontierRealization ML}

/-- The natural equivalence notion available at the current abstract level: two
factorizations are equivalent exactly when they agree as factorization data. -/
def Equivalent (F1 F2 : FrontierPiZeroFactorization ML R) : Prop :=
  F1 = F2

/-- The structural compatibility propositions recorded by a `pi_0` factorization. -/
structure RecordedRealizationStructure (F : FrontierPiZeroFactorization ML R) where
  exactTriangles : Prop
  tensor : Prop
  idempotentCompletion : Prop

theorem equivalent_iff_eq (F1 F2 : FrontierPiZeroFactorization ML R) :
    F1.Equivalent F2 ↔ F1 = F2 := by
  rfl

def recordsRealizationStructure (F : FrontierPiZeroFactorization ML R) :
    FrontierPiZeroFactorization.RecordedRealizationStructure F :=
  ⟨F.preservesExactTriangles, F.preservesTensor, F.preservesIdempotentCompletion⟩

end FrontierPiZeroFactorization

namespace FrontierInfinityFactorization

variable {ML : LayerB.MotivicLocalization.{u, v}}
variable {R : AdmissibleFrontierRealization ML}

/-- Forget the higher-coherent fields of an infinity factorization and keep only
its `π₀`-level factorization shadow. -/
def toPiZeroFactorization (F : FrontierInfinityFactorization ML R) :
    FrontierPiZeroFactorization ML R where
  realizeLocalizedObj := F.realizeLocalizedObj
  factorsEnvelopeAssignment := F.factorsEnvelopeAssignment
  factorsGeneratorAssignment := F.factorsGeneratorAssignment
  preservesExactTriangles := F.preservesExactTriangles
  preservesTensor := F.preservesTensor
  preservesIdempotentCompletion := F.preservesIdempotentCompletion

@[simp] theorem toPiZeroFactorization_realizeLocalizedObj
    (F : FrontierInfinityFactorization ML R) :
    F.toPiZeroFactorization.realizeLocalizedObj = F.realizeLocalizedObj :=
  rfl

@[simp] theorem toPiZeroFactorization_factorsEnvelopeAssignment
    (F : FrontierInfinityFactorization ML R) :
    F.toPiZeroFactorization.factorsEnvelopeAssignment = F.factorsEnvelopeAssignment :=
  rfl

@[simp] theorem toPiZeroFactorization_factorsGeneratorAssignment
    (F : FrontierInfinityFactorization ML R) :
    F.toPiZeroFactorization.factorsGeneratorAssignment = F.factorsGeneratorAssignment :=
  rfl

@[simp] theorem toPiZeroFactorization_preservesExactTriangles
    (F : FrontierInfinityFactorization ML R) :
    F.toPiZeroFactorization.preservesExactTriangles = F.preservesExactTriangles :=
  rfl

@[simp] theorem toPiZeroFactorization_preservesTensor
    (F : FrontierInfinityFactorization ML R) :
    F.toPiZeroFactorization.preservesTensor = F.preservesTensor :=
  rfl

@[simp] theorem toPiZeroFactorization_preservesIdempotentCompletion
    (F : FrontierInfinityFactorization ML R) :
    F.toPiZeroFactorization.preservesIdempotentCompletion =
      F.preservesIdempotentCompletion :=
  rfl

/-- The structural compatibility propositions recorded by an `infty` factorization. -/
structure RecordedRealizationStructure (F : FrontierInfinityFactorization ML R) where
  exactTriangles : Prop
  tensor : Prop
  idempotentCompletion : Prop
  mappingSpectra : Prop
  higherCoherence : Prop
  stableStructure : Prop
  symmetricMonoidalStructure : Prop

def recordsRealizationStructure (F : FrontierInfinityFactorization ML R) :
    FrontierInfinityFactorization.RecordedRealizationStructure F :=
  ⟨F.preservesExactTriangles, F.preservesTensor, F.preservesIdempotentCompletion,
    F.preservesMappingSpectra, F.preservesHigherCoherence,
    F.preservesStableInfinityStructure, F.preservesSymmetricMonoidalInfinityStructure⟩

end FrontierInfinityFactorization

/-- Chosen infinity lift of every `π₀` factorization.

This is the constructive content needed to upgrade a `π₀`-level factorization
package to an infinity-level one: not just existence, but a specified lift with
the correct shadow. -/
structure FrontierInfinityLiftData
    (ML : LayerB.MotivicLocalization.{u, v}) where
  lift :
    ∀ {R : AdmissibleFrontierRealization ML},
      FrontierPiZeroFactorization ML R → FrontierInfinityFactorization ML R
  shadow_lift :
    ∀ {R : AdmissibleFrontierRealization ML}
      (F : FrontierPiZeroFactorization ML R),
      (lift F).toPiZeroFactorization = F

/-- Equality reflection for infinity factorizations from equality of their
`π₀` shadows. -/
structure FrontierInfinityReflectionData
    (ML : LayerB.MotivicLocalization.{u, v}) where
  reflects_shadow_equality :
    ∀ {R : AdmissibleFrontierRealization ML}
      {F1 F2 : FrontierInfinityFactorization ML R},
      F1.toPiZeroFactorization = F2.toPiZeroFactorization → F1 = F2

namespace FrontierInfinityToPiZeroShadowContract

def ofLiftData
    {ML : LayerB.MotivicLocalization.{u, v}}
    (liftData : FrontierInfinityLiftData ML) :
    FrontierInfinityToPiZeroShadowContract ML where
  shadow := fun F => F.toPiZeroFactorization
  liftsPiZero := by
    intro R F
    exact ⟨⟨liftData.lift F, liftData.shadow_lift F⟩⟩

end FrontierInfinityToPiZeroShadowContract

namespace FrontierPiZeroFactorization

variable {ML : LayerB.MotivicLocalization.{u, v}}
variable {R : AdmissibleFrontierRealization ML}

/-- Any factorization determines its own realizable-image boundary inside the chosen target. -/
def realizableImage (F : FrontierPiZeroFactorization ML R) : LayerE.RealizableImage ML.Loc R.Tgt where
  sourceMap := F.realizeLocalizedObj
  IsRealizable := fun targetObj => Nonempty { sourceObj : ML.Loc // F.realizeLocalizedObj sourceObj = targetObj }
  realizable_iff := by
    intro targetObj
    rfl

end FrontierPiZeroFactorization

/-- `pi_0`-level contract form of the universal property: existence and uniqueness of
factorization for every admissible frontier realization datum after passing to the
homotopy category / triangulated shadow. -/
structure FrontierPiZeroInitialityContract (ML : LayerB.MotivicLocalization.{u, v}) where
  existsFactorization : forall R : AdmissibleFrontierRealization ML,
    Nonempty (FrontierPiZeroFactorization ML R)
  uniqueFactorization :
    forall (R : AdmissibleFrontierRealization ML)
      (F1 F2 : FrontierPiZeroFactorization ML R),
      F1 = F2

/-- Full stable `infty`-categorical contract form of the universal property.
This extends the `pi_0`-level contract rather than replacing it. -/
structure FrontierInfinityInitialityContract (ML : LayerB.MotivicLocalization.{u, v}) where
  piZero : FrontierPiZeroInitialityContract ML
  existsInfinityFactorization : forall R : AdmissibleFrontierRealization ML,
    Nonempty (FrontierInfinityFactorization ML R)
  uniqueInfinityFactorization :
    forall (R : AdmissibleFrontierRealization ML)
      (F1 F2 : FrontierInfinityFactorization ML R),
      F1 = F2

namespace FrontierPiZeroInitialityContract

variable {ML : LayerB.MotivicLocalization.{u, v}}

/-- Bundled statement used by downstream comparison layers when they only need the
existence/uniqueness form and not a concrete proof term. -/
def initialityStatement (_U : FrontierPiZeroInitialityContract ML) : Prop :=
  forall R : AdmissibleFrontierRealization ML,
    Nonempty (FrontierPiZeroFactorization ML R) /\
      forall F1 F2 : FrontierPiZeroFactorization ML R, F1 = F2

theorem initialityStatement_of_contract (U : FrontierPiZeroInitialityContract ML) :
    U.initialityStatement := by
  intro R
  refine ⟨U.existsFactorization R, ?_⟩
  intro F1 F2
  exact U.uniqueFactorization R F1 F2

end FrontierPiZeroInitialityContract

namespace FrontierInfinityInitialityContract

variable {ML : LayerB.MotivicLocalization.{u, v}}

/-- Bundled `infty`-level statement used when the comparison theorem genuinely needs the
higher coherent universal property, not just its `pi_0` shadow. -/
def initialityStatement (_U : FrontierInfinityInitialityContract ML) : Prop :=
  forall R : AdmissibleFrontierRealization ML,
    Nonempty (FrontierInfinityFactorization ML R) /\
      forall F1 F2 : FrontierInfinityFactorization ML R, F1 = F2

theorem initialityStatement_of_contract (U : FrontierInfinityInitialityContract ML) :
    U.initialityStatement := by
  intro R
  refine ⟨U.existsInfinityFactorization R, ?_⟩
  intro F1 F2
  exact U.uniqueInfinityFactorization R F1 F2

/-- The higher contract always exposes its underlying `pi_0` shadow. -/
theorem piZero_initialityStatement (U : FrontierInfinityInitialityContract ML) :
    U.piZero.initialityStatement :=
  FrontierPiZeroInitialityContract.initialityStatement_of_contract U.piZero

/-- Any `infty`-initiality contract yields `pi_0`-existence once an explicit shadow map is
supplied. -/
theorem shadow_factorization_exists
    (U : FrontierInfinityInitialityContract ML)
    (B : FrontierInfinityToPiZeroShadowContract ML)
    (R : AdmissibleFrontierRealization ML) :
    Nonempty (FrontierPiZeroFactorization ML R) := by
  rcases U.existsInfinityFactorization R with ⟨F⟩
  exact ⟨B.shadow F⟩

/-- `pi_0` initiality can be derived from `infty` initiality together with an explicit
shadow/lifting bridge. -/
def toPiZeroInitialityContract
    (U : FrontierInfinityInitialityContract ML)
    (B : FrontierInfinityToPiZeroShadowContract ML) :
    FrontierPiZeroInitialityContract ML where
  existsFactorization := shadow_factorization_exists U B
  uniqueFactorization := by
    intro R F1 F2
    rcases B.liftsPiZero F1 with ⟨⟨FInf1, h1⟩⟩
    rcases B.liftsPiZero F2 with ⟨⟨FInf2, h2⟩⟩
    have hInf : FInf1 = FInf2 := U.uniqueInfinityFactorization R FInf1 FInf2
    calc
      F1 = B.shadow FInf1 := by simp [h1]
      _ = B.shadow FInf2 := by simp [hInf]
      _ = F2 := by simp [h2]

theorem piZero_initiality_of_infinity_shadow
    (U : FrontierInfinityInitialityContract ML)
    (B : FrontierInfinityToPiZeroShadowContract ML) :
    (U.toPiZeroInitialityContract B).initialityStatement :=
  FrontierPiZeroInitialityContract.initialityStatement_of_contract _

/-- Upgrade a `π₀`-initiality contract to an infinity-initiality contract once
the codebase supplies chosen infinity lifts of all `π₀` factorizations and a
reflection principle showing that equality of `π₀` shadows determines equality
of the lifted infinity factorizations. -/
def ofPiZeroInitialityAndLifts
    (U : FrontierPiZeroInitialityContract ML)
    (liftData : FrontierInfinityLiftData ML)
    (reflection : FrontierInfinityReflectionData ML) :
    FrontierInfinityInitialityContract ML where
  piZero := U
  existsInfinityFactorization := by
    intro R
    rcases U.existsFactorization R with ⟨F⟩
    exact ⟨liftData.lift F⟩
  uniqueInfinityFactorization := by
    intro R F1 F2
    apply reflection.reflects_shadow_equality
    exact U.uniqueFactorization R F1.toPiZeroFactorization F2.toPiZeroFactorization

theorem ofPiZeroInitialityAndLifts_piZero
    (U : FrontierPiZeroInitialityContract ML)
    (liftData : FrontierInfinityLiftData ML)
    (reflection : FrontierInfinityReflectionData ML) :
    (ofPiZeroInitialityAndLifts U liftData reflection).piZero = U :=
  rfl

def infinity_initiality_exposes_piZero_shadow
  (_U : FrontierInfinityInitialityContract ML)
    (B : FrontierInfinityToPiZeroShadowContract ML)
    (R : AdmissibleFrontierRealization ML)
    (F : FrontierInfinityFactorization ML R) :
    FrontierPiZeroFactorization.RecordedRealizationStructure (B.shadow F) :=
  FrontierPiZeroFactorization.recordsRealizationStructure _

end FrontierInfinityInitialityContract

/-- Manuscript-facing alias for the `pi_0` universal-property surface. -/
theorem theorem_frontier_pi0_universal_property_surface
    {ML : LayerB.MotivicLocalization.{u, v}}
    (U : FrontierPiZeroInitialityContract ML) :
    U.initialityStatement :=
  FrontierPiZeroInitialityContract.initialityStatement_of_contract U

/-- Manuscript-facing alias for the stable `infty` universal-property surface. -/
theorem theorem_frontier_infinity_universal_property_surface
    {ML : LayerB.MotivicLocalization.{u, v}}
    (U : FrontierInfinityInitialityContract ML) :
    U.initialityStatement :=
  FrontierInfinityInitialityContract.initialityStatement_of_contract U

theorem theorem_frontier_pi0_shadow_of_infinity_surface
    {ML : LayerB.MotivicLocalization.{u, v}}
    (U : FrontierInfinityInitialityContract ML)
    (B : FrontierInfinityToPiZeroShadowContract ML) :
    (U.toPiZeroInitialityContract B).initialityStatement :=
  FrontierInfinityInitialityContract.piZero_initiality_of_infinity_shadow U B

/-- Comparison-ready package: a source localization together with the two theorem-sized
universal-property contracts that any later motivic comparison theorem must consume. -/
structure UniversalFrontierSemantics where
  ML : LayerB.MotivicLocalization.{u, v}
  piZeroContract : FrontierPiZeroInitialityContract ML
  infinityContract : FrontierInfinityInitialityContract ML
  targetPiZeroUniversalCharacterization : Prop
  targetInfinityUniversalCharacterization : Prop

namespace UniversalFrontierSemantics

/-- The homotopy-category / triangulated comparison layer is ready only after the source
and target `pi_0` universal-property statements are both available. -/
def piZeroComparisonReady (U : UniversalFrontierSemantics.{u, v}) : Prop :=
  U.piZeroContract.initialityStatement /\ U.targetPiZeroUniversalCharacterization

/-- The full stable `infty`-comparison layer is ready only after the higher coherent
source and target universal-property statements are both available. -/
def infinityComparisonReady (U : UniversalFrontierSemantics.{u, v}) : Prop :=
  U.infinityContract.initialityStatement /\ U.targetInfinityUniversalCharacterization

/-- The full comparison package exposes both readiness levels explicitly. -/
def comparisonReady (U : UniversalFrontierSemantics.{u, v}) : Prop :=
  U.piZeroComparisonReady /\ U.infinityComparisonReady

end UniversalFrontierSemantics

end LayerD
end TraceCalc