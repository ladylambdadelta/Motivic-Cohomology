import TraceCalc.LayerE.MotivicRecognition.HomPacketDecomposition

universe u v w x y z

namespace TraceCalc
namespace MotivicRecognition

set_option maxHeartbeats 3000000

/-!
# Campaign 12 taxonomy targets

Campaign 12 is now split internally as follows:

* 12A: triangulated/stable motivic recognition at the pinned `DM_gm(Q)_Q` layer;
* 12B: normalization-induced motivic `t`-structure on the recognized category;
* 12C: heart construction `MM(Q)` as the heart of that `t`-structure;
* 12D: heart recognition and mixed-motive comparison packaging.

Campaign 11 weight devissage remains an input to 12B. It is not itself the
motivic `t`-structure theorem.
-/

/-- Proof-relevant ambient triangulated/stable interface used by the Campaign
12 t-structure construction.  This is intentionally object-and-morphism level:
later t-structure axioms can mention the shift, the connecting morphism, and
distinguished triangles directly instead of referring to a theorem-name slot. -/
structure TraceMotivicAmbientTriangulatedData
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}) where
  shiftObject :
    structuralRecognition.recognition.recognizedCategory.Object →
      structuralRecognition.recognition.recognizedCategory.Object
  distinguishedTriangle :
    {X Y Z : structuralRecognition.recognition.recognizedCategory.Object} →
      structuralRecognition.recognition.recognizedCategory.Hom X Y →
      structuralRecognition.recognition.recognizedCategory.Hom Y Z →
      structuralRecognition.recognition.recognizedCategory.Hom Z (shiftObject X) → Prop
  shiftFunctoriality : structuralRecognition.structuralPackage.triangulated.shiftFunctorTarget
  distinguishedTrianglesSound :
    structuralRecognition.structuralPackage.triangulated.distinguishedTrianglesTarget

/-- Proof-relevant truncation triangle for the indexed t-structure halves.
For an object `X` and index `n`, this is the data of
`tau_le n X -> X -> tau_ge (n+1) X -> (tau_le n X)[1]`, its distinguished
triangle certificate, and membership witnesses for the two truncation objects. -/
structure TraceMotivicTruncationTriangleData
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z})
    (ambient : TraceMotivicAmbientTriangulatedData structuralRecognition)
    (isNonpos isNonneg : Int → structuralRecognition.recognition.recognizedCategory.Object → Type z)
    (n : Int)
    (X : structuralRecognition.recognition.recognizedCategory.Object) where
  left : structuralRecognition.recognition.recognizedCategory.Object
  right : structuralRecognition.recognition.recognizedCategory.Object
  inclusion : structuralRecognition.recognition.recognizedCategory.Hom left X
  projection : structuralRecognition.recognition.recognizedCategory.Hom X right
  connecting : structuralRecognition.recognition.recognizedCategory.Hom right (ambient.shiftObject left)
  triangle : ambient.distinguishedTriangle inclusion projection connecting
  left_nonpos : isNonpos n left
  right_nonneg : isNonneg (n + 1) right

/-- Concrete degree bounds for an object in the normalization packet model.
This is the boundedness datum that later feeds the t-structure axiom: the
object has a finite lower and upper amplitude, together with the corresponding
indexed membership witnesses. -/
structure TraceMotivicPacketAmplitudeBound
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z})
    (isNonpos isNonneg : Int → structuralRecognition.recognition.recognizedCategory.Object → Type z)
    (X : structuralRecognition.recognition.recognizedCategory.Object) where
  lowerBound : Int
  upperBound : Int
  lowerMembership : isNonneg lowerBound X
  upperMembership : isNonpos upperBound X

/-- Explicit packet-degree refinement data. This replaces a bare theorem flag by
an actual refined packet index, the map back to packets, its degree function,
and the compatibility/surjectivity data relating the refinement to the exposed
packet grading. -/
structure PacketDegreeRefinementData
    {Obj : Type u}
    (packetRecord : Obj → Type z)
    (packetDegree : (X : Obj) → packetRecord X → Int) where
  RefinedPacketIndex : Obj → Type z
  refinedToPacket : ∀ X, RefinedPacketIndex X → packetRecord X
  refinedDegree : ∀ X, RefinedPacketIndex X → Int
  degree_compatible :
    ∀ X i,
      packetDegree X (refinedToPacket X i) = refinedDegree X i
  packet_covered :
    ∀ X p, {i : RefinedPacketIndex X // refinedToPacket X i = p}

/-- Explicit adjacent-degree packet shift data. The packet cut layer does not
yet identify a global triangulated shift object, but it can still expose the
local packet-degree step relation that a later compatibility theorem must tie
to the ambient shift. -/
structure PacketDegreeShiftData
    {Obj : Type u}
    (packetRecord : Obj → Type z)
    (packetDegree : (X : Obj) → packetRecord X → Int) where
  ShiftStep : ∀ X, packetRecord X → packetRecord X → Type z
  shift_degree :
    ∀ X p q,
      ShiftStep X p q → packetDegree X q = packetDegree X p + 1

structure NatStepWitness (sourceDegree targetDegree : Nat) : Type z where
  eq_succ : targetDegree = sourceDegree + 1

structure NatLeWitness (lower upper : Nat) : Type z where
  le_proof : lower ≤ upper

structure NatLtWitness (lower upper : Nat) : Type z where
  lt_proof : lower < upper

/-- Explicit finite degree-amplitude data for packet degrees. -/
structure FinitePacketAmplitudeData
    {Obj : Type u}
    (packetRecord : Obj → Type z)
    (packetDegree : (X : Obj) → packetRecord X → Int) where
  lowerBound : Obj → Int
  upperBound : Obj → Int
  lower_bound : ∀ X p, lowerBound X ≤ packetDegree X p
  upper_bound : ∀ X p, packetDegree X p ≤ upperBound X

/-- Explicit finite packet DAG data. This records a concrete edge relation,
monotonicity of degrees along edges, and an actual finite indexing family that
covers all exposed packets. -/
structure FiniteDegreeLabeledPacketDAGData
    {Obj : Type u}
    (packetRecord : Obj → Type z)
    (packetDegree : (X : Obj) → packetRecord X → Int) where
  Edge : ∀ X, packetRecord X → packetRecord X → Type z
  edge_degree_mono :
    ∀ X p q,
      Edge X p q → packetDegree X p ≤ packetDegree X q
  finitePacketIndex : Obj → Type z
  finitePacketIndexToPacket : ∀ X, finitePacketIndex X → packetRecord X
  packetCovered :
    ∀ X p, {i : finitePacketIndex X // finitePacketIndexToPacket X i = p}

structure CanonicalThresholdCutData
    {Obj : Type u}
    (packetRecord : Obj → Type z)
    (packetDegree : (X : Obj) → packetRecord X → Int)
    (lowerCutRecord : (X : Obj) → packetRecord X → Type z)
    (upperCutRecord : (X : Obj) → packetRecord X → Type z) where
  cutoff : Int
  lower_of_degree_lt :
    ∀ {X} (packet : packetRecord X),
      packetDegree X packet < cutoff → lowerCutRecord X packet
  lower_degree_bound :
    ∀ {X} (packet : packetRecord X),
      lowerCutRecord X packet → packetDegree X packet < cutoff
  upper_of_cutoff_le :
    ∀ {X} (packet : packetRecord X),
      cutoff ≤ packetDegree X packet → upperCutRecord X packet
  upper_cutoff_bound :
    ∀ {X} (packet : packetRecord X),
      upperCutRecord X packet → cutoff ≤ packetDegree X packet

structure BoundaryDependencyClosureData
    {Obj : Type u}
    (packetRecord : Obj → Type z)
    (lowerCutRecord : (X : Obj) → packetRecord X → Type z) where
  dependencyEdge : ∀ X, packetRecord X → packetRecord X → Type z
  lower_closed_under_dependencies :
    ∀ {X} (sourcePacket targetPacket : packetRecord X),
      dependencyEdge X sourcePacket targetPacket →
        lowerCutRecord X targetPacket → lowerCutRecord X sourcePacket

structure LowerCutAdmissibilityData
    {Obj : Type u}
    (packetRecord : Obj → Type z)
    (packetDegree : (X : Obj) → packetRecord X → Int)
    (lowerCutRecord : (X : Obj) → packetRecord X → Type z) where
  cutoff : Int
  lower_cut_degree :
    ∀ {X} (packet : packetRecord X),
      lowerCutRecord X packet → packetDegree X packet < cutoff

structure UpperCutAdmissibilityData
    {Obj : Type u}
    (packetRecord : Obj → Type z)
    (packetDegree : (X : Obj) → packetRecord X → Int)
    (lowerCutRecord : (X : Obj) → packetRecord X → Type z)
    (upperCutRecord : (X : Obj) → packetRecord X → Type z) where
  cutoff : Int
  upper_cut_degree :
    ∀ {X} (packet : packetRecord X),
      upperCutRecord X packet → cutoff ≤ packetDegree X packet
  cut_partition :
    ∀ {X} (packet : packetRecord X),
      Sum (lowerCutRecord X packet) (upperCutRecord X packet)
  cut_disjoint :
    ∀ {X} (packet : packetRecord X),
      lowerCutRecord X packet → upperCutRecord X packet → False

structure GluingClosureData
    {Obj : Type u}
    (packetRecord : Obj → Type z)
    (upperCutRecord : (X : Obj) → packetRecord X → Type z) where
  gluePacket :
    ∀ {X} (packet : packetRecord X),
      upperCutRecord X packet → packetRecord X
  glue_preserves_upper :
    ∀ {X} (packet : packetRecord X) (hUpper : upperCutRecord X packet),
      upperCutRecord X (gluePacket packet hUpper)

structure CanonicalReconstructionCompatibilityData
    {Obj : Type u}
    (packetRecord : Obj → Type z)
    (packetDegree : (X : Obj) → packetRecord X → Int) where
  reconstructPacket : ∀ {X}, packetRecord X → packetRecord X
  reconstruction_preserves_degree :
    ∀ {X} (packet : packetRecord X),
      packetDegree X (reconstructPacket packet) = packetDegree X packet

structure Campaign11WeightDevissageCompatibilityData
    {Obj : Type u}
    (packetRecord : Obj → Type z)
    (packetDegree : (X : Obj) → packetRecord X → Int) where
  weightIndex : ∀ {X}, packetRecord X → Int
  weight_matches_packet_degree :
    ∀ {X} (packet : packetRecord X),
      weightIndex packet = packetDegree X packet

/-- Actual Campaign 12B t-structure recognition theorem on the recognized trace
motivic category.  The two halves are indexed predicates, and the axioms are
stated directly: shift behavior, orthogonality as vanishing of every relevant
morphism, truncation triangles as proof-relevant data, boundedness, and
compatibility with the recognition/motivic comparison layer. -/
structure TraceMotivicTStructure
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}) where
  ambient : TraceMotivicAmbientTriangulatedData structuralRecognition
  isNonpos : Int → structuralRecognition.recognition.recognizedCategory.Object → Type z
  isNonneg : Int → structuralRecognition.recognition.recognizedCategory.Object → Type z
  shift_nonpos :
    ∀ (n : Int) (X : structuralRecognition.recognition.recognizedCategory.Object),
      isNonpos n X → isNonpos (n + 1) (ambient.shiftObject X)
  shift_nonneg :
    ∀ (n : Int) (X : structuralRecognition.recognition.recognizedCategory.Object),
      isNonneg n X → isNonneg (n + 1) (ambient.shiftObject X)
  orthogonality :
    ∀ (X Y : structuralRecognition.recognition.recognizedCategory.Object),
      isNonpos 0 X → isNonneg 1 Y →
        (f : structuralRecognition.recognition.recognizedCategory.Hom X Y) →
          TraceMotivicZeroMorphismWitness structuralRecognition f
  truncationTriangle :
    ∀ (n : Int) (X : structuralRecognition.recognition.recognizedCategory.Object),
      TraceMotivicTruncationTriangleData structuralRecognition ambient isNonpos isNonneg n X
  bounded :
    ∀ X : structuralRecognition.recognition.recognizedCategory.Object,
      TraceMotivicPacketAmplitudeBound structuralRecognition isNonpos isNonneg X
  recognition_nonpos_compatibility :
    ∀ (n : Int) (X : structuralRecognition.recognition.recognizedCategory.Object),
      isNonpos n X → Prop
  recognition_nonneg_compatibility :
    ∀ (n : Int) (X : structuralRecognition.recognition.recognizedCategory.Object),
      isNonneg n X → Prop
  recognition_truncation_compatibility :
    ∀ (n : Int) (X : structuralRecognition.recognition.recognizedCategory.Object),
      TraceMotivicTruncationTriangleData structuralRecognition ambient isNonpos isNonneg n X → Prop

/-!
Audit of the Campaign 12B t-structure spine:

* `ambient.shiftObject` is genuine missing data: it must be constructed from
  the recognized DM_gm triangulated shift, not by identity shift.
* `ambient.distinguishedTriangle` is a real predicate on three recognized
  morphisms; its soundness is tied to the structural triangulated package.
* `isNonpos` and `isNonneg` are normalization-packet indexed halves, supplied
  below by `normalizationPacketNonposAt` and `normalizationPacketNonnegAt`;
  their membership includes packet-degree inequalities against the index.
  The canonical constructor now exposes a concrete `Fin reconstructionLength`
  packet index and records its relation to the public packet grading in
  `packetDegreeRefinement`.
* `orthogonality` is a genuine separated-degree theorem frontier: it must show
  each recognized morphism in the forbidden range is zero, using trace-native
  separated-degree orthogonality.
* `truncationTriangle` is proof-relevant data: lower/right objects and the three
  morphisms must come from the canonical packet cut plus cofiber machinery.
* `bounded` is finite packet-amplitude data, not a fixed bound or `Nonempty`.
* recognition compatibility fields are the DM_gm(Q)_Q transport theorem
  frontiers for the two halves and the truncation triangle construction.
-/

/-- Theorem target for a weight-structure package on the structurally-recognized
motivic category.

Campaign 11 trace-native weight orthogonality feeds this only as a later
consumer; it is not itself the motivic t-structure theorem. -/
structure WeightStructureTarget
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}) where
  certifiedWeightDevissage : CertifiedWeightDevissageData structuralRecognition
  weightClassNonpositive :
    structuralRecognition.recognition.recognizedCategory.Object → Type z
  weightClassNonnegative :
    structuralRecognition.recognition.recognizedCategory.Object → Type z
  separatedWeightRelation :
    structuralRecognition.recognition.recognizedCategory.Object →
      structuralRecognition.recognition.recognizedCategory.Object → Type z
  orthogonalityTarget : certifiedWeightDevissage.weightOrthogonalityTarget
  proofRelevantOrthogonalityTarget :
    ∀ {sourceObj targetObj : structuralRecognition.recognition.recognizedCategory.Object}
      (separated : separatedWeightRelation sourceObj targetObj)
      (f : structuralRecognition.recognition.recognizedCategory.Hom sourceObj targetObj),
      Prop
  weightDecompositionTarget : certifiedWeightDevissage.boundedWeightDecompositionTarget

namespace WeightStructureTarget

def ofCertifiedWeightDevissage
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (certifiedWeightDevissage : CertifiedWeightDevissageData structuralRecognition) :
    WeightStructureTarget structuralRecognition where
  certifiedWeightDevissage := certifiedWeightDevissage
  weightClassNonpositive := certifiedWeightDevissage.weightClassNonpositive
  weightClassNonnegative := certifiedWeightDevissage.weightClassNonnegative
  separatedWeightRelation := certifiedWeightDevissage.separatedWeightRelation
  orthogonalityTarget := certifiedWeightDevissage.weightOrthogonality_holds
  proofRelevantOrthogonalityTarget := fun {sourceObj targetObj} separated f =>
    certifiedWeightDevissage.proofRelevantWeightOrthogonalityTarget separated f
  weightDecompositionTarget := certifiedWeightDevissage.boundedWeightDecomposition_holds

end WeightStructureTarget



/-- Campaign 12B sublemma target: canonical normalization yields a finite
degree-labeled packet decomposition together with an admissible threshold cut.

This packages the precise bridge from Campaign 11 normalized packet data to the
later truncation triangle. It does not yet assert the full `t`-structure. -/
structure NormalizationPacketCutData
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}) where
  packetRecord :
    structuralRecognition.recognition.recognizedCategory.Object → Type z
  packetDegree :
    (X : structuralRecognition.recognition.recognizedCategory.Object) →
      packetRecord X → Int
  PacketHom :
    {X Y : structuralRecognition.recognition.recognizedCategory.Object} →
      packetRecord X → packetRecord Y → Type z
  packetHomUnderlying :
    {X Y : structuralRecognition.recognition.recognizedCategory.Object} →
      {sourcePacket : packetRecord X} → {targetPacket : packetRecord Y} →
        PacketHom sourcePacket targetPacket →
          structuralRecognition.recognition.recognizedCategory.Hom X Y
  IsZeroPacketHom :
    {X Y : structuralRecognition.recognition.recognizedCategory.Object} →
      {sourcePacket : packetRecord X} → {targetPacket : packetRecord Y} →
        PacketHom sourcePacket targetPacket → Prop
  packetZeroTransports :
    {X Y : structuralRecognition.recognition.recognizedCategory.Object} →
      {sourcePacket : packetRecord X} → {targetPacket : packetRecord Y} →
        (packetHom : PacketHom sourcePacket targetPacket) →
          IsZeroPacketHom packetHom →
            TraceMotivicZeroMorphismWitness structuralRecognition
              (packetHomUnderlying packetHom)
  packetDegreeRefinement :
    PacketDegreeRefinementData packetRecord packetDegree
  packetDegreeShift :
    PacketDegreeShiftData packetRecord packetDegree
  finitePacketAmplitude :
    FinitePacketAmplitudeData packetRecord packetDegree
  lowerCutRecord :
    (X : structuralRecognition.recognition.recognizedCategory.Object) →
      packetRecord X → Type z
  upperCutRecord :
    (X : structuralRecognition.recognition.recognizedCategory.Object) →
      packetRecord X → Type z
  finiteDegreeLabeledPacketDAG :
    FiniteDegreeLabeledPacketDAGData packetRecord packetDegree
  separatedDegreePacketVanishing :
    ∀ {X Y : structuralRecognition.recognition.recognizedCategory.Object}
      {sourcePacket : packetRecord X} {targetPacket : packetRecord Y}
      (packetHom : PacketHom sourcePacket targetPacket) (n : Int),
        packetDegree X sourcePacket ≤ n →
        n < packetDegree Y targetPacket →
        IsZeroPacketHom packetHom
  recognizedHomPacketComponent :
    ∀ {X Y : structuralRecognition.recognition.recognizedCategory.Object}
      (sourcePacket : packetRecord X) (targetPacket : packetRecord Y)
      (f : structuralRecognition.recognition.recognizedCategory.Hom X Y),
        PacketHom sourcePacket targetPacket
  /-- Detector/conservativity frontier for packet components. This is not an
  additive Hom decomposition theorem and does not assert that a global morphism
  is a single packet morphism. It says the selected packet/component shadow is
  jointly conservative enough for the zero test needed by t-structure
  orthogonality. -/
  packetComponentsDetectZero :
    ∀ {X Y : structuralRecognition.recognition.recognizedCategory.Object}
      (f : structuralRecognition.recognition.recognizedCategory.Hom X Y)
      (sourceSupports : packetRecord X → Prop)
      (targetSupports : packetRecord Y → Prop)
      (sourceSupportWitness : {sourcePacket : packetRecord X //
        sourceSupports sourcePacket})
      (targetSupportWitness : {targetPacket : packetRecord Y //
        targetSupports targetPacket}),
        (∀ sourcePacket : packetRecord X,
            ∀ targetPacket : packetRecord Y,
              sourceSupports sourcePacket →
              targetSupports targetPacket →
              IsZeroPacketHom (recognizedHomPacketComponent sourcePacket targetPacket f)) →
          TraceMotivicZeroMorphismWitness structuralRecognition f
  canonicalThresholdCut :
    CanonicalThresholdCutData packetRecord packetDegree lowerCutRecord upperCutRecord
  lowerCutAdmissibility :
    LowerCutAdmissibilityData packetRecord packetDegree lowerCutRecord
  upperCutAdmissibility :
    UpperCutAdmissibilityData packetRecord packetDegree lowerCutRecord upperCutRecord
  boundaryDependencyClosure :
    BoundaryDependencyClosureData packetRecord lowerCutRecord
  gluingClosure :
    GluingClosureData packetRecord upperCutRecord
  canonicalReconstructionCompatibility :
    CanonicalReconstructionCompatibilityData packetRecord packetDegree
  campaign11WeightDevissageCompatibility :
    Campaign11WeightDevissageCompatibilityData packetRecord packetDegree

namespace NormalizationPacketCutData

/-- Lower-half monotonicity is the order-theoretic part of the packet-degree
definition: once a packet has degree at most `n`, it has degree at most any
larger cutoff `m`. -/
theorem packet_nonpos_mono
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (packetCut : NormalizationPacketCutData structuralRecognition)
    {X : structuralRecognition.recognition.recognizedCategory.Object}
    {packet : packetCut.packetRecord X}
    {n m : Int}
    (hDegree : packetCut.packetDegree X packet ≤ n)
    (hCutoff : n ≤ m) :
    packetCut.packetDegree X packet ≤ m :=
  le_trans hDegree hCutoff

/-- Upper-half monotonicity is the dual order-theoretic part of the packet-degree
definition: if a packet lies above `n`, then it lies above any smaller cutoff
`m`. -/
theorem packet_nonneg_mono
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (packetCut : NormalizationPacketCutData structuralRecognition)
    {X : structuralRecognition.recognition.recognizedCategory.Object}
    {packet : packetCut.packetRecord X}
    {n m : Int}
    (hDegree : n ≤ packetCut.packetDegree X packet)
    (hCutoff : m ≤ n) :
    m ≤ packetCut.packetDegree X packet :=
  le_trans hCutoff hDegree

/-- Frontier statement for the real packet-graded shift theorem. The current
normalization package does not yet expose a concrete shifted packet operation,
so the theorem is carried as the exact obligation that such an operation should
raise packet degree by one. -/
def packetDegreeShiftStatement
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (packetCut : NormalizationPacketCutData structuralRecognition) : Prop :=
  ∀ X p q,
    packetCut.packetDegreeShift.ShiftStep X p q →
      packetCut.packetDegree X q = packetCut.packetDegree X p + 1

theorem packetDegreeShiftStatement_holds
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (packetCut : NormalizationPacketCutData structuralRecognition) :
    packetDegreeShiftStatement packetCut :=
  packetCut.packetDegreeShift.shift_degree

/-- Frontier statement for finite packet support/amplitude. A future proof should
extract these bounds from the finite degree-labeled packet DAG, not from a fixed
zero or threshold-only model. -/
def finite_packet_amplitude
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (packetCut : NormalizationPacketCutData structuralRecognition) : Prop :=
  ∀ X : structuralRecognition.recognition.recognizedCategory.Object,
    ∃ lower upper : Int,
      (∀ packet : packetCut.packetRecord X, lower ≤ packetCut.packetDegree X packet) ∧
        (∀ packet : packetCut.packetRecord X, packetCut.packetDegree X packet ≤ upper)

theorem finite_packet_amplitude_holds
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (packetCut : NormalizationPacketCutData structuralRecognition) :
    finite_packet_amplitude packetCut := by
  intro X
  exact ⟨packetCut.finitePacketAmplitude.lowerBound X,
    packetCut.finitePacketAmplitude.upperBound X,
    packetCut.finitePacketAmplitude.lower_bound X,
    packetCut.finitePacketAmplitude.upper_bound X⟩

def canonical_threshold_cut_statement
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (packetCut : NormalizationPacketCutData structuralRecognition) : Prop :=
  (∀ {X} (packet : packetCut.packetRecord X),
      packetCut.packetDegree X packet < packetCut.canonicalThresholdCut.cutoff →
        ∃ lowerWitness : packetCut.lowerCutRecord X packet,
          packetCut.packetDegree X packet < packetCut.canonicalThresholdCut.cutoff) ∧
    (∀ {X} (packet : packetCut.packetRecord X),
      packetCut.lowerCutRecord X packet →
        packetCut.packetDegree X packet < packetCut.canonicalThresholdCut.cutoff) ∧
    (∀ {X} (packet : packetCut.packetRecord X),
      packetCut.canonicalThresholdCut.cutoff ≤ packetCut.packetDegree X packet →
        ∃ upperWitness : packetCut.upperCutRecord X packet,
          packetCut.canonicalThresholdCut.cutoff ≤ packetCut.packetDegree X packet) ∧
    (∀ {X} (packet : packetCut.packetRecord X),
      packetCut.upperCutRecord X packet →
        packetCut.canonicalThresholdCut.cutoff ≤ packetCut.packetDegree X packet)

theorem canonical_threshold_cut_statement_holds
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (packetCut : NormalizationPacketCutData structuralRecognition) :
    canonical_threshold_cut_statement packetCut := by
  refine ⟨?_, packetCut.canonicalThresholdCut.lower_degree_bound, ?_, packetCut.canonicalThresholdCut.upper_cutoff_bound⟩
  · intro X packet hPacket
    exact ⟨packetCut.canonicalThresholdCut.lower_of_degree_lt packet hPacket, hPacket⟩
  · intro X packet hPacket
    exact ⟨packetCut.canonicalThresholdCut.upper_of_cutoff_le packet hPacket, hPacket⟩

def lower_cut_admissibility_statement
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (packetCut : NormalizationPacketCutData structuralRecognition) : Prop :=
  ∀ {X} (packet : packetCut.packetRecord X),
    packetCut.lowerCutRecord X packet →
      packetCut.packetDegree X packet < packetCut.lowerCutAdmissibility.cutoff

theorem lower_cut_admissibility_statement_holds
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (packetCut : NormalizationPacketCutData structuralRecognition) :
    lower_cut_admissibility_statement packetCut := by
  exact packetCut.lowerCutAdmissibility.lower_cut_degree

def upper_cut_admissibility_statement
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (packetCut : NormalizationPacketCutData structuralRecognition) : Prop :=
  (∀ {X} (packet : packetCut.packetRecord X),
      packetCut.upperCutRecord X packet →
        packetCut.upperCutAdmissibility.cutoff ≤ packetCut.packetDegree X packet) ∧
    (∀ {X} (packet : packetCut.packetRecord X),
      (∃ lowerWitness : packetCut.lowerCutRecord X packet,
          packetCut.packetDegree X packet < packetCut.lowerCutAdmissibility.cutoff) ∨
        (∃ upperWitness : packetCut.upperCutRecord X packet,
          packetCut.upperCutAdmissibility.cutoff ≤ packetCut.packetDegree X packet)) ∧
    (∀ {X} (packet : packetCut.packetRecord X),
      packetCut.lowerCutRecord X packet → packetCut.upperCutRecord X packet → False)

theorem upper_cut_admissibility_statement_holds
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (packetCut : NormalizationPacketCutData structuralRecognition) :
    upper_cut_admissibility_statement packetCut := by
  refine ⟨packetCut.upperCutAdmissibility.upper_cut_degree, ?_, packetCut.upperCutAdmissibility.cut_disjoint⟩
  intro X packet
  cases packetCut.upperCutAdmissibility.cut_partition (X := X) packet with
    | inl lowerWitness =>
      exact Or.inl ⟨lowerWitness, packetCut.lowerCutAdmissibility.lower_cut_degree (X := X) packet lowerWitness⟩
    | inr upperWitness =>
      exact Or.inr ⟨upperWitness, packetCut.upperCutAdmissibility.upper_cut_degree (X := X) packet upperWitness⟩

def boundary_dependency_closure_statement
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (packetCut : NormalizationPacketCutData structuralRecognition) : Prop :=
  ∀ {X} (sourcePacket targetPacket : packetCut.packetRecord X),
    packetCut.boundaryDependencyClosure.dependencyEdge X sourcePacket targetPacket →
      ∀ targetWitness : packetCut.lowerCutRecord X targetPacket,
        ∃ sourceWitness : packetCut.lowerCutRecord X sourcePacket,
          packetCut.packetDegree X sourcePacket < packetCut.lowerCutAdmissibility.cutoff

theorem boundary_dependency_closure_statement_holds
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (packetCut : NormalizationPacketCutData structuralRecognition) :
    boundary_dependency_closure_statement packetCut := by
  intro X sourcePacket targetPacket hEdge targetWitness
  let sourceWitness :=
    packetCut.boundaryDependencyClosure.lower_closed_under_dependencies
      sourcePacket targetPacket hEdge targetWitness
  exact ⟨sourceWitness, packetCut.lowerCutAdmissibility.lower_cut_degree sourcePacket sourceWitness⟩

def gluing_closure_statement
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (packetCut : NormalizationPacketCutData structuralRecognition) : Prop :=
  ∀ {X} (packet : packetCut.packetRecord X)
    (hUpper : packetCut.upperCutRecord X packet),
    ∃ gluedUpper : packetCut.upperCutRecord X (packetCut.gluingClosure.gluePacket packet hUpper),
      packetCut.upperCutAdmissibility.cutoff ≤
        packetCut.packetDegree X (packetCut.gluingClosure.gluePacket packet hUpper)

theorem gluing_closure_statement_holds
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (packetCut : NormalizationPacketCutData structuralRecognition) :
    gluing_closure_statement packetCut := by
  intro X packet hUpper
  let gluedUpper := packetCut.gluingClosure.glue_preserves_upper packet hUpper
  exact ⟨gluedUpper, packetCut.upperCutAdmissibility.upper_cut_degree _ gluedUpper⟩

def canonical_reconstruction_compatibility_statement
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (packetCut : NormalizationPacketCutData structuralRecognition) : Prop :=
  ∀ {X} (packet : packetCut.packetRecord X),
    packetCut.packetDegree X
        (packetCut.canonicalReconstructionCompatibility.reconstructPacket packet) =
      packetCut.packetDegree X packet

theorem canonical_reconstruction_compatibility_statement_holds
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (packetCut : NormalizationPacketCutData structuralRecognition) :
    canonical_reconstruction_compatibility_statement packetCut := by
  intro X packet
  exact packetCut.canonicalReconstructionCompatibility.reconstruction_preserves_degree packet

def campaign11_weight_devissage_compatibility_statement
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (packetCut : NormalizationPacketCutData structuralRecognition) : Prop :=
  ∀ {X} (packet : packetCut.packetRecord X),
    packetCut.campaign11WeightDevissageCompatibility.weightIndex packet =
      packetCut.packetDegree X packet

theorem campaign11_weight_devissage_compatibility_statement_holds
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (packetCut : NormalizationPacketCutData structuralRecognition) :
    campaign11_weight_devissage_compatibility_statement packetCut := by
  intro X packet
  exact packetCut.campaign11WeightDevissageCompatibility.weight_matches_packet_degree packet

/-- Separated-degree orthogonality at the packet level. Every packet morphism
from degree at most `n` to degree greater than `n` is zero. -/
def packet_degree_orthogonality
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (packetCut : NormalizationPacketCutData structuralRecognition) : Prop :=
  ∀ (source target : structuralRecognition.recognition.recognizedCategory.Object)
    (sourcePacket : packetCut.packetRecord source)
    (targetPacket : packetCut.packetRecord target)
    (packetHom : packetCut.PacketHom sourcePacket targetPacket) (n : Int),
      packetCut.packetDegree source sourcePacket ≤ n →
      n < packetCut.packetDegree target targetPacket →
      packetCut.IsZeroPacketHom packetHom

theorem packet_degree_orthogonality_holds
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (packetCut : NormalizationPacketCutData structuralRecognition) :
    packet_degree_orthogonality packetCut := by
  intro source target sourcePacket targetPacket packetHom n hSource hTarget
  exact packetCut.separatedDegreePacketVanishing packetHom n hSource hTarget

end NormalizationPacketCutData

def NormalizationPacketCutData.toHomPacketComponentData
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (packetCut : NormalizationPacketCutData structuralRecognition) :
    TraceMotivicHomPacketComponentData structuralRecognition where
  PacketRecord := packetCut.packetRecord
  packetDegree := packetCut.packetDegree
  PacketHom := packetCut.PacketHom
  packetComponent := fun sourcePacket targetPacket f =>
    packetCut.recognizedHomPacketComponent sourcePacket targetPacket f
  packetZero := fun packetHom => packetCut.IsZeroPacketHom packetHom

def NormalizationPacketCutData.toHomPacketExtensionality
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (packetCut : NormalizationPacketCutData structuralRecognition) :
    TraceMotivicHomPacketExtensionality structuralRecognition
      packetCut.toHomPacketComponentData where
  hom_zero_of_packet_family_vanishing := by
    intro X Y f sourceSupports targetSupports sourceSupportWitness targetSupportWitness hPacketVanishing
    exact
      packetCut.packetComponentsDetectZero
        f sourceSupports targetSupports sourceSupportWitness targetSupportWitness hPacketVanishing

def NormalizationPacketCutData.toHomPacketSeparatedVanishing
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (packetCut : NormalizationPacketCutData structuralRecognition) :
    TraceMotivicHomPacketSeparatedVanishing structuralRecognition
      packetCut.toHomPacketComponentData where
  packet_vanishes_of_separated_degrees := by
    intro X Y f n sourcePacket targetPacket hSource hTarget
    exact
      packetCut.separatedDegreePacketVanishing
        (packetCut.recognizedHomPacketComponent sourcePacket targetPacket f)
        n hSource hTarget

/-- Campaign 12B key sublemma target: the canonical normalized lower cut gives
the truncation triangle, and the complementary cofiber agrees with the upper
cut.

This is the precise formal surface for the argument that normalization produces
canonical truncation data rather than merely a weight assignment. -/
structure LowerCutRealizationData
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z})
    (packetCut : NormalizationPacketCutData structuralRecognition)
    (lowerTruncationCarrier :
      structuralRecognition.recognition.recognizedCategory.Object → Type z)
    (lowerTruncationObject :
      structuralRecognition.recognition.recognizedCategory.Object →
        structuralRecognition.recognition.recognizedCategory.Object) where
  lower_packets_compatible :
    NormalizationPacketCutData.canonical_threshold_cut_statement packetCut ∧
      NormalizationPacketCutData.lower_cut_admissibility_statement packetCut ∧
      NormalizationPacketCutData.boundary_dependency_closure_statement packetCut

structure UpperCutCofiberRealizationData
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z})
    (packetCut : NormalizationPacketCutData structuralRecognition)
    (upperTruncationCarrier :
      structuralRecognition.recognition.recognizedCategory.Object → Type z)
    (upperTruncationObject :
      structuralRecognition.recognition.recognizedCategory.Object →
        structuralRecognition.recognition.recognizedCategory.Object)
    (cofiberSequenceWitness :
      structuralRecognition.recognition.recognizedCategory.Object → Type z)
    (cofiberIdentifiesUpper :
      structuralRecognition.recognition.recognizedCategory.Object → Prop) where
  upper_packets_compatible :
    NormalizationPacketCutData.upper_cut_admissibility_statement packetCut
  cofiber_sequence_data :
    ∀ X : structuralRecognition.recognition.recognizedCategory.Object,
      cofiberSequenceWitness X
  cofiber_agrees_with_upper :
    ∀ X : structuralRecognition.recognition.recognizedCategory.Object,
      cofiberIdentifiesUpper X

structure CanonicalInclusionData
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z})
    (packetCut : NormalizationPacketCutData structuralRecognition)
    (lowerTruncationCarrier :
      structuralRecognition.recognition.recognizedCategory.Object → Type z)
    (totalObject :
      structuralRecognition.recognition.recognizedCategory.Object →
        structuralRecognition.recognition.recognizedCategory.Object)
    (lowerTruncationObject :
      structuralRecognition.recognition.recognizedCategory.Object →
        structuralRecognition.recognition.recognizedCategory.Object)
    (lowerInclusion :
      (X : structuralRecognition.recognition.recognizedCategory.Object) →
        structuralRecognition.recognition.recognizedCategory.Hom
          (lowerTruncationObject X)
          (totalObject X)) where
  inclusion_matches_cut :
    NormalizationPacketCutData.canonical_threshold_cut_statement packetCut ∧
      NormalizationPacketCutData.lower_cut_admissibility_statement packetCut

structure TruncationTriangleWitnessData
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z})
    (lowerTruncationObject :
      structuralRecognition.recognition.recognizedCategory.Object →
        structuralRecognition.recognition.recognizedCategory.Object)
    (totalObject :
      structuralRecognition.recognition.recognizedCategory.Object →
        structuralRecognition.recognition.recognizedCategory.Object)
    (upperTruncationObject :
      structuralRecognition.recognition.recognizedCategory.Object →
        structuralRecognition.recognition.recognizedCategory.Object)
    (lowerInclusion :
      (X : structuralRecognition.recognition.recognizedCategory.Object) →
        structuralRecognition.recognition.recognizedCategory.Hom
          (lowerTruncationObject X)
          (totalObject X))
    (upperProjection :
      (X : structuralRecognition.recognition.recognizedCategory.Object) →
        structuralRecognition.recognition.recognizedCategory.Hom
          (totalObject X)
          (upperTruncationObject X)) where
  distinguished_triangle :
    Prop
  tensor_triangle_compatibility :
    Prop

structure CofiberIdentifiesUpperCutData
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z})
    (packetCut : NormalizationPacketCutData structuralRecognition)
    (upperTruncationObject :
      structuralRecognition.recognition.recognizedCategory.Object →
        structuralRecognition.recognition.recognizedCategory.Object)
    (cofiberSequenceWitness :
      structuralRecognition.recognition.recognizedCategory.Object → Type z)
    (cofiberIdentifiesUpper :
      structuralRecognition.recognition.recognizedCategory.Object → Prop) where
  upper_cut_and_gluing_compatible :
    NormalizationPacketCutData.upper_cut_admissibility_statement packetCut ∧
      NormalizationPacketCutData.gluing_closure_statement packetCut
  cofiber_sequence_data :
    ∀ X : structuralRecognition.recognition.recognizedCategory.Object,
      cofiberSequenceWitness X
  cofiber_identifies_upper_cut :
    ∀ X : structuralRecognition.recognition.recognizedCategory.Object,
      cofiberIdentifiesUpper X
  distinguished_triangle :
    Prop
  cone_functoriality :
    Prop
  tensor_triangle_compatibility :
    Prop

structure TruncationFunctorialityData
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z})
    (lowerTruncationObject :
      structuralRecognition.recognition.recognizedCategory.Object →
        structuralRecognition.recognition.recognizedCategory.Object)
    (upperTruncationObject :
      structuralRecognition.recognition.recognizedCategory.Object →
        structuralRecognition.recognition.recognizedCategory.Object) where
  cone_functoriality :
    Prop

structure TruncationRecognitionCompatibilityData
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z})
    (totalObject :
      structuralRecognition.recognition.recognizedCategory.Object →
        structuralRecognition.recognition.recognizedCategory.Object)
    (lowerTruncationObject :
      structuralRecognition.recognition.recognizedCategory.Object →
        structuralRecognition.recognition.recognizedCategory.Object)
    (upperTruncationObject :
      structuralRecognition.recognition.recognizedCategory.Object →
        structuralRecognition.recognition.recognizedCategory.Object) where
  recognized_triangle_transport :
    Prop

structure TruncationWeightDevissageCompatibilityData
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z})
    (packetCut : NormalizationPacketCutData structuralRecognition) where
  packet_weight_compatibility :
    NormalizationPacketCutData.campaign11_weight_devissage_compatibility_statement packetCut

structure NormalizationTruncationTriangle
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z})
    (packetCut : NormalizationPacketCutData structuralRecognition) where
  lowerTruncationCarrier :
    structuralRecognition.recognition.recognizedCategory.Object → Type z
  upperTruncationCarrier :
    structuralRecognition.recognition.recognizedCategory.Object → Type z
  totalObject :
    structuralRecognition.recognition.recognizedCategory.Object →
      structuralRecognition.recognition.recognizedCategory.Object
  lowerTruncationObject :
    structuralRecognition.recognition.recognizedCategory.Object →
      structuralRecognition.recognition.recognizedCategory.Object
  upperTruncationObject :
    structuralRecognition.recognition.recognizedCategory.Object →
      structuralRecognition.recognition.recognizedCategory.Object
  lowerInclusion :
    (X : structuralRecognition.recognition.recognizedCategory.Object) →
      structuralRecognition.recognition.recognizedCategory.Hom
        (lowerTruncationObject X)
        (totalObject X)
  upperProjection :
    (X : structuralRecognition.recognition.recognizedCategory.Object) →
      structuralRecognition.recognition.recognizedCategory.Hom
        (totalObject X)
        (upperTruncationObject X)
  cofiberSequenceWitness :
    structuralRecognition.recognition.recognizedCategory.Object → Type z
  cofiberIdentifiesUpper :
    structuralRecognition.recognition.recognizedCategory.Object → Prop
  lowerCutRealization :
    LowerCutRealizationData structuralRecognition packetCut
      lowerTruncationCarrier lowerTruncationObject
  upperCutCofiberRealization :
    UpperCutCofiberRealizationData structuralRecognition packetCut
      upperTruncationCarrier upperTruncationObject cofiberSequenceWitness cofiberIdentifiesUpper
  canonicalInclusion :
    CanonicalInclusionData structuralRecognition packetCut
      lowerTruncationCarrier totalObject lowerTruncationObject lowerInclusion
  truncationTriangle :
    TruncationTriangleWitnessData structuralRecognition
      lowerTruncationObject totalObject upperTruncationObject lowerInclusion upperProjection
  cofiberIdentifiesUpperCut :
    CofiberIdentifiesUpperCutData structuralRecognition packetCut
      upperTruncationObject cofiberSequenceWitness cofiberIdentifiesUpper
  orthogonalityFromSeparatedDegrees :
    ∀ (X Y : structuralRecognition.recognition.recognizedCategory.Object)
      (sourcePacket : packetCut.packetRecord X)
      (targetPacket : packetCut.packetRecord Y)
      (f : structuralRecognition.recognition.recognizedCategory.Hom X Y),
      packetCut.lowerCutRecord X sourcePacket →
      packetCut.upperCutRecord Y targetPacket →
      TraceMotivicZeroMorphismWitness structuralRecognition f
  truncationFunctoriality :
    TruncationFunctorialityData structuralRecognition
      lowerTruncationObject upperTruncationObject
  recognitionCompatibility :
    TruncationRecognitionCompatibilityData structuralRecognition
      totalObject lowerTruncationObject upperTruncationObject
  campaign11WeightDevissageCompatibility :
    TruncationWeightDevissageCompatibilityData structuralRecognition packetCut

structure TStructureNormalizationCompatibilityData
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z})
    (tStructure : TraceMotivicTStructure structuralRecognition) where
  nonposCompatibility :
    ∀ (n : Int) (X : structuralRecognition.recognition.recognizedCategory.Object)
      (hX : tStructure.isNonpos n X),
      tStructure.recognition_nonpos_compatibility n X hX
  nonnegCompatibility :
    ∀ (n : Int) (X : structuralRecognition.recognition.recognizedCategory.Object)
      (hX : tStructure.isNonneg n X),
      tStructure.recognition_nonneg_compatibility n X hX

structure TStructureRecognitionCompatibilityData
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z})
    (tStructure : TraceMotivicTStructure structuralRecognition)
    {packetCut : NormalizationPacketCutData structuralRecognition}
    (truncation : NormalizationTruncationTriangle structuralRecognition packetCut) where
  truncationCompatibility :
    Prop
  recognizedTriangleTransport :
    Prop

structure TraceMotivicTStructureData
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}) where
  tStructure : TraceMotivicTStructure structuralRecognition
  packetCut : NormalizationPacketCutData structuralRecognition
  truncation : NormalizationTruncationTriangle structuralRecognition packetCut
  tNonpos :
    structuralRecognition.recognition.recognizedCategory.Object → Type z
  tNonneg :
    structuralRecognition.recognition.recognizedCategory.Object → Type z
  tNonpos_agrees : ∀ X, tNonpos X = tStructure.isNonpos 0 X
  tNonneg_agrees : ∀ X, tNonneg X = tStructure.isNonneg 0 X
  truncationFunctoriality :
    TruncationFunctorialityData structuralRecognition
      truncation.lowerTruncationObject truncation.upperTruncationObject
  normalizationCompatibility :
    TStructureNormalizationCompatibilityData structuralRecognition tStructure
  canonicalReconstructionCompatibility :
    CanonicalReconstructionCompatibilityData
      packetCut.packetRecord packetCut.packetDegree
  orthogonalityFromSeparatedDegrees :
    ∀ (X Y : structuralRecognition.recognition.recognizedCategory.Object),
      tStructure.isNonpos 0 X → tStructure.isNonneg 1 Y →
        (f : structuralRecognition.recognition.recognizedCategory.Hom X Y) →
          TraceMotivicZeroMorphismWitness structuralRecognition f
  campaign11WeightDevissageInput :
    TruncationWeightDevissageCompatibilityData structuralRecognition packetCut
  recognitionCompatibility :
    TStructureRecognitionCompatibilityData structuralRecognition tStructure truncation

namespace TraceMotivicTStructureData

/-- Indexed nonpositive half induced by the normalization packet cut. Membership
means that the object's normalized packet lies in the lower packet at threshold
`n`. The witness is intentionally concrete packet-cut data, not a theorem-name
slot. -/
def normalizationPacketNonposAt
    {structuralRecognition :
      _root_.TraceCalc.MotivicRecognition.DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (packetCut : _root_.TraceCalc.MotivicRecognition.NormalizationPacketCutData structuralRecognition)
    (n : Int)
    (X : structuralRecognition.recognition.recognizedCategory.Object) : Type z :=
  Σ packet : packetCut.packetRecord X,
    packetCut.lowerCutRecord X packet × PLift (packetCut.packetDegree X packet ≤ n)

/-- Indexed nonnegative half induced by the normalization packet cut. Membership
means that the object's normalized packet lies in the upper packet at threshold
`n + 1`. This is the complementary half used in truncation triangles
`tau_le n X -> X -> tau_ge (n+1) X`. -/
def normalizationPacketNonnegAt
    {structuralRecognition :
      _root_.TraceCalc.MotivicRecognition.DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (packetCut : _root_.TraceCalc.MotivicRecognition.NormalizationPacketCutData structuralRecognition)
    (n : Int)
    (X : structuralRecognition.recognition.recognizedCategory.Object) : Type z :=
  Σ packet : packetCut.packetRecord X,
    packetCut.upperCutRecord X packet × PLift (n ≤ packetCut.packetDegree X packet)

def truncation_functoriality_statement
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition) : Prop :=
  structuralRecognition.structuralPackage.triangulated.coneFunctorialityTarget

def truncation_functoriality_statement_holds
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition) : Prop :=
  tStructure.truncationFunctoriality.cone_functoriality

def normalization_compatibility_statement
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition) : Prop :=
  (∀ (n : Int) (X : structuralRecognition.recognition.recognizedCategory.Object)
      (hX : tStructure.tStructure.isNonpos n X),
      tStructure.tStructure.recognition_nonpos_compatibility n X hX) ∧
    ∀ (n : Int) (X : structuralRecognition.recognition.recognizedCategory.Object)
      (hX : tStructure.tStructure.isNonneg n X),
      tStructure.tStructure.recognition_nonneg_compatibility n X hX

theorem normalization_compatibility_statement_holds
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition) :
    normalization_compatibility_statement tStructure :=
  ⟨tStructure.normalizationCompatibility.nonposCompatibility,
    tStructure.normalizationCompatibility.nonnegCompatibility⟩

def canonical_reconstruction_compatibility_statement
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition) : Prop :=
  NormalizationPacketCutData.canonical_reconstruction_compatibility_statement tStructure.packetCut

theorem canonical_reconstruction_compatibility_statement_holds
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition) :
    canonical_reconstruction_compatibility_statement tStructure :=
  NormalizationPacketCutData.canonical_reconstruction_compatibility_statement_holds tStructure.packetCut

def normalization_packet_cut_statement
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition) : Prop :=
  (∀ X p,
    ∃ i : tStructure.packetCut.finiteDegreeLabeledPacketDAG.finitePacketIndex X,
      tStructure.packetCut.finiteDegreeLabeledPacketDAG.finitePacketIndexToPacket X i = p) ∧
    NormalizationPacketCutData.canonical_threshold_cut_statement tStructure.packetCut ∧
    NormalizationPacketCutData.lower_cut_admissibility_statement tStructure.packetCut ∧
    NormalizationPacketCutData.upper_cut_admissibility_statement tStructure.packetCut

theorem normalization_packet_cut_statement_holds
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition) :
    normalization_packet_cut_statement tStructure := by
  refine ⟨?_, NormalizationPacketCutData.canonical_threshold_cut_statement_holds tStructure.packetCut,
    NormalizationPacketCutData.lower_cut_admissibility_statement_holds tStructure.packetCut,
    NormalizationPacketCutData.upper_cut_admissibility_statement_holds tStructure.packetCut⟩
  intro X p
  exact ⟨(tStructure.packetCut.finiteDegreeLabeledPacketDAG.packetCovered X p).1,
    (tStructure.packetCut.finiteDegreeLabeledPacketDAG.packetCovered X p).2⟩

def normalization_truncation_triangle_statement
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition) : Prop :=
  NormalizationPacketCutData.canonical_threshold_cut_statement tStructure.packetCut ∧
    NormalizationPacketCutData.lower_cut_admissibility_statement tStructure.packetCut ∧
    NormalizationPacketCutData.upper_cut_admissibility_statement tStructure.packetCut ∧
    tStructure.truncation.truncationTriangle.distinguished_triangle ∧
    tStructure.truncation.truncationTriangle.tensor_triangle_compatibility ∧
    NormalizationPacketCutData.gluing_closure_statement tStructure.packetCut

def normalization_truncation_triangle_statement_holds
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition) : Prop :=
  tStructure.truncation.truncationTriangle.distinguished_triangle ∧
    tStructure.truncation.truncationTriangle.tensor_triangle_compatibility

def orthogonality_from_separated_degrees_statement
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition) : Prop :=
  ∀ (X Y : structuralRecognition.recognition.recognizedCategory.Object)
    (hX : tStructure.tStructure.isNonpos 0 X) (hY : tStructure.tStructure.isNonneg 1 Y)
    (f : structuralRecognition.recognition.recognizedCategory.Hom X Y),
      Nonempty (TraceMotivicZeroMorphismWitness structuralRecognition f)

theorem orthogonality_from_separated_degrees_statement_holds
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition) :
    orthogonality_from_separated_degrees_statement tStructure := by
  intro X Y hX hY f
  exact ⟨tStructure.orthogonalityFromSeparatedDegrees X Y hX hY f⟩

def campaign11_weight_devissage_input_statement
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition) : Prop :=
  NormalizationPacketCutData.campaign11_weight_devissage_compatibility_statement tStructure.packetCut

theorem campaign11_weight_devissage_input_statement_holds
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition) :
    campaign11_weight_devissage_input_statement tStructure :=
  tStructure.campaign11WeightDevissageInput.packet_weight_compatibility

def recognition_compatibility_statement
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition) : Prop :=
  structuralRecognition.structuralPackage.triangulated.distinguishedTrianglesTarget

def recognition_compatibility_statement_holds
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition) : Prop :=
  tStructure.recognitionCompatibility.recognizedTriangleTransport

theorem nonpos_is_zero_threshold
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition)
    (X : structuralRecognition.recognition.recognizedCategory.Object) :
  tStructure.tNonpos X = tStructure.tStructure.isNonpos 0 X :=
  tStructure.tNonpos_agrees X

theorem nonneg_is_zero_threshold
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition)
    (X : structuralRecognition.recognition.recognizedCategory.Object) :
  tStructure.tNonneg X = tStructure.tStructure.isNonneg 0 X :=
  tStructure.tNonneg_agrees X

end TraceMotivicTStructureData
/-- Theorem target for a coarse legacy `t`-structure compatibility shell on the
structurally-recognized motivic category.

This compatibility shell is retained for existing callers. The richer Campaign
12B target surface is `TraceMotivicTStructureData`. -/
structure TStructureTarget
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}) where
  traceMotivicTStructure : TraceMotivicTStructureData structuralRecognition
  connectiveObject :
    structuralRecognition.recognition.recognizedCategory.Object → Type z
  coconnectiveObject :
    structuralRecognition.recognition.recognizedCategory.Object → Type z
  truncationTriangleTarget : Prop
  orthogonalityTarget :
    TraceMotivicTStructureData.orthogonality_from_separated_degrees_statement
      traceMotivicTStructure

/-- Preferred honest name for the coarse compatibility shell retained for
legacy callers. Public theorem-facing routes should use
`TraceMotivicTStructureData` for the actual motivic `t`-structure target. -/
abbrev CoarseTStructureCompatibilityTarget := TStructureTarget

/-- Typed candidate for the heart of the recognized t-structure.

Membership witnesses remain type-valued rather than being collapsed into `Prop`. -/
structure HeartCandidate
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}) where
  heartObject : Type z
  forgetToMotivicObject :
    heartObject → structuralRecognition.recognition.recognizedCategory.Object
  heartMembershipWitness : heartObject → Type z

structure AbelianHeartTarget
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (heart : HeartCandidate structuralRecognition) where
  kernelData : Type z
  cokernelData : Type z
  imageData : Type z
  coimageData : Type z
  imageCoimageComparison : Type z

structure MMQHeartTarget
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {heart : HeartCandidate structuralRecognition}
    (abelianHeart : AbelianHeartTarget heart) where
  mixedMotivesOverQTarget : heart.heartObject → Type z
  realizationCompatibilityTarget : Prop
  periodCompatibilityTarget : Prop

/-- Campaign 12C typed heart surface induced by a specific Campaign 12B
`t`-structure.

This packages the heart as the intersection of the `tNonpos` and `tNonneg`
classes without assuming any pre-existing classical `MM(Q)` object. -/
structure TraceMotivicHeart
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition) where
  heartObject : Type z
  forgetToMotivicObject :
    heartObject → structuralRecognition.recognition.recognizedCategory.Object
  heartNonposWitness :
    ∀ obj : heartObject, tStructure.tNonpos (forgetToMotivicObject obj)
  heartNonnegWitness :
    ∀ obj : heartObject, tStructure.tNonneg (forgetToMotivicObject obj)

namespace TraceMotivicHeart

def ofTStructure
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition) :
    TraceMotivicHeart tStructure where
  heartObject :=
    Σ obj : structuralRecognition.recognition.recognizedCategory.Object,
      tStructure.tNonpos obj × tStructure.tNonneg obj
  forgetToMotivicObject := fun obj => obj.1
  heartNonposWitness := fun obj => obj.2.1
  heartNonnegWitness := fun obj => obj.2.2

end TraceMotivicHeart

/-- Heart morphisms are recognized-category morphisms whose endpoints are
already certified as heart objects. -/
structure TraceMotivicHeartMorphism
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (heart : TraceMotivicHeart tStructure)
    (source target : heart.heartObject) where
  underlying :
    structuralRecognition.recognition.recognizedCategory.Hom
      (heart.forgetToMotivicObject source)
      (heart.forgetToMotivicObject target)
  sourceHeart :
    tStructure.tNonpos (heart.forgetToMotivicObject source) ×
      tStructure.tNonneg (heart.forgetToMotivicObject source)
  targetHeart :
    tStructure.tNonpos (heart.forgetToMotivicObject target) ×
      tStructure.tNonneg (heart.forgetToMotivicObject target)

namespace TraceMotivicHeartMorphism

/-- Build a trace-heart morphism from its underlying recognized-category map
once the source and target heart objects have been fixed. -/
def ofUnderlying
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    {heart : TraceMotivicHeart tStructure}
    (source target : heart.heartObject)
    (underlying :
      structuralRecognition.recognition.recognizedCategory.Hom
        (heart.forgetToMotivicObject source)
        (heart.forgetToMotivicObject target)) :
    TraceMotivicHeartMorphism heart source target where
  underlying := underlying
  sourceHeart :=
    ⟨heart.heartNonposWitness source, heart.heartNonnegWitness source⟩
  targetHeart :=
    ⟨heart.heartNonposWitness target, heart.heartNonnegWitness target⟩

/-- The canonical `ofUnderlying` wrapper is determined by its underlying
recognized-category map. -/
theorem ofUnderlying_eq_of_underlying_eq
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    {heart : TraceMotivicHeart tStructure}
    {source target : heart.heartObject}
    {f g : structuralRecognition.recognition.recognizedCategory.Hom
      (heart.forgetToMotivicObject source)
      (heart.forgetToMotivicObject target)}
    (h : f = g) :
    TraceMotivicHeartMorphism.ofUnderlying source target f =
      TraceMotivicHeartMorphism.ofUnderlying source target g := by
  cases h
  rfl

/-- `HEq` on underlying recognized-category maps is enough to identify the
canonical `ofUnderlying` wrappers. -/
theorem ofUnderlying_eq_of_underlying_heq
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    {heart : TraceMotivicHeart tStructure}
    {source target : heart.heartObject}
    {f g : structuralRecognition.recognition.recognizedCategory.Hom
      (heart.forgetToMotivicObject source)
      (heart.forgetToMotivicObject target)}
    (h : HEq f g) :
    TraceMotivicHeartMorphism.ofUnderlying source target f =
      TraceMotivicHeartMorphism.ofUnderlying source target g := by
  cases h
  rfl

end TraceMotivicHeartMorphism

/-- Proof-relevant exactness data for a heart morphism. This does not assert
the abelian theorem by itself; it packages the concrete heart objects,
morphism, and comparison witness that such a theorem would consume. -/
structure TraceMotivicHeartExactData
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (heart : TraceMotivicHeart tStructure)
    {sourceObject targetObject : heart.heartObject}
    (morphism : TraceMotivicHeartMorphism heart sourceObject targetObject) where
  kernelObject : heart.heartObject
  cokernelObject : heart.heartObject
  imageObject : heart.heartObject
  coimageObject : heart.heartObject
  kernelInclusion :
    structuralRecognition.recognition.recognizedCategory.Hom
      (heart.forgetToMotivicObject kernelObject)
      (heart.forgetToMotivicObject sourceObject)
  cokernelProjection :
    structuralRecognition.recognition.recognizedCategory.Hom
      (heart.forgetToMotivicObject targetObject)
      (heart.forgetToMotivicObject cokernelObject)
  imageInclusion :
    structuralRecognition.recognition.recognizedCategory.Hom
      (heart.forgetToMotivicObject imageObject)
      (heart.forgetToMotivicObject targetObject)
  coimageProjection :
    structuralRecognition.recognition.recognizedCategory.Hom
      (heart.forgetToMotivicObject sourceObject)
      (heart.forgetToMotivicObject coimageObject)
  kernelWitness : Type z
  cokernelWitness : Type z
  imageWitness : Type z
  coimageWitness : Type z
  imageCoimageComparison :
    structuralRecognition.recognition.recognizedCategory.Hom
      (heart.forgetToMotivicObject imageObject)
      (heart.forgetToMotivicObject coimageObject)
  imageCoimageComparisonWitness : Type z

/-- Proof-relevant exactness package indexed by an actual transported heart
morphism. The package does not erase the witness carrier: consumers receive a
type of exactness data together with a realization into concrete kernel /
cokernel / image / coimage objects and maps for that same morphism. -/
structure TraceMotivicHeartExactPackage
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (heart : TraceMotivicHeart tStructure)
    {sourceObject targetObject : heart.heartObject}
    (morphism : TraceMotivicHeartMorphism heart sourceObject targetObject) where
  ExactnessWitness : Type z
  realize : ExactnessWitness → TraceMotivicHeartExactData heart morphism

abbrev TraceMotivicHeartExactWitnessData
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (heart : TraceMotivicHeart tStructure)
    (exactnessData :
      ∀ {sourceObject targetObject : heart.heartObject},
        (morphism : TraceMotivicHeartMorphism heart sourceObject targetObject) →
          TraceMotivicHeartExactPackage heart morphism) :
    Type z :=
  Σ sourceObject : heart.heartObject,
    Σ targetObject : heart.heartObject,
      Σ morphism : TraceMotivicHeartMorphism heart sourceObject targetObject,
        (exactnessData morphism).ExactnessWitness

/-- Heart-level compatibility needed to turn recognized morphism-indexed fiber
and cofiber data into actual heart objects. The recognized exactness system
constructs the underlying objects and maps; this package records that those
objects land back in the heart of the given `t`-structure. -/
structure RecognizedFiberCofiberHeartCompatibility
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition)
    (fiberCofiberSystem : RecognizedFiberCofiberSystem structuralRecognition) where
  fiberHeartWitness :
    ∀ {sourceObject targetObject :
      structuralRecognition.recognition.recognizedCategory.Object}
      (morphism :
        structuralRecognition.recognition.recognizedCategory.Hom
          sourceObject targetObject),
        tStructure.tNonpos (fiberCofiberSystem.fiberData morphism).fiberObject ×
          tStructure.tNonneg (fiberCofiberSystem.fiberData morphism).fiberObject
  cofiberHeartWitness :
    ∀ {sourceObject targetObject :
      structuralRecognition.recognition.recognizedCategory.Object}
      (morphism :
        structuralRecognition.recognition.recognizedCategory.Hom
          sourceObject targetObject),
        tStructure.tNonpos (fiberCofiberSystem.cofiberData morphism).cofiberObject ×
          tStructure.tNonneg (fiberCofiberSystem.cofiberData morphism).cofiberObject

/-- Proof-relevant image/coimage comparison data indexed by an actual heart
morphism and derived from the same recognized fiber/cofiber system. -/
structure RecognizedImageCoimageComparisonData
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition)
    (fiberCofiberSystem : RecognizedFiberCofiberSystem structuralRecognition)
    {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject}
    (morphism :
      TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
        sourceObject targetObject) where
  comparisonMorphism :
    structuralRecognition.recognition.recognizedCategory.Hom
      (fiberCofiberSystem.fiberData
        (fiberCofiberSystem.cofiberData morphism.underlying).targetToCofiber).fiberObject
      (fiberCofiberSystem.cofiberData
        (fiberCofiberSystem.fiberData morphism.underlying).fiberToSource).cofiberObject
  ComparisonWitnessCarrier : Type z
  comparisonWitness : ComparisonWitnessCarrier
  comparisonCompatibilityTarget : Prop

/-- Constructive exactness system for the Campaign 12 heart. This is the
minimal proof-relevant package needed to replace the generic fallback exactness
route. -/

structure TraceMotivicHeartConstructiveExactnessSystem
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition) where
  recognizedFiberCofiber : RecognizedFiberCofiberSystem structuralRecognition
  heartCompatibility :
    RecognizedFiberCofiberHeartCompatibility tStructure recognizedFiberCofiber
  imageCoimageComparisonData :
    ∀ {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject}
      (morphism :
        TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
          sourceObject targetObject),
        RecognizedImageCoimageComparisonData tStructure recognizedFiberCofiber morphism

namespace TraceMotivicHeart

def kernelRecognizedData
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (system : TraceMotivicHeartConstructiveExactnessSystem tStructure)
    {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject}
    (morphism :
      TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
        sourceObject targetObject) :
    RecognizedFiberData structuralRecognition morphism.underlying :=
  system.recognizedFiberCofiber.fiberData morphism.underlying

def cokernelRecognizedData
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (system : TraceMotivicHeartConstructiveExactnessSystem tStructure)
    {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject}
    (morphism :
      TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
        sourceObject targetObject) :
    RecognizedCofiberData structuralRecognition morphism.underlying :=
  system.recognizedFiberCofiber.cofiberData morphism.underlying

def imageRecognizedData
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (system : TraceMotivicHeartConstructiveExactnessSystem tStructure)
    {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject}
    (morphism :
      TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
        sourceObject targetObject) :
    RecognizedFiberData structuralRecognition
      ((TraceMotivicHeart.cokernelRecognizedData system morphism).targetToCofiber) :=
  system.recognizedFiberCofiber.fiberData
    (TraceMotivicHeart.cokernelRecognizedData system morphism).targetToCofiber

def coimageRecognizedData
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (system : TraceMotivicHeartConstructiveExactnessSystem tStructure)
    {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject}
    (morphism :
      TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
        sourceObject targetObject) :
    RecognizedCofiberData structuralRecognition
      ((TraceMotivicHeart.kernelRecognizedData system morphism).fiberToSource) :=
  system.recognizedFiberCofiber.cofiberData
    (TraceMotivicHeart.kernelRecognizedData system morphism).fiberToSource

def recognizedFiber_yields_heartKernel
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (system : TraceMotivicHeartConstructiveExactnessSystem tStructure)
    {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject}
    (morphism :
      TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
        sourceObject targetObject) :
    (TraceMotivicHeart.ofTStructure tStructure).heartObject :=
  ⟨(TraceMotivicHeart.kernelRecognizedData system morphism).fiberObject,
    system.heartCompatibility.fiberHeartWitness morphism.underlying⟩

def recognizedCofiber_yields_heartCokernel
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (system : TraceMotivicHeartConstructiveExactnessSystem tStructure)
    {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject}
    (morphism :
      TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
        sourceObject targetObject) :
    (TraceMotivicHeart.ofTStructure tStructure).heartObject :=
  ⟨(TraceMotivicHeart.cokernelRecognizedData system morphism).cofiberObject,
    system.heartCompatibility.cofiberHeartWitness morphism.underlying⟩

def heartImage_from_kernelCokernel
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (system : TraceMotivicHeartConstructiveExactnessSystem tStructure)
    {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject}
    (morphism :
      TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
        sourceObject targetObject) :
    (TraceMotivicHeart.ofTStructure tStructure).heartObject :=
  ⟨(TraceMotivicHeart.imageRecognizedData system morphism).fiberObject,
    system.heartCompatibility.fiberHeartWitness
      (TraceMotivicHeart.cokernelRecognizedData system morphism).targetToCofiber⟩

def heartCoimage_from_kernelCokernel
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (system : TraceMotivicHeartConstructiveExactnessSystem tStructure)
    {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject}
    (morphism :
      TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
        sourceObject targetObject) :
    (TraceMotivicHeart.ofTStructure tStructure).heartObject :=
  ⟨(TraceMotivicHeart.coimageRecognizedData system morphism).cofiberObject,
    system.heartCompatibility.cofiberHeartWitness
      (TraceMotivicHeart.kernelRecognizedData system morphism).fiberToSource⟩

def kernelInclusion
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (system : TraceMotivicHeartConstructiveExactnessSystem tStructure)
    {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject}
    (morphism :
      TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
        sourceObject targetObject) :
    TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
      (TraceMotivicHeart.recognizedFiber_yields_heartKernel system morphism)
      sourceObject where
  underlying := (TraceMotivicHeart.kernelRecognizedData system morphism).fiberToSource
  sourceHeart :=
    (system.heartCompatibility.fiberHeartWitness morphism.underlying)
  targetHeart := sourceObject.2

def cokernelProjection
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (system : TraceMotivicHeartConstructiveExactnessSystem tStructure)
    {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject}
    (morphism :
      TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
        sourceObject targetObject) :
    TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
      targetObject
      (TraceMotivicHeart.recognizedCofiber_yields_heartCokernel system morphism) where
  underlying := (TraceMotivicHeart.cokernelRecognizedData system morphism).targetToCofiber
  sourceHeart := targetObject.2
  targetHeart :=
    (system.heartCompatibility.cofiberHeartWitness morphism.underlying)

def imageInclusion
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (system : TraceMotivicHeartConstructiveExactnessSystem tStructure)
    {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject}
    (morphism :
      TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
        sourceObject targetObject) :
    TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
      (TraceMotivicHeart.heartImage_from_kernelCokernel system morphism)
      targetObject where
  underlying := (TraceMotivicHeart.imageRecognizedData system morphism).fiberToSource
  sourceHeart :=
    system.heartCompatibility.fiberHeartWitness
      (TraceMotivicHeart.cokernelRecognizedData system morphism).targetToCofiber
  targetHeart := targetObject.2

def coimageProjection
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (system : TraceMotivicHeartConstructiveExactnessSystem tStructure)
    {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject}
    (morphism :
      TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
        sourceObject targetObject) :
    TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
      sourceObject
      (TraceMotivicHeart.heartCoimage_from_kernelCokernel system morphism) where
  underlying := (TraceMotivicHeart.coimageRecognizedData system morphism).targetToCofiber
  sourceHeart := sourceObject.2
  targetHeart :=
    system.heartCompatibility.cofiberHeartWitness
      (TraceMotivicHeart.kernelRecognizedData system morphism).fiberToSource

def heartImageCoimageComparison
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (system : TraceMotivicHeartConstructiveExactnessSystem tStructure)
    {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject}
    (morphism :
      TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
        sourceObject targetObject) :
    TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
      (TraceMotivicHeart.heartImage_from_kernelCokernel system morphism)
      (TraceMotivicHeart.heartCoimage_from_kernelCokernel system morphism) where
  underlying := (system.imageCoimageComparisonData morphism).comparisonMorphism
  sourceHeart :=
    system.heartCompatibility.fiberHeartWitness
      (TraceMotivicHeart.cokernelRecognizedData system morphism).targetToCofiber
  targetHeart :=
    system.heartCompatibility.cofiberHeartWitness
      (TraceMotivicHeart.kernelRecognizedData system morphism).fiberToSource

end TraceMotivicHeart

structure TraceMotivicHeartKernelWitness
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (system : TraceMotivicHeartConstructiveExactnessSystem tStructure)
    {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject}
    (morphism :
      TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
        sourceObject targetObject) where
  kernelMap :
    TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
      (TraceMotivicHeart.recognizedFiber_yields_heartKernel system morphism)
      sourceObject
  universalPropertyWitness :
    (TraceMotivicHeart.kernelRecognizedData system morphism).FiberWitnessCarrier
  universalPropertyCorrect :
    (TraceMotivicHeart.kernelRecognizedData system morphism).fiberCompatibilityTarget

structure TraceMotivicHeartCokernelWitness
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (system : TraceMotivicHeartConstructiveExactnessSystem tStructure)
    {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject}
    (morphism :
      TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
        sourceObject targetObject) where
  cokernelMap :
    TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
      targetObject
      (TraceMotivicHeart.recognizedCofiber_yields_heartCokernel system morphism)
  universalPropertyWitness :
    (TraceMotivicHeart.cokernelRecognizedData system morphism).CofiberWitnessCarrier
  universalPropertyCorrect :
    (TraceMotivicHeart.cokernelRecognizedData system morphism).cofiberCompatibilityTarget

structure TraceMotivicHeartImageWitness
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (system : TraceMotivicHeartConstructiveExactnessSystem tStructure)
    {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject}
    (morphism :
      TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
        sourceObject targetObject) where
  imageMap :
    TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
      (TraceMotivicHeart.heartImage_from_kernelCokernel system morphism)
      targetObject
  factorizationWitness :
    (TraceMotivicHeart.imageRecognizedData system morphism).FiberWitnessCarrier
  factorizationCorrect :
    (TraceMotivicHeart.imageRecognizedData system morphism).fiberCompatibilityTarget

structure TraceMotivicHeartCoimageWitness
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (system : TraceMotivicHeartConstructiveExactnessSystem tStructure)
    {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject}
    (morphism :
      TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
        sourceObject targetObject) where
  coimageMap :
    TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
      sourceObject
      (TraceMotivicHeart.heartCoimage_from_kernelCokernel system morphism)
  factorizationWitness :
    (TraceMotivicHeart.coimageRecognizedData system morphism).CofiberWitnessCarrier
  factorizationCorrect :
    (TraceMotivicHeart.coimageRecognizedData system morphism).cofiberCompatibilityTarget

structure TraceMotivicHeartImageCoimageComparisonWitness
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (system : TraceMotivicHeartConstructiveExactnessSystem tStructure)
    {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject}
    (morphism :
      TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
        sourceObject targetObject) where
  comparisonMap :
    TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
      (TraceMotivicHeart.heartImage_from_kernelCokernel system morphism)
      (TraceMotivicHeart.heartCoimage_from_kernelCokernel system morphism)
  comparisonWitness :
    (system.imageCoimageComparisonData morphism).ComparisonWitnessCarrier
  comparisonCorrect :
    (system.imageCoimageComparisonData morphism).comparisonCompatibilityTarget

structure TraceMotivicHeartConstructedExactnessWitness
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (system : TraceMotivicHeartConstructiveExactnessSystem tStructure)
    {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject}
    (morphism :
      TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
        sourceObject targetObject) where
  kernelData : TraceMotivicHeartKernelWitness system morphism
  cokernelData : TraceMotivicHeartCokernelWitness system morphism
  imageData : TraceMotivicHeartImageWitness system morphism
  coimageData : TraceMotivicHeartCoimageWitness system morphism
  imageCoimageData : TraceMotivicHeartImageCoimageComparisonWitness system morphism

namespace TraceMotivicHeartExactData

def ofConstructedExactness
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (system : TraceMotivicHeartConstructiveExactnessSystem tStructure)
    {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject}
    (morphism :
      TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
        sourceObject targetObject)
    (witness : TraceMotivicHeartConstructedExactnessWitness system morphism) :
    TraceMotivicHeartExactData (TraceMotivicHeart.ofTStructure tStructure) morphism where
  kernelObject := TraceMotivicHeart.recognizedFiber_yields_heartKernel system morphism
  cokernelObject := TraceMotivicHeart.recognizedCofiber_yields_heartCokernel system morphism
  imageObject := TraceMotivicHeart.heartImage_from_kernelCokernel system morphism
  coimageObject := TraceMotivicHeart.heartCoimage_from_kernelCokernel system morphism
  kernelInclusion := witness.kernelData.kernelMap.underlying
  cokernelProjection := witness.cokernelData.cokernelMap.underlying
  imageInclusion := witness.imageData.imageMap.underlying
  coimageProjection := witness.coimageData.coimageMap.underlying
  kernelWitness := TraceMotivicHeartKernelWitness system morphism
  cokernelWitness := TraceMotivicHeartCokernelWitness system morphism
  imageWitness := TraceMotivicHeartImageWitness system morphism
  coimageWitness := TraceMotivicHeartCoimageWitness system morphism
  imageCoimageComparison := witness.imageCoimageData.comparisonMap.underlying
  imageCoimageComparisonWitness := TraceMotivicHeartImageCoimageComparisonWitness system morphism

end TraceMotivicHeartExactData

namespace TraceMotivicHeartExactPackage

def heartExactPackage_from_recognizedFiberCofiber
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (system : TraceMotivicHeartConstructiveExactnessSystem tStructure)
    {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject}
    (morphism :
      TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
        sourceObject targetObject) :
    TraceMotivicHeartExactPackage (TraceMotivicHeart.ofTStructure tStructure) morphism where
  ExactnessWitness := TraceMotivicHeartConstructedExactnessWitness system morphism
  realize := TraceMotivicHeartExactData.ofConstructedExactness system morphism

end TraceMotivicHeartExactPackage

/-- Campaign 12C legacy trace-native candidate/scaffold for the category
`MM(Q)` constructed as the heart of the Campaign 12B `t`-structure.

This is a construction target, not an assumption that a classical `MM(Q)` is
already available. No semisimplicity or global `Ext`-vanishing is asserted at
this stage. The live classical MM(Q) recognition path is
`RecognizesClassicalMMQ.ofFinalMotivicInfrastructure`
in `ManuscriptSpineTargets.lean`. -/
structure MMQ
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition) where
  motive : Type z
  forgetToMotivicObject :
    motive → structuralRecognition.recognition.recognizedCategory.Object
  heartWitness :
    ∀ obj : motive,
      tStructure.tNonpos (forgetToMotivicObject obj) ×
        tStructure.tNonneg (forgetToMotivicObject obj)

abbrev MixedMotivesQ
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}} :=
  MMQ (structuralRecognition := structuralRecognition)

namespace MMQ

/-- Campaign 12C theorem target asserting that the constructed `MM(Q)` is the
heart of the Campaign 12B `t`-structure. -/
structure isHeartOfTraceMotivicTStructure
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (mmq : MMQ tStructure) where
  heartConstructionTarget :
    ∀ obj : mmq.motive,
      tStructure.tNonpos (mmq.forgetToMotivicObject obj) ×
        tStructure.tNonneg (mmq.forgetToMotivicObject obj)
  heartAgreementTarget : TraceMotivicHeart tStructure

/-- Campaign 12C theorem target asserting that the constructed `MM(Q)` is
abelian. This does not assert semisimplicity. -/
structure isAbelianTarget
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (mmq : MMQ tStructure) where
  exactnessData :
    ∀ {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject},
      (morphism :
        TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
          sourceObject targetObject) →
        TraceMotivicHeartExactPackage (TraceMotivicHeart.ofTStructure tStructure) morphism
  kernelData : Type z
  cokernelData : Type z
  imageData : Type z
  coimageData : Type z
  imageCoimageComparison : Type z
  kernelTarget :
    ∀ {sourceObject targetObject}
      (morphism :
        TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
          sourceObject targetObject)
      (witness : (exactnessData morphism).ExactnessWitness),
        Type z
  cokernelTarget :
    ∀ {sourceObject targetObject}
      (morphism :
        TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
          sourceObject targetObject)
      (witness : (exactnessData morphism).ExactnessWitness),
        Type z
  imageCoimageTarget :
    ∀ {sourceObject targetObject}
      (morphism :
        TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
          sourceObject targetObject)
      (witness : (exactnessData morphism).ExactnessWitness),
        Type z
  abelianCategoryTarget : Type z

/-- Campaign 12D target for the embedding of the constructed `MM(Q)` into the
recognized `DM_gm(Q)_Q`-level motivic category. -/
structure embeddingIntoDMgmQTarget
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (mmq : MMQ tStructure) where
  embeddingTarget : Prop
  comparisonCompatibilityTarget : Prop
  recognitionCompatibilityTarget : Prop

end MMQ

/-- Named theorem package for the three normalization t-structure obligations in
Package 7.  Each field is an exact theorem statement, not a free `Prop` slot. -/
structure NormTStructureTheoremPackage
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition)
    (packetCut : NormalizationPacketCutData structuralRecognition) where
  /-- The normalization-transported t-structure is compatible with the underlying
  weight structure: the weight filtration cutoffs coincide with the
  t-truncation degrees as recorded by the normalization packet cut. -/
  normalizationInducesWeightCompatibleTStructure :
    TraceMotivicTStructureData.normalization_packet_cut_statement tStructure ∧
      NormalizationPacketCutData.canonical_reconstruction_compatibility_statement packetCut
  /-- The transported t-structure is motivic: the t-truncation triangles respect
  the normalization data and the campaign-11 weight devissage input. -/
  transportedTStructureIsMotivic :
    TraceMotivicTStructureData.normalization_compatibility_statement tStructure ∧
      TraceMotivicTStructureData.campaign11_weight_devissage_input_statement tStructure
  /-- Truncation triangles from the normalization packet cut are representable:
  the truncation triangle and truncation functoriality targets both hold. -/
  truncationTriangleRepresentability :
    TraceMotivicTStructureData.normalization_truncation_triangle_statement tStructure ∧
      TraceMotivicTStructureData.truncation_functoriality_statement tStructure

/-- Classical-facing recognition statement for the trace-constructed heart.

This is the exported theorem surface saying that `TraceMotivicHeart.ofTStructure`
is recognized as the classical mixed-motive abelian heart over `Q`, through the
already assembled `DM_gm(Q)_Q` recognition path. It deliberately packages the
recognition as the conjunction of the transported-heart identification, the
mixed-motive abelian-heart identification, the MM(Q) identification, and the
exact transported-heart compatibility laws, rather than reducing the statement
to a bare normalization or orthogonality fragment. -/
structure TStructureMotivicMMQInfrastructure
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition)
    (heart : TraceMotivicHeart tStructure) where
  dm_gm_Q_Q_category : Type u
  dm_gm_Q_Q_object : dm_gm_Q_Q_category
  dm_gm_Q_Q_hom : dm_gm_Q_Q_category → dm_gm_Q_Q_category → Type v
  dm_gm_Q_Q_id : ∀ X, dm_gm_Q_Q_hom X X
  dm_gm_Q_Q_comp : ∀ {X Y Z}, dm_gm_Q_Q_hom X Y → dm_gm_Q_Q_hom Y Z → dm_gm_Q_Q_hom X Z
  rationalBaseField : Type w
  rationalCoefficientField : Type x
  rationalBaseFieldIsQ : FieldIsQData rationalBaseField
  rationalCoefficientFieldIsQ : FieldIsQData rationalCoefficientField
  tNonpositive : dm_gm_Q_Q_category → Prop
  tNonnegative : dm_gm_Q_Q_category → Prop
  truncLE : Int → dm_gm_Q_Q_category → dm_gm_Q_Q_category
  truncGE : Int → dm_gm_Q_Q_category → dm_gm_Q_Q_category
  truncationTriangle : ∀ (n : Int) (X : dm_gm_Q_Q_category), Prop
  classicalHeartObject : Type y
  classicalHeartEmbedding : classicalHeartObject → dm_gm_Q_Q_category
  classicalHeartIsHeart : ∀ A : classicalHeartObject,
    tNonpositive (classicalHeartEmbedding A) ∧
      tNonnegative (classicalHeartEmbedding A)
  classicalHeartHom : classicalHeartObject → classicalHeartObject → Type z
  classicalHeartZero : classicalHeartObject
  classicalHeartAdd : classicalHeartObject → classicalHeartObject → classicalHeartObject
  classicalHeartKernel : ∀ {A B : classicalHeartObject}, classicalHeartHom A B → classicalHeartObject
  classicalHeartCokernel : ∀ {A B : classicalHeartObject}, classicalHeartHom A B → classicalHeartObject
  mixedMotivesQ : Type y
  mixedMotivesQHom : mixedMotivesQ → mixedMotivesQ → Type z
  mixedMotivesQToHeart : mixedMotivesQ → classicalHeartObject
  heartToMixedMotivesQ : classicalHeartObject → mixedMotivesQ
  mixedMotivesQToHeart_leftInverse :
    ∀ M : mixedMotivesQ, heartToMixedMotivesQ (mixedMotivesQToHeart M) = M
  mixedMotivesQToHeart_rightInverse :
    ∀ A : classicalHeartObject, mixedMotivesQToHeart (heartToMixedMotivesQ A) = A
  traceHeartToClassicalHeart : TraceMotivicHeart tStructure → classicalHeartObject
  traceHeartFromClassicalHeart : classicalHeartObject → TraceMotivicHeart tStructure
  traceHeartClassical_leftInverse :
    ∀ H : TraceMotivicHeart tStructure,
      traceHeartFromClassicalHeart (traceHeartToClassicalHeart H) = H
  traceHeartClassical_rightInverse :
    ∀ A : classicalHeartObject,
      traceHeartToClassicalHeart (traceHeartFromClassicalHeart A) = A
  distinguishedHeartAgreement : traceHeartToClassicalHeart heart =
    traceHeartToClassicalHeart (TraceMotivicHeart.ofTStructure tStructure)
  transportedTStructureMatchesClassical :
    TraceMotivicTStructureData.recognition_compatibility_statement tStructure
  normalizationRealizesClassicalHeart :
    TraceMotivicTStructureData.normalization_compatibility_statement tStructure
  canonicalReconstructionRealizesClassicalHeart :
    TraceMotivicTStructureData.canonical_reconstruction_compatibility_statement tStructure
  separatedDegreeOrthogonalityRealizesMMQ :
    TraceMotivicTStructureData.orthogonality_from_separated_degrees_statement tStructure
  exactHeartEmbedding :
    structuralRecognition.structuralPackage.triangulated.shiftFunctorTarget ∧
      structuralRecognition.structuralPackage.triangulated.shiftFunctorTarget ∧
      TraceMotivicTStructureData.orthogonality_from_separated_degrees_statement tStructure
  pureHeartNaturality :
    TraceMotivicTStructureData.normalization_compatibility_statement tStructure ∧
      TraceMotivicTStructureData.normalization_packet_cut_statement tStructure

structure RecognizesClassicalMMQ
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition)
  (heart : TraceMotivicHeart tStructure) where
  finalMotivicInfrastructure : TStructureMotivicMMQInfrastructure tStructure heart
  traceHeartIsConstructedHeart : heart = TraceMotivicHeart.ofTStructure tStructure
  recognizedDMgmQTransportTarget :
    TraceMotivicTStructureData.recognition_compatibility_statement tStructure
  classicalAbelianHeartOverQTarget :
    TraceMotivicTStructureData.normalization_compatibility_statement tStructure ∧
      TraceMotivicTStructureData.canonical_reconstruction_compatibility_statement tStructure
  mixedMotiveHeartOverQTarget :
    TraceMotivicTStructureData.normalization_compatibility_statement tStructure ∧
      TraceMotivicTStructureData.orthogonality_from_separated_degrees_statement tStructure
  transportedHeartExactnessTarget :
    structuralRecognition.structuralPackage.triangulated.shiftFunctorTarget ∧
      structuralRecognition.structuralPackage.triangulated.shiftFunctorTarget ∧
      TraceMotivicTStructureData.orthogonality_from_separated_degrees_statement tStructure
  heartRecognitionNaturalityTarget :
    TraceMotivicTStructureData.normalization_compatibility_statement tStructure ∧
      TraceMotivicTStructureData.normalization_packet_cut_statement tStructure

namespace RecognizesClassicalMMQ

/-- Assemble the classical MM(Q) recognition record from the already named
recognition-spine components. This is the provenance-preserving constructor:
each field of `RecognizesClassicalMMQ` is supplied by the corresponding
transport, heart-identification, exactness, or naturality theorem rather than
by an opaque single theorem-package field. -/
def ofFinalMotivicInfrastructure
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    {heart : TraceMotivicHeart tStructure}
    (infrastructure : TStructureMotivicMMQInfrastructure tStructure heart)
    (traceHeartIsConstructedHeart : heart = TraceMotivicHeart.ofTStructure tStructure) :
    RecognizesClassicalMMQ tStructure heart where
  finalMotivicInfrastructure := infrastructure
  traceHeartIsConstructedHeart := traceHeartIsConstructedHeart
  recognizedDMgmQTransportTarget := infrastructure.transportedTStructureMatchesClassical
  classicalAbelianHeartOverQTarget :=
    ⟨infrastructure.normalizationRealizesClassicalHeart,
      infrastructure.canonicalReconstructionRealizesClassicalHeart⟩
  mixedMotiveHeartOverQTarget :=
    ⟨infrastructure.normalizationRealizesClassicalHeart,
      infrastructure.separatedDegreeOrthogonalityRealizesMMQ⟩
  transportedHeartExactnessTarget := infrastructure.exactHeartEmbedding
  heartRecognitionNaturalityTarget := infrastructure.pureHeartNaturality

end RecognizesClassicalMMQ

/-- Named component theorem package for the classical MM(Q) heart recognition
surface.  The fields are exactly the five non-definitional component facts
needed to assemble `ClassicalMMQHeartTheorems` for the canonical transported
heart.  This record is deliberately below the final `RecognizesClassicalMMQ`
surface: it exposes the cobblestone facts individually instead of accepting the
closed recognition statement as an input. -/
structure TraceMotivicTStructureComponentTheorems
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition) where
  transportedHeartIdentifiesClassicalGeometricMotivesHeart :
    TraceMotivicTStructureData.recognition_compatibility_statement tStructure
  classicalAbelianHeartIsMixedMotivesQ :
    TraceMotivicTStructureData.normalization_compatibility_statement tStructure ∧
      TraceMotivicTStructureData.canonical_reconstruction_compatibility_statement tStructure
  mixedMotiveHeartOverQTarget :
    TraceMotivicTStructureData.normalization_compatibility_statement tStructure ∧
      TraceMotivicTStructureData.orthogonality_from_separated_degrees_statement tStructure
  compatibilityWithTransportedTStructureIsExact :
    structuralRecognition.structuralPackage.triangulated.shiftFunctorTarget ∧
      structuralRecognition.structuralPackage.triangulated.shiftFunctorTarget ∧
      TraceMotivicTStructureData.orthogonality_from_separated_degrees_statement tStructure
  compatibilityWithHeartRecognitionIsNatural :
    TraceMotivicTStructureData.normalization_compatibility_statement tStructure ∧
      TraceMotivicTStructureData.normalization_packet_cut_statement tStructure

namespace TraceMotivicTStructureComponentTheorems

/-- Assemble the component theorem package from its individual projection facts.
This is a compatibility constructor for callers that already expose the five
component theorems separately. -/
def ofComponents
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition)
    (transportedHeartIdentifiesClassicalGeometricMotivesHeart :
      TraceMotivicTStructureData.recognition_compatibility_statement tStructure)
    (classicalAbelianHeartIsMixedMotivesQ :
      TraceMotivicTStructureData.normalization_compatibility_statement tStructure ∧
        TraceMotivicTStructureData.canonical_reconstruction_compatibility_statement tStructure)
    (mixedMotiveHeartOverQTarget :
      TraceMotivicTStructureData.normalization_compatibility_statement tStructure ∧
        TraceMotivicTStructureData.orthogonality_from_separated_degrees_statement tStructure)
    (compatibilityWithTransportedTStructureIsExact :
      structuralRecognition.structuralPackage.triangulated.shiftFunctorTarget ∧
        structuralRecognition.structuralPackage.triangulated.shiftFunctorTarget ∧
        TraceMotivicTStructureData.orthogonality_from_separated_degrees_statement tStructure)
    (compatibilityWithHeartRecognitionIsNatural :
      TraceMotivicTStructureData.normalization_compatibility_statement tStructure ∧
        TraceMotivicTStructureData.normalization_packet_cut_statement tStructure) :
    TraceMotivicTStructureComponentTheorems tStructure where
  transportedHeartIdentifiesClassicalGeometricMotivesHeart :=
    transportedHeartIdentifiesClassicalGeometricMotivesHeart
  classicalAbelianHeartIsMixedMotivesQ := classicalAbelianHeartIsMixedMotivesQ
  mixedMotiveHeartOverQTarget := mixedMotiveHeartOverQTarget
  compatibilityWithTransportedTStructureIsExact :=
    compatibilityWithTransportedTStructureIsExact
  compatibilityWithHeartRecognitionIsNatural := compatibilityWithHeartRecognitionIsNatural

end TraceMotivicTStructureComponentTheorems

/-- Named theorem package for the classical heart identification in Package 7.
Each field is an exact theorem statement: the transported trace heart is the
abelian heart of the classical triangulated category of geometric motives over Q
with rational coefficients, and that heart is MM(Q). -/
structure ClassicalMMQHeartTheorems
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition)
    (heart : TraceMotivicHeart tStructure) where
  finalMotivicInfrastructure : TStructureMotivicMMQInfrastructure tStructure heart
  /-- The transported heart used by this theorem package is the canonical heart
  constructed from the transported t-structure. -/
  classicalTraceHeartAgreement : heart = TraceMotivicHeart.ofTStructure tStructure
  /-- The transported trace heart identifies with the classical abelian heart:
  `TraceMotivicHeart` already carries proof-relevant `heartNonposWitness` and
  `heartNonnegWitness` data by construction.  At the Prop level the canonical
  identification is recorded by the recognition compatibility target. -/
  transportedHeartIdentifiesClassicalGeometricMotivesHeart :
    TraceMotivicTStructureData.recognition_compatibility_statement tStructure
  /-- The classical abelian heart is the category of mixed motives over Q:
  the identification respects the mixed-motive structure recorded by
  the normalization compatibility and canonical reconstruction targets. -/
  classicalAbelianHeartIsMixedMotivesQ :
    TraceMotivicTStructureData.normalization_compatibility_statement tStructure ∧
      TraceMotivicTStructureData.canonical_reconstruction_compatibility_statement tStructure
  /-- The mixed-motive heart over Q satisfies the MM(Q)-level separated-degree
  orthogonality criterion. This is a component theorem, not the full
  `RecognizesClassicalMMQ` record. -/
  mixedMotiveHeartOverQTarget :
    TraceMotivicTStructureData.normalization_compatibility_statement tStructure ∧
      TraceMotivicTStructureData.orthogonality_from_separated_degrees_statement tStructure
  /-- The heart identification is compatible with the transported t-structure:
  the abelian heart embedding respects the shift-closure and orthogonality laws. -/
  compatibilityWithTransportedTStructureIsExact :
    structuralRecognition.structuralPackage.triangulated.shiftFunctorTarget ∧
      structuralRecognition.structuralPackage.triangulated.shiftFunctorTarget ∧
      TraceMotivicTStructureData.orthogonality_from_separated_degrees_statement tStructure
  /-- The identification is compatible with the pure-heart recognition:
  the normalization compatibility and normalization packet cut targets hold,
  confirming that pure-motive objects sit in the weight-zero part of the heart. -/
  compatibilityWithHeartRecognitionIsNatural :
    TraceMotivicTStructureData.normalization_compatibility_statement tStructure ∧
      TraceMotivicTStructureData.normalization_packet_cut_statement tStructure
  /-- The category of mixed motives over Q with rational coefficients is MM(Q):
  this compatibility alias remains for existing package code, but is derived
  from the component fields rather than accepted as a theorem-package input. -/
  classicalMixedMotivesQIsMMQ :=
    RecognizesClassicalMMQ.ofFinalMotivicInfrastructure
      (tStructure := tStructure)
      (heart := heart)
      finalMotivicInfrastructure
      classicalTraceHeartAgreement
  /-- The trace-constructed heart is recognized as the classical mixed-motive
  abelian heart over Q. This preferred exported recognition surface is derived
  from the component fields above. -/
  traceHeart_recognizes_classical_MMQ :=
    RecognizesClassicalMMQ.ofFinalMotivicInfrastructure
      (tStructure := tStructure)
      (heart := heart)
      finalMotivicInfrastructure
      classicalTraceHeartAgreement

/-- Concrete morphism-level transport data from the trace-constructed heart to
`MM(Q)`.

This is the exact missing carrier for the final replay-reflection step: object
transport from trace-heart objects to the classical heart, morphism transport
from trace-heart morphisms to classical-heart morphisms, and then transport
from classical-heart morphisms to `MM(Q)` morphisms. -/
structure ClassicalMMQHeartMorphismTransport
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    {heart : TraceMotivicHeart tStructure}
    (theorems : ClassicalMMQHeartTheorems tStructure heart) where
  traceObjectToClassicalHeart :
    heart.heartObject → theorems.finalMotivicInfrastructure.classicalHeartObject
  traceMorphismToClassicalHeart :
    ∀ {source target : heart.heartObject},
      TraceMotivicHeartMorphism heart source target →
        theorems.finalMotivicInfrastructure.classicalHeartHom
          (traceObjectToClassicalHeart source)
          (traceObjectToClassicalHeart target)
  classicalHeartMorphismToMixedMotivesQ :
    ∀ {source target : theorems.finalMotivicInfrastructure.classicalHeartObject},
      theorems.finalMotivicInfrastructure.classicalHeartHom source target →
        theorems.finalMotivicInfrastructure.mixedMotivesQHom
          (theorems.finalMotivicInfrastructure.heartToMixedMotivesQ source)
          (theorems.finalMotivicInfrastructure.heartToMixedMotivesQ target)

namespace ClassicalMMQHeartMorphismTransport

/-- The `MM(Q)` object corresponding to a trace-heart object under a concrete
morphism-transport package. -/
def traceObjectToMixedMotivesQ
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    {heart : TraceMotivicHeart tStructure}
    {theorems : ClassicalMMQHeartTheorems tStructure heart}
    (transport : ClassicalMMQHeartMorphismTransport theorems)
    (obj : heart.heartObject) :
    theorems.finalMotivicInfrastructure.mixedMotivesQ :=
  theorems.finalMotivicInfrastructure.heartToMixedMotivesQ
    (transport.traceObjectToClassicalHeart obj)

/-- Transport a trace-heart morphism to the corresponding `MM(Q)` morphism. -/
def traceMorphismToMixedMotivesQ
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    {heart : TraceMotivicHeart tStructure}
    {theorems : ClassicalMMQHeartTheorems tStructure heart}
    (transport : ClassicalMMQHeartMorphismTransport theorems)
    {source target : heart.heartObject}
    (morphism : TraceMotivicHeartMorphism heart source target) :
    theorems.finalMotivicInfrastructure.mixedMotivesQHom
      (transport.traceObjectToMixedMotivesQ source)
      (transport.traceObjectToMixedMotivesQ target) :=
  transport.classicalHeartMorphismToMixedMotivesQ
    (transport.traceMorphismToClassicalHeart morphism)

/-- The transport theorem needed by the recognized replay-reflection step:
equality of trace-heart morphisms implies equality of the transported `MM(Q)`
morphisms. -/
theorem traceMorphism_eq_implies_mixedMotivesQHom_eq
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    {heart : TraceMotivicHeart tStructure}
    {theorems : ClassicalMMQHeartTheorems tStructure heart}
    (transport : ClassicalMMQHeartMorphismTransport theorems)
    {source target : heart.heartObject}
    {f g : TraceMotivicHeartMorphism heart source target}
    (hfg : f = g) :
    transport.traceMorphismToMixedMotivesQ f =
      transport.traceMorphismToMixedMotivesQ g := by
  cases hfg
  rfl

end ClassicalMMQHeartMorphismTransport

/-- RealObjects-side semantic interpretation of completed traces into the
underlying recognized-category Hom for fixed heart endpoints.

This is the exact special case supplied by the existing frontier-determination
theorems: once a completed replay record has been interpreted as the
underlying recognized morphism between the chosen source and target heart
objects, the heart-morphism wrapper is canonical. -/
structure RealObjectsUnderlyingHeartMorphismRealization
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {C : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CanNF setup}
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (heart : TraceMotivicHeart tStructure)
    (source target : heart.heartObject) where
  underlyingOfCompletedTrace :
    TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
      structuralRecognition.recognition.recognizedCategory.Hom
        (heart.forgetToMotivicObject source)
        (heart.forgetToMotivicObject target)
  underlyingHEq_of_frontierEquiv :
    ∀ {R₁ R₂ : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup},
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.FrontierWord.Equiv
        (C.assignment.assign R₁).frontier
        (C.assignment.assign R₂).frontier →
          HEq
            (underlyingOfCompletedTrace R₁)
            (underlyingOfCompletedTrace R₂)

/-- RealObjects-side realization of completed reconstruction records as fixed
trace-heart morphisms.

This is the exact seam for the remaining holographic step: once a certified
completed trace has been assigned a trace-heart morphism with fixed source and
target heart objects, frontier-equivalent completed traces determine the same
underlying heart morphism action. -/
structure RealObjectsTraceHeartMorphismRealization
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {C : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CanNF setup}
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (heart : TraceMotivicHeart tStructure)
    (source target : heart.heartObject) where
  underlyingOfCompletedTrace :
    TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
      structuralRecognition.recognition.recognizedCategory.Hom
        (heart.forgetToMotivicObject source)
        (heart.forgetToMotivicObject target)
  underlyingHEq_of_frontierEquiv :
    ∀ {R₁ R₂ : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup},
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.FrontierWord.Equiv
        (C.assignment.assign R₁).frontier
        (C.assignment.assign R₂).frontier →
          HEq
            (underlyingOfCompletedTrace R₁)
            (underlyingOfCompletedTrace R₂)

namespace RealObjectsTraceHeartMorphismRealization

/-- The canonical trace-heart morphism realized by a completed trace. -/
def morphismOfCompletedTrace
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {C : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CanNF setup}
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    {heart : TraceMotivicHeart tStructure}
    {source target : heart.heartObject}
    (realization : RealObjectsTraceHeartMorphismRealization (C := C) heart source target)
    (R : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup) :
    TraceMotivicHeartMorphism heart source target :=
  TraceMotivicHeartMorphism.ofUnderlying source target
    (realization.underlyingOfCompletedTrace R)

@[simp] theorem morphismOfCompletedTrace_underlying
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {C : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CanNF setup}
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    {heart : TraceMotivicHeart tStructure}
    {source target : heart.heartObject}
    (realization : RealObjectsTraceHeartMorphismRealization (C := C) heart source target)
    (R : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup) :
    (realization.morphismOfCompletedTrace R).underlying = realization.underlyingOfCompletedTrace R :=
  rfl

/-- Frontier-equivalent completed traces induce the same trace-heart morphism
once the realization map fixes the source and target heart objects. -/
theorem traceHeartMorphism_eq_of_frontierEquiv
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {C : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CanNF setup}
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    {heart : TraceMotivicHeart tStructure}
    {source target : heart.heartObject}
    (realization : RealObjectsTraceHeartMorphismRealization (C := C) heart source target)
    {R₁ R₂ : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup}
    (hFrontier : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.FrontierWord.Equiv
      (C.assignment.assign R₁).frontier
      (C.assignment.assign R₂).frontier) :
    realization.morphismOfCompletedTrace R₁ =
      realization.morphismOfCompletedTrace R₂ := by
  exact TraceMotivicHeartMorphism.ofUnderlying_eq_of_underlying_heq
    (source := source) (target := target)
    (realization.underlyingHEq_of_frontierEquiv hFrontier)

/-- Equality of RealObjects canonical normal forms implies equality of the
realized trace-heart morphisms.

This is the exact CanNF-to-trace-heart equality step needed by the holographic
bridge once the completed-trace-to-heart realization has been fixed. -/
theorem traceHeartMorphism_eq_of_normalize_eq
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {C : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CanNF setup}
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    {heart : TraceMotivicHeart tStructure}
    {source target : heart.heartObject}
    (realization : RealObjectsTraceHeartMorphismRealization (C := C) heart source target)
    {R₁ R₂ : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup}
    (hNormalize : C.normalize R₁ = C.normalize R₂) :
    realization.morphismOfCompletedTrace R₁ =
      realization.morphismOfCompletedTrace R₂ := by
  exact realization.traceHeartMorphism_eq_of_frontierEquiv
    (C.CanNF_complete hNormalize)

/-- Frontier-equivalent completed traces induce the same transported
`MM(Q)` morphism once the completed traces have been realized as fixed
trace-heart morphisms and the heart-level transport to `MM(Q)` is available. -/
theorem mixedMotivesQHom_eq_of_frontierEquiv
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {C : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CanNF setup}
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    {heart : TraceMotivicHeart tStructure}
    {theorems : ClassicalMMQHeartTheorems tStructure heart}
    (transport : ClassicalMMQHeartMorphismTransport theorems)
    {source target : heart.heartObject}
    (realization : RealObjectsTraceHeartMorphismRealization (C := C) heart source target)
    {R₁ R₂ : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup}
    (hFrontier : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.FrontierWord.Equiv
      (C.assignment.assign R₁).frontier
      (C.assignment.assign R₂).frontier) :
    transport.traceMorphismToMixedMotivesQ (realization.morphismOfCompletedTrace R₁) =
      transport.traceMorphismToMixedMotivesQ (realization.morphismOfCompletedTrace R₂) := by
  exact ClassicalMMQHeartMorphismTransport.traceMorphism_eq_implies_mixedMotivesQHom_eq
    transport
    (realization.traceHeartMorphism_eq_of_frontierEquiv hFrontier)

/-- Equality of RealObjects canonical normal forms induces equality of the
transported `MM(Q)` morphisms once the completed traces have been realized as
fixed trace-heart morphisms. -/
theorem mixedMotivesQHom_eq_of_normalize_eq
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {C : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CanNF setup}
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    {heart : TraceMotivicHeart tStructure}
    {theorems : ClassicalMMQHeartTheorems tStructure heart}
    (transport : ClassicalMMQHeartMorphismTransport theorems)
    {source target : heart.heartObject}
    (realization : RealObjectsTraceHeartMorphismRealization (C := C) heart source target)
    {R₁ R₂ : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup}
    (hNormalize : C.normalize R₁ = C.normalize R₂) :
    transport.traceMorphismToMixedMotivesQ (realization.morphismOfCompletedTrace R₁) =
      transport.traceMorphismToMixedMotivesQ (realization.morphismOfCompletedTrace R₂) := by
  exact realization.mixedMotivesQHom_eq_of_frontierEquiv transport
    (C.CanNF_complete hNormalize)

end RealObjectsTraceHeartMorphismRealization

namespace RealObjectsUnderlyingHeartMorphismRealization

/-- Upgrade an underlying-map realization of completed traces to the fixed
trace-heart realization map. The endpoint heart witnesses are supplied once and
for all by the chosen source and target heart objects. -/
def toTraceHeartMorphismRealization
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {C : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CanNF setup}
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    {heart : TraceMotivicHeart tStructure}
    {source target : heart.heartObject}
    (realization :
      RealObjectsUnderlyingHeartMorphismRealization (C := C) heart source target) :
    RealObjectsTraceHeartMorphismRealization (C := C) heart source target where
  underlyingOfCompletedTrace := realization.underlyingOfCompletedTrace
  underlyingHEq_of_frontierEquiv := by
    intro R₁ R₂ hFrontier
    exact realization.underlyingHEq_of_frontierEquiv hFrontier

@[simp] theorem toTraceHeartMorphismRealization_underlying
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {C : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CanNF setup}
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    {heart : TraceMotivicHeart tStructure}
    {source target : heart.heartObject}
    (realization :
      RealObjectsUnderlyingHeartMorphismRealization (C := C) heart source target)
    (R : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup) :
    (realization.toTraceHeartMorphismRealization.morphismOfCompletedTrace R).underlying =
      realization.underlyingOfCompletedTrace R :=
  rfl

end RealObjectsUnderlyingHeartMorphismRealization

namespace ClassicalMMQHeartTheorems

/-- Assemble the classical MM(Q) heart theorem package from the named component
theorem package for the canonical transported heart. -/
def ofTStructureComponentTheorems
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition)
    (components : TraceMotivicTStructureComponentTheorems tStructure)
    (infrastructure :
      TStructureMotivicMMQInfrastructure tStructure
        (TraceMotivicHeart.ofTStructure tStructure)) :
    ClassicalMMQHeartTheorems tStructure (TraceMotivicHeart.ofTStructure tStructure) where
  finalMotivicInfrastructure := infrastructure
  classicalTraceHeartAgreement := rfl
  transportedHeartIdentifiesClassicalGeometricMotivesHeart :=
    components.transportedHeartIdentifiesClassicalGeometricMotivesHeart
  classicalAbelianHeartIsMixedMotivesQ :=
    components.classicalAbelianHeartIsMixedMotivesQ
  mixedMotiveHeartOverQTarget := components.mixedMotiveHeartOverQTarget
  compatibilityWithTransportedTStructureIsExact :=
    components.compatibilityWithTransportedTStructureIsExact
  compatibilityWithHeartRecognitionIsNatural :=
    components.compatibilityWithHeartRecognitionIsNatural

/-- Canonical local assembly route for a `TraceMotivicTStructureData` once its
component theorem package has been exposed. -/
def ofTraceMotivicTStructureData
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition)
    (components : TraceMotivicTStructureComponentTheorems tStructure)
    (infrastructure :
      TStructureMotivicMMQInfrastructure tStructure
        (TraceMotivicHeart.ofTStructure tStructure)) :
    ClassicalMMQHeartTheorems tStructure (TraceMotivicHeart.ofTStructure tStructure) :=
  ofTStructureComponentTheorems tStructure components infrastructure

/-- Assemble the classical MM(Q) heart theorem package from its component
fields for the canonical transported heart. This constructor does not accept
the final `RecognizesClassicalMMQ` record; both exported MM(Q) aliases are
derived by the structure defaults. -/
def ofTransportedTStructureComponents
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition)
    (transportedHeartIdentifiesClassicalGeometricMotivesHeart :
      TraceMotivicTStructureData.recognition_compatibility_statement tStructure)
    (classicalAbelianHeartIsMixedMotivesQ :
      TraceMotivicTStructureData.normalization_compatibility_statement tStructure ∧
        TraceMotivicTStructureData.canonical_reconstruction_compatibility_statement tStructure)
    (mixedMotiveHeartOverQTarget :
      TraceMotivicTStructureData.normalization_compatibility_statement tStructure ∧
        TraceMotivicTStructureData.orthogonality_from_separated_degrees_statement tStructure)
    (compatibilityWithTransportedTStructureIsExact :
      structuralRecognition.structuralPackage.triangulated.shiftFunctorTarget ∧
        structuralRecognition.structuralPackage.triangulated.shiftFunctorTarget ∧
        TraceMotivicTStructureData.orthogonality_from_separated_degrees_statement tStructure)
    (compatibilityWithHeartRecognitionIsNatural :
      TraceMotivicTStructureData.normalization_compatibility_statement tStructure ∧
        TraceMotivicTStructureData.normalization_packet_cut_statement tStructure)
    (infrastructure :
      TStructureMotivicMMQInfrastructure tStructure
        (TraceMotivicHeart.ofTStructure tStructure)) :
    ClassicalMMQHeartTheorems tStructure (TraceMotivicHeart.ofTStructure tStructure) :=
  ClassicalMMQHeartTheorems.ofTStructureComponentTheorems tStructure
    (TraceMotivicTStructureComponentTheorems.ofComponents tStructure
      transportedHeartIdentifiesClassicalGeometricMotivesHeart
      classicalAbelianHeartIsMixedMotivesQ
      mixedMotiveHeartOverQTarget
      compatibilityWithTransportedTStructureIsExact
      compatibilityWithHeartRecognitionIsNatural)
    infrastructure

end ClassicalMMQHeartTheorems

/-- Indexed weight classes used by the internal pure-heart construction route.
This keeps the weight-side grading explicit, before the bounded `t`-structure
is transported back from the semisimple pure heart. -/
structure IndexedWeightClassSystem
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (weightStructure : WeightStructureTarget structuralRecognition) where
  nonpositiveAt :
    Int → structuralRecognition.recognition.recognizedCategory.Object → Type z
  nonnegativeAt :
    Int → structuralRecognition.recognition.recognizedCategory.Object → Type z
  zero_nonpositive :
    ∀ X,
      nonpositiveAt 0 X = weightStructure.weightClassNonpositive X
  zero_nonnegative :
    ∀ X,
      nonnegativeAt 0 X = weightStructure.weightClassNonnegative X

/-- Internal pure heart coming from the weight-zero part before passage to the
transported bounded `t`-structure. -/
structure TracePureWeightHeart
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (weightStructure : WeightStructureTarget structuralRecognition) where
  heartObject : Type z
  forgetToMotivicObject :
    heartObject → structuralRecognition.recognition.recognizedCategory.Object
  heartNonpositive :
    ∀ obj : heartObject,
      weightStructure.weightClassNonpositive (forgetToMotivicObject obj)
  heartNonnegative :
    ∀ obj : heartObject,
      weightStructure.weightClassNonnegative (forgetToMotivicObject obj)

namespace TracePureWeightHeart

def ofWeightStructure
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (weightStructure : WeightStructureTarget structuralRecognition) :
    TracePureWeightHeart weightStructure where
  heartObject :=
    Σ obj : structuralRecognition.recognition.recognizedCategory.Object,
      weightStructure.weightClassNonpositive obj ×
        weightStructure.weightClassNonnegative obj
  forgetToMotivicObject := fun obj => obj.1
  heartNonpositive := fun obj => obj.2.1
  heartNonnegative := fun obj => obj.2.2

end TracePureWeightHeart

/-- Morphisms in the internal pure heart. -/
structure TracePureWeightHeartMorphism
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {weightStructure : WeightStructureTarget structuralRecognition}
    (pureHeart : TracePureWeightHeart weightStructure)
    (source target : pureHeart.heartObject) where
  underlying :
    structuralRecognition.recognition.recognizedCategory.Hom
      (pureHeart.forgetToMotivicObject source)
      (pureHeart.forgetToMotivicObject target)
  sourceHeart :
    weightStructure.weightClassNonpositive (pureHeart.forgetToMotivicObject source) ×
      weightStructure.weightClassNonnegative (pureHeart.forgetToMotivicObject source)
  targetHeart :
    weightStructure.weightClassNonpositive (pureHeart.forgetToMotivicObject target) ×
      weightStructure.weightClassNonnegative (pureHeart.forgetToMotivicObject target)

namespace TracePureWeightHeartMorphism

def ofUnderlying
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {weightStructure : WeightStructureTarget structuralRecognition}
    {pureHeart : TracePureWeightHeart weightStructure}
    (source target : pureHeart.heartObject)
    (underlying :
      structuralRecognition.recognition.recognizedCategory.Hom
        (pureHeart.forgetToMotivicObject source)
        (pureHeart.forgetToMotivicObject target)) :
    TracePureWeightHeartMorphism pureHeart source target where
  underlying := underlying
  sourceHeart :=
    ⟨pureHeart.heartNonpositive source, pureHeart.heartNonnegative source⟩
  targetHeart :=
    ⟨pureHeart.heartNonpositive target, pureHeart.heartNonnegative target⟩

end TracePureWeightHeartMorphism

/-- Step 1: full shifted-Hom vanishing on the internal pure heart. -/
structure PureHeartFullVanishingStep
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {weightStructure : WeightStructureTarget structuralRecognition}
    (pureHeart : TracePureWeightHeart weightStructure) where
  shiftedPureObject :
    Int → pureHeart.heartObject →
      structuralRecognition.recognition.recognizedCategory.Object
  shift_zero :
    ∀ obj : pureHeart.heartObject,
      shiftedPureObject 0 obj = pureHeart.forgetToMotivicObject obj
  nonzeroShiftHomVanishes :
    ∀ (source target : pureHeart.heartObject) (n : Int),
      n ≠ 0 →
      (f : structuralRecognition.recognition.recognizedCategory.Hom
        (pureHeart.forgetToMotivicObject source)
        (shiftedPureObject n target)) →
        Prop

namespace PureHeartFullVanishingStep

/-- Minimal bridge needed to turn the certified Campaign 11 orthogonality seam
into Step 1 full vanishing on the internal pure heart.

Mathematically, this isolates the remaining input that Campaign 11 still has to
provide before the eight-step route becomes genuinely constructed: for each
nonzero shift of a pure-heart object, the source object and shifted target must
be exhibited in a separated weight configuration. -/
structure FromCertifiedWeightOrthogonalityBridge
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (weightStructure : WeightStructureTarget structuralRecognition)
    (pureHeart : TracePureWeightHeart weightStructure) where
  shiftedPureObject :
    Int → pureHeart.heartObject →
      structuralRecognition.recognition.recognizedCategory.Object
  shift_zero :
    ∀ obj : pureHeart.heartObject,
      shiftedPureObject 0 obj = pureHeart.forgetToMotivicObject obj
  separatedShiftRelation :
    ∀ (source target : pureHeart.heartObject) (n : Int),
      n ≠ 0 →
      weightStructure.separatedWeightRelation
        (pureHeart.forgetToMotivicObject source)
        (shiftedPureObject n target)

def ofCertifiedWeightOrthogonality
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {weightStructure : WeightStructureTarget structuralRecognition}
    (pureHeart : TracePureWeightHeart weightStructure)
    (bridge : FromCertifiedWeightOrthogonalityBridge weightStructure pureHeart) :
    PureHeartFullVanishingStep pureHeart where
  shiftedPureObject := bridge.shiftedPureObject
  shift_zero := bridge.shift_zero
  nonzeroShiftHomVanishes := by
    intro source target n hn f
    exact weightStructure.proofRelevantOrthogonalityTarget
      (bridge.separatedShiftRelation source target n hn)
      f

end PureHeartFullVanishingStep

/-- Step 2: cone of a pure-heart morphism has weight range `[-1,0]`. -/
structure PureHeartConeWeightRangeStep
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {weightStructure : WeightStructureTarget structuralRecognition}
    (indexedWeightClasses : IndexedWeightClassSystem weightStructure)
    (pureHeart : TracePureWeightHeart weightStructure)
    (vanishing : PureHeartFullVanishingStep pureHeart) where
  coneObject :
    ∀ {source target : pureHeart.heartObject},
      TracePureWeightHeartMorphism pureHeart source target →
        structuralRecognition.recognition.recognizedCategory.Object
  coneWeightNonpositive :
    ∀ {source target : pureHeart.heartObject}
      (morphism : TracePureWeightHeartMorphism pureHeart source target),
      indexedWeightClasses.nonpositiveAt 0 (coneObject morphism)
  coneWeightNonnegative :
    ∀ {source target : pureHeart.heartObject}
      (morphism : TracePureWeightHeartMorphism pureHeart source target),
      indexedWeightClasses.nonnegativeAt (-1) (coneObject morphism)

namespace PureHeartConeWeightRangeStep

/-- Step 2 data abstracting the cone-weight-range lemma used in the semisimplicity
argument in the paper. The input is exactly the cone carrier together with the
two weight-bound witnesses asserted by Lemma `cone-weight-range`. -/
structure FromConeTriangleBridge
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {weightStructure : WeightStructureTarget structuralRecognition}
    (indexedWeightClasses : IndexedWeightClassSystem weightStructure)
    (pureHeart : TracePureWeightHeart weightStructure)
    (vanishing : PureHeartFullVanishingStep pureHeart) where
  coneObject :
    ∀ {source target : pureHeart.heartObject},
      TracePureWeightHeartMorphism pureHeart source target →
        structuralRecognition.recognition.recognizedCategory.Object
  coneWeightNonpositive :
    ∀ {source target : pureHeart.heartObject}
      (morphism : TracePureWeightHeartMorphism pureHeart source target),
      indexedWeightClasses.nonpositiveAt 0 (coneObject morphism)
  coneWeightNonnegative :
    ∀ {source target : pureHeart.heartObject}
      (morphism : TracePureWeightHeartMorphism pureHeart source target),
      indexedWeightClasses.nonnegativeAt (-1) (coneObject morphism)

def ofConeTriangleBridge
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {weightStructure : WeightStructureTarget structuralRecognition}
    {indexedWeightClasses : IndexedWeightClassSystem weightStructure}
    {pureHeart : TracePureWeightHeart weightStructure}
    {vanishing : PureHeartFullVanishingStep pureHeart}
    (bridge : FromConeTriangleBridge indexedWeightClasses pureHeart vanishing) :
    PureHeartConeWeightRangeStep indexedWeightClasses pureHeart vanishing where
  coneObject := bridge.coneObject
  coneWeightNonpositive := bridge.coneWeightNonpositive
  coneWeightNonnegative := bridge.coneWeightNonnegative

end PureHeartConeWeightRangeStep

/-- Step 3: the internal pure heart is semisimple abelian. -/
structure PureHeartSemisimpleAbelianStep
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {weightStructure : WeightStructureTarget structuralRecognition}
    (indexedWeightClasses : IndexedWeightClassSystem weightStructure)
    (pureHeart : TracePureWeightHeart weightStructure)
    (vanishing : PureHeartFullVanishingStep pureHeart)
    (coneRange : PureHeartConeWeightRangeStep indexedWeightClasses pureHeart vanishing) where
  kernelObject :
    ∀ {source target : pureHeart.heartObject},
      TracePureWeightHeartMorphism pureHeart source target → pureHeart.heartObject
  cokernelObject :
    ∀ {source target : pureHeart.heartObject},
      TracePureWeightHeartMorphism pureHeart source target → pureHeart.heartObject
  imageObject :
    ∀ {source target : pureHeart.heartObject},
      TracePureWeightHeartMorphism pureHeart source target → pureHeart.heartObject
  coimageObject :
    ∀ {source target : pureHeart.heartObject},
      TracePureWeightHeartMorphism pureHeart source target → pureHeart.heartObject
  kernelWitness :
    ∀ {source target : pureHeart.heartObject}
      (morphism : TracePureWeightHeartMorphism pureHeart source target),
        Type z
  cokernelWitness :
    ∀ {source target : pureHeart.heartObject}
      (morphism : TracePureWeightHeartMorphism pureHeart source target),
        Type z
  imageWitness :
    ∀ {source target : pureHeart.heartObject}
      (morphism : TracePureWeightHeartMorphism pureHeart source target),
        Type z
  coimageWitness :
    ∀ {source target : pureHeart.heartObject}
      (morphism : TracePureWeightHeartMorphism pureHeart source target),
        Type z
  imageCoimageComparison :
    ∀ {source target : pureHeart.heartObject}
      (morphism : TracePureWeightHeartMorphism pureHeart source target),
        structuralRecognition.recognition.recognizedCategory.Hom
          (pureHeart.forgetToMotivicObject (imageObject morphism))
          (pureHeart.forgetToMotivicObject (coimageObject morphism))
  imageCoimageComparisonWitness :
    ∀ {source target : pureHeart.heartObject}
      (morphism : TracePureWeightHeartMorphism pureHeart source target),
        Type z
  everyShortExactSequenceSplits :
    ∀ {source target : pureHeart.heartObject}
      (morphism : TracePureWeightHeartMorphism pureHeart source target),
        Type z

namespace PureHeartSemisimpleAbelianStep

/-- Manuscript-sourced bridge for Step 3, matching the proof that kernels,
cokernels, image/coimage comparison, and splitting of short exact sequences are
all extracted from the cone-weight-range argument. -/
structure FromConeWeightRangeBridge
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {weightStructure : WeightStructureTarget structuralRecognition}
    (indexedWeightClasses : IndexedWeightClassSystem weightStructure)
    (pureHeart : TracePureWeightHeart weightStructure)
    (vanishing : PureHeartFullVanishingStep pureHeart)
    (coneRange : PureHeartConeWeightRangeStep indexedWeightClasses pureHeart vanishing) where
  kernelObject :
    ∀ {source target : pureHeart.heartObject},
      TracePureWeightHeartMorphism pureHeart source target → pureHeart.heartObject
  cokernelObject :
    ∀ {source target : pureHeart.heartObject},
      TracePureWeightHeartMorphism pureHeart source target → pureHeart.heartObject
  imageObject :
    ∀ {source target : pureHeart.heartObject},
      TracePureWeightHeartMorphism pureHeart source target → pureHeart.heartObject
  coimageObject :
    ∀ {source target : pureHeart.heartObject},
      TracePureWeightHeartMorphism pureHeart source target → pureHeart.heartObject
  kernelWitness :
    ∀ {source target : pureHeart.heartObject}
      (morphism : TracePureWeightHeartMorphism pureHeart source target), Type z
  cokernelWitness :
    ∀ {source target : pureHeart.heartObject}
      (morphism : TracePureWeightHeartMorphism pureHeart source target), Type z
  imageWitness :
    ∀ {source target : pureHeart.heartObject}
      (morphism : TracePureWeightHeartMorphism pureHeart source target), Type z
  coimageWitness :
    ∀ {source target : pureHeart.heartObject}
      (morphism : TracePureWeightHeartMorphism pureHeart source target), Type z
  imageCoimageComparison :
    ∀ {source target : pureHeart.heartObject}
      (morphism : TracePureWeightHeartMorphism pureHeart source target),
      structuralRecognition.recognition.recognizedCategory.Hom
        (pureHeart.forgetToMotivicObject (imageObject morphism))
        (pureHeart.forgetToMotivicObject (coimageObject morphism))
  imageCoimageComparisonWitness :
    ∀ {source target : pureHeart.heartObject}
      (morphism : TracePureWeightHeartMorphism pureHeart source target), Type z
  everyShortExactSequenceSplits :
    ∀ {source target : pureHeart.heartObject}
      (morphism : TracePureWeightHeartMorphism pureHeart source target), Type z

def ofConeWeightRangeBridge
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {weightStructure : WeightStructureTarget structuralRecognition}
    {indexedWeightClasses : IndexedWeightClassSystem weightStructure}
    {pureHeart : TracePureWeightHeart weightStructure}
    {vanishing : PureHeartFullVanishingStep pureHeart}
    {coneRange : PureHeartConeWeightRangeStep indexedWeightClasses pureHeart vanishing}
    (bridge : FromConeWeightRangeBridge indexedWeightClasses pureHeart vanishing coneRange) :
    PureHeartSemisimpleAbelianStep indexedWeightClasses pureHeart vanishing coneRange where
  kernelObject := bridge.kernelObject
  cokernelObject := bridge.cokernelObject
  imageObject := bridge.imageObject
  coimageObject := bridge.coimageObject
  kernelWitness := bridge.kernelWitness
  cokernelWitness := bridge.cokernelWitness
  imageWitness := bridge.imageWitness
  coimageWitness := bridge.coimageWitness
  imageCoimageComparison := bridge.imageCoimageComparison
  imageCoimageComparisonWitness := bridge.imageCoimageComparisonWitness
  everyShortExactSequenceSplits := bridge.everyShortExactSequenceSplits

end PureHeartSemisimpleAbelianStep

/-- Step 4: split weight decompositions and the exact equivalence with the
bounded homotopy category of the pure heart. -/
structure SplitWeightDecompositionStep
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {weightStructure : WeightStructureTarget structuralRecognition}
    (pureHeart : TracePureWeightHeart weightStructure)
    {indexedWeightClasses : IndexedWeightClassSystem weightStructure}
    {vanishing : PureHeartFullVanishingStep pureHeart}
    {coneRange : PureHeartConeWeightRangeStep indexedWeightClasses pureHeart vanishing}
    (semisimple :
      PureHeartSemisimpleAbelianStep indexedWeightClasses pureHeart vanishing coneRange) where
  boundedHomotopyCategory : Type u
  toBoundedHomotopy :
    structuralRecognition.recognition.recognizedCategory.Object → boundedHomotopyCategory
  fromBoundedHomotopy :
    boundedHomotopyCategory → structuralRecognition.recognition.recognizedCategory.Object
  splitWeightTriangleWitness :
    structuralRecognition.recognition.recognizedCategory.Object → Type z
  objectDecompositionWitness :
    structuralRecognition.recognition.recognizedCategory.Object → Type z
  transportLeftInverse :
    ∀ X : structuralRecognition.recognition.recognizedCategory.Object,
      fromBoundedHomotopy (toBoundedHomotopy X) = X
  transportRightInverse :
    ∀ K : boundedHomotopyCategory,
      toBoundedHomotopy (fromBoundedHomotopy K) = K

namespace SplitWeightDecompositionStep

/-- Manuscript-sourced bridge for Step 4, matching the splitting of weight
decomposition triangles and the resulting equivalence with `K^b(H_w)`. -/
structure FromWeightSplittingBridge
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {weightStructure : WeightStructureTarget structuralRecognition}
    (pureHeart : TracePureWeightHeart weightStructure)
    {indexedWeightClasses : IndexedWeightClassSystem weightStructure}
    {vanishing : PureHeartFullVanishingStep pureHeart}
    {coneRange : PureHeartConeWeightRangeStep indexedWeightClasses pureHeart vanishing}
    (semisimple :
      PureHeartSemisimpleAbelianStep indexedWeightClasses pureHeart vanishing coneRange) where
  boundedHomotopyCategory : Type u
  toBoundedHomotopy :
    structuralRecognition.recognition.recognizedCategory.Object → boundedHomotopyCategory
  fromBoundedHomotopy :
    boundedHomotopyCategory → structuralRecognition.recognition.recognizedCategory.Object
  splitWeightTriangleWitness :
    structuralRecognition.recognition.recognizedCategory.Object → Type z
  objectDecompositionWitness :
    structuralRecognition.recognition.recognizedCategory.Object → Type z
  transportLeftInverse :
    ∀ X : structuralRecognition.recognition.recognizedCategory.Object,
      fromBoundedHomotopy (toBoundedHomotopy X) = X
  transportRightInverse :
    ∀ K : boundedHomotopyCategory,
      toBoundedHomotopy (fromBoundedHomotopy K) = K

def ofWeightSplittingBridge
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {weightStructure : WeightStructureTarget structuralRecognition}
    {pureHeart : TracePureWeightHeart weightStructure}
    {indexedWeightClasses : IndexedWeightClassSystem weightStructure}
    {vanishing : PureHeartFullVanishingStep pureHeart}
    {coneRange : PureHeartConeWeightRangeStep indexedWeightClasses pureHeart vanishing}
    {semisimple :
      PureHeartSemisimpleAbelianStep indexedWeightClasses pureHeart vanishing coneRange}
    (bridge : FromWeightSplittingBridge pureHeart semisimple) :
    SplitWeightDecompositionStep pureHeart semisimple where
  boundedHomotopyCategory := bridge.boundedHomotopyCategory
  toBoundedHomotopy := bridge.toBoundedHomotopy
  fromBoundedHomotopy := bridge.fromBoundedHomotopy
  splitWeightTriangleWitness := bridge.splitWeightTriangleWitness
  objectDecompositionWitness := bridge.objectDecompositionWitness
  transportLeftInverse := bridge.transportLeftInverse
  transportRightInverse := bridge.transportRightInverse

end SplitWeightDecompositionStep

/-- Step 5: semisimplicity upgrades the bounded homotopy category of the pure
heart to the bounded derived category. -/
structure SemisimpleDerivedTransportStep
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {weightStructure : WeightStructureTarget structuralRecognition}
    (pureHeart : TracePureWeightHeart weightStructure)
    {indexedWeightClasses : IndexedWeightClassSystem weightStructure}
    {vanishing : PureHeartFullVanishingStep pureHeart}
    {coneRange : PureHeartConeWeightRangeStep indexedWeightClasses pureHeart vanishing}
    {semisimple :
      PureHeartSemisimpleAbelianStep indexedWeightClasses pureHeart vanishing coneRange}
    (splitWeight : SplitWeightDecompositionStep pureHeart semisimple) where
  boundedDerivedCategory : Type u
  homotopyToDerived :
    splitWeight.boundedHomotopyCategory → boundedDerivedCategory
  derivedToHomotopy :
    boundedDerivedCategory → splitWeight.boundedHomotopyCategory
  localizationWitness :
    splitWeight.boundedHomotopyCategory → Type z
  localizationLeftInverse :
    ∀ K : splitWeight.boundedHomotopyCategory,
      derivedToHomotopy (homotopyToDerived K) = K
  localizationRightInverse :
    ∀ D : boundedDerivedCategory,
      homotopyToDerived (derivedToHomotopy D) = D

namespace SemisimpleDerivedTransportStep

/-- Manuscript-sourced bridge for Step 5, matching the semisimple-localization
equivalence `K^b(H_w) ≃ D^b(H_w)`. -/
structure FromSemisimpleLocalizationBridge
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {weightStructure : WeightStructureTarget structuralRecognition}
    (pureHeart : TracePureWeightHeart weightStructure)
    {indexedWeightClasses : IndexedWeightClassSystem weightStructure}
    {vanishing : PureHeartFullVanishingStep pureHeart}
    {coneRange : PureHeartConeWeightRangeStep indexedWeightClasses pureHeart vanishing}
    {semisimple :
      PureHeartSemisimpleAbelianStep indexedWeightClasses pureHeart vanishing coneRange}
    (splitWeight : SplitWeightDecompositionStep pureHeart semisimple) where
  boundedDerivedCategory : Type u
  homotopyToDerived : splitWeight.boundedHomotopyCategory → boundedDerivedCategory
  derivedToHomotopy : boundedDerivedCategory → splitWeight.boundedHomotopyCategory
  localizationWitness : splitWeight.boundedHomotopyCategory → Type z
  localizationLeftInverse :
    ∀ K : splitWeight.boundedHomotopyCategory,
      derivedToHomotopy (homotopyToDerived K) = K
  localizationRightInverse :
    ∀ D : boundedDerivedCategory,
      homotopyToDerived (derivedToHomotopy D) = D

def ofSemisimpleLocalizationBridge
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {weightStructure : WeightStructureTarget structuralRecognition}
    {pureHeart : TracePureWeightHeart weightStructure}
    {indexedWeightClasses : IndexedWeightClassSystem weightStructure}
    {vanishing : PureHeartFullVanishingStep pureHeart}
    {coneRange : PureHeartConeWeightRangeStep indexedWeightClasses pureHeart vanishing}
    {semisimple :
      PureHeartSemisimpleAbelianStep indexedWeightClasses pureHeart vanishing coneRange}
    {splitWeight : SplitWeightDecompositionStep pureHeart semisimple}
    (bridge : FromSemisimpleLocalizationBridge pureHeart splitWeight) :
    SemisimpleDerivedTransportStep pureHeart splitWeight where
  boundedDerivedCategory := bridge.boundedDerivedCategory
  homotopyToDerived := bridge.homotopyToDerived
  derivedToHomotopy := bridge.derivedToHomotopy
  localizationWitness := bridge.localizationWitness
  localizationLeftInverse := bridge.localizationLeftInverse
  localizationRightInverse := bridge.localizationRightInverse

end SemisimpleDerivedTransportStep

/-- Step 6: transport the standard bounded `t`-structure on the bounded derived
category of the pure heart back to the trace category. -/
structure InternalTransportedTStructureStep
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {weightStructure : WeightStructureTarget structuralRecognition}
    (pureHeart : TracePureWeightHeart weightStructure)
    {indexedWeightClasses : IndexedWeightClassSystem weightStructure}
    {vanishing : PureHeartFullVanishingStep pureHeart}
    {coneRange : PureHeartConeWeightRangeStep indexedWeightClasses pureHeart vanishing}
    {semisimple :
      PureHeartSemisimpleAbelianStep indexedWeightClasses pureHeart vanishing coneRange}
    {splitWeight : SplitWeightDecompositionStep pureHeart semisimple}
    (derivedTransport : SemisimpleDerivedTransportStep pureHeart splitWeight) where
  derivedNonpositive : derivedTransport.boundedDerivedCategory → Prop
  derivedNonnegative : derivedTransport.boundedDerivedCategory → Prop
  traceTStructure : TraceMotivicTStructureData structuralRecognition
  standardTransportWitness :
    TraceMotivicTStructureData.normalization_compatibility_statement traceTStructure ∧
      TraceMotivicTStructureData.normalization_truncation_triangle_statement traceTStructure ∧
      TraceMotivicTStructureData.truncation_functoriality_statement traceTStructure
  theoremPackage :
    NormTStructureTheoremPackage traceTStructure traceTStructure.packetCut

namespace InternalTransportedTStructureStep

/-- Manuscript-sourced bridge for Step 6, matching transport of the standard
bounded `t`-structure from `D^b(H_w)` together with representability of
truncation. -/
structure FromDerivedTransportBridge
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {weightStructure : WeightStructureTarget structuralRecognition}
    (pureHeart : TracePureWeightHeart weightStructure)
    {indexedWeightClasses : IndexedWeightClassSystem weightStructure}
    {vanishing : PureHeartFullVanishingStep pureHeart}
    {coneRange : PureHeartConeWeightRangeStep indexedWeightClasses pureHeart vanishing}
    {semisimple :
      PureHeartSemisimpleAbelianStep indexedWeightClasses pureHeart vanishing coneRange}
    {splitWeight : SplitWeightDecompositionStep pureHeart semisimple}
    (derivedTransport : SemisimpleDerivedTransportStep pureHeart splitWeight) where
  derivedNonpositive : derivedTransport.boundedDerivedCategory → Prop
  derivedNonnegative : derivedTransport.boundedDerivedCategory → Prop
  traceTStructure : TraceMotivicTStructureData structuralRecognition
  standardTransportWitness :
    TraceMotivicTStructureData.normalization_compatibility_statement traceTStructure ∧
      TraceMotivicTStructureData.normalization_truncation_triangle_statement traceTStructure ∧
      TraceMotivicTStructureData.truncation_functoriality_statement traceTStructure
  theoremPackage :
    NormTStructureTheoremPackage traceTStructure traceTStructure.packetCut

def ofDerivedTransportBridge
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {weightStructure : WeightStructureTarget structuralRecognition}
    {pureHeart : TracePureWeightHeart weightStructure}
    {indexedWeightClasses : IndexedWeightClassSystem weightStructure}
    {vanishing : PureHeartFullVanishingStep pureHeart}
    {coneRange : PureHeartConeWeightRangeStep indexedWeightClasses pureHeart vanishing}
    {semisimple :
      PureHeartSemisimpleAbelianStep indexedWeightClasses pureHeart vanishing coneRange}
    {splitWeight : SplitWeightDecompositionStep pureHeart semisimple}
    {derivedTransport : SemisimpleDerivedTransportStep pureHeart splitWeight}
    (bridge : FromDerivedTransportBridge pureHeart derivedTransport) :
    InternalTransportedTStructureStep pureHeart derivedTransport where
  derivedNonpositive := bridge.derivedNonpositive
  derivedNonnegative := bridge.derivedNonnegative
  traceTStructure := bridge.traceTStructure
  standardTransportWitness := bridge.standardTransportWitness
  theoremPackage := bridge.theoremPackage

end InternalTransportedTStructureStep

/-- Step 7: the heart of the transported bounded `t`-structure agrees with the
internal pure heart. -/
structure PureHeartIdentifiesTransportedHeartStep
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {weightStructure : WeightStructureTarget structuralRecognition}
    (pureHeart : TracePureWeightHeart weightStructure)
    {indexedWeightClasses : IndexedWeightClassSystem weightStructure}
    {vanishing : PureHeartFullVanishingStep pureHeart}
    {coneRange : PureHeartConeWeightRangeStep indexedWeightClasses pureHeart vanishing}
    {semisimple :
      PureHeartSemisimpleAbelianStep indexedWeightClasses pureHeart vanishing coneRange}
    {splitWeight : SplitWeightDecompositionStep pureHeart semisimple}
    {derivedTransport : SemisimpleDerivedTransportStep pureHeart splitWeight}
    (transportedTStructure :
      InternalTransportedTStructureStep pureHeart derivedTransport) where
  pureHeartToTraceHeart :
    pureHeart.heartObject →
      (TraceMotivicHeart.ofTStructure transportedTStructure.traceTStructure).heartObject
  traceHeartToPureHeart :
    (TraceMotivicHeart.ofTStructure transportedTStructure.traceTStructure).heartObject →
      pureHeart.heartObject
  leftInverse :
    ∀ obj : pureHeart.heartObject,
      traceHeartToPureHeart (pureHeartToTraceHeart obj) = obj
  rightInverse :
    ∀ obj :
      (TraceMotivicHeart.ofTStructure transportedTStructure.traceTStructure).heartObject,
      pureHeartToTraceHeart (traceHeartToPureHeart obj) = obj

/-- Step 8: agreement of the internally constructed bounded `t`-structure with
the classical comparison-recognized MM(Q) heart and its transport package. -/
structure ComparisonTransportAgreementStep
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {weightStructure : WeightStructureTarget structuralRecognition}
    (pureHeart : TracePureWeightHeart weightStructure)
    {indexedWeightClasses : IndexedWeightClassSystem weightStructure}
    {vanishing : PureHeartFullVanishingStep pureHeart}
    {coneRange : PureHeartConeWeightRangeStep indexedWeightClasses pureHeart vanishing}
    {semisimple :
      PureHeartSemisimpleAbelianStep indexedWeightClasses pureHeart vanishing coneRange}
    {splitWeight : SplitWeightDecompositionStep pureHeart semisimple}
    {derivedTransport : SemisimpleDerivedTransportStep pureHeart splitWeight}
    (transportedTStructure :
      InternalTransportedTStructureStep pureHeart derivedTransport) where
  components :
    TraceMotivicTStructureComponentTheorems transportedTStructure.traceTStructure
  infrastructure :
    TStructureMotivicMMQInfrastructure
      transportedTStructure.traceTStructure
      (TraceMotivicHeart.ofTStructure transportedTStructure.traceTStructure)

namespace ComparisonTransportAgreementStep

def classicalHeartTheorems
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {weightStructure : WeightStructureTarget structuralRecognition}
    {pureHeart : TracePureWeightHeart weightStructure}
    {indexedWeightClasses : IndexedWeightClassSystem weightStructure}
    {vanishing : PureHeartFullVanishingStep pureHeart}
    {coneRange : PureHeartConeWeightRangeStep indexedWeightClasses pureHeart vanishing}
    {semisimple :
      PureHeartSemisimpleAbelianStep indexedWeightClasses pureHeart vanishing coneRange}
    {splitWeight : SplitWeightDecompositionStep pureHeart semisimple}
    {derivedTransport : SemisimpleDerivedTransportStep pureHeart splitWeight}
    {transportedTStructure : InternalTransportedTStructureStep pureHeart derivedTransport}
    (step : ComparisonTransportAgreementStep pureHeart transportedTStructure) :
    ClassicalMMQHeartTheorems
      transportedTStructure.traceTStructure
      (TraceMotivicHeart.ofTStructure transportedTStructure.traceTStructure) :=
  ClassicalMMQHeartTheorems.ofTStructureComponentTheorems
    transportedTStructure.traceTStructure
    step.components
    step.infrastructure

def recognizesClassicalMMQ
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {weightStructure : WeightStructureTarget structuralRecognition}
    {pureHeart : TracePureWeightHeart weightStructure}
    {indexedWeightClasses : IndexedWeightClassSystem weightStructure}
    {vanishing : PureHeartFullVanishingStep pureHeart}
    {coneRange : PureHeartConeWeightRangeStep indexedWeightClasses pureHeart vanishing}
    {semisimple :
      PureHeartSemisimpleAbelianStep indexedWeightClasses pureHeart vanishing coneRange}
    {splitWeight : SplitWeightDecompositionStep pureHeart semisimple}
    {derivedTransport : SemisimpleDerivedTransportStep pureHeart splitWeight}
    {transportedTStructure : InternalTransportedTStructureStep pureHeart derivedTransport}
    (step : ComparisonTransportAgreementStep pureHeart transportedTStructure) :
    RecognizesClassicalMMQ
      transportedTStructure.traceTStructure
      (TraceMotivicHeart.ofTStructure transportedTStructure.traceTStructure) :=
  (step.classicalHeartTheorems).traceHeart_recognizes_classical_MMQ

end ComparisonTransportAgreementStep

/-- Explicit eight-step internal construction route for the bounded motivic
`t`-structure and the MM(Q) recognition theorem.

This is the repository-native formalization of the internal argument:

1. full shifted-Hom vanishing on the internal pure heart;
2. cone weight range for pure-heart morphisms;
3. semisimple abelian pure heart;
4. splitting of weight decompositions and exact equivalence with `K^b`;
5. semisimplicity upgrade from `K^b` to `D^b`;
6. transport of the standard bounded `t`-structure from `D^b`;
7. identification of the transported heart with the pure heart;
8. agreement with the classical comparison-recognized MM(Q) heart.

The earlier packet-cut construction remains valuable as the normalization /
weight / orthogonality input, but this structure records the mathematically
correct provenance of the final bounded `t`-structure. -/
structure InternalSemisimplePureHeartTStructureConstruction
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}) where
  weightStructure : WeightStructureTarget structuralRecognition
  indexedWeightClasses : IndexedWeightClassSystem weightStructure
  pureHeart : TracePureWeightHeart weightStructure
  fullVanishing : PureHeartFullVanishingStep pureHeart
  coneWeightRange :
    PureHeartConeWeightRangeStep indexedWeightClasses pureHeart fullVanishing
  semisimpleAbelian :
    PureHeartSemisimpleAbelianStep
      indexedWeightClasses
      pureHeart
      fullVanishing
      coneWeightRange
  splitWeightDecomposition :
    SplitWeightDecompositionStep pureHeart semisimpleAbelian
  derivedTransport :
    SemisimpleDerivedTransportStep pureHeart splitWeightDecomposition
  transportedTStructure :
    InternalTransportedTStructureStep pureHeart derivedTransport
  pureHeartIdentification :
    PureHeartIdentifiesTransportedHeartStep pureHeart transportedTStructure
  comparisonAgreement :
    ComparisonTransportAgreementStep pureHeart transportedTStructure

namespace InternalSemisimplePureHeartTStructureConstruction

def traceTStructure
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (construction : InternalSemisimplePureHeartTStructureConstruction structuralRecognition) :
    TraceMotivicTStructureData structuralRecognition :=
  construction.transportedTStructure.traceTStructure

def normTStructureTheoremPackage
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (construction : InternalSemisimplePureHeartTStructureConstruction structuralRecognition) :
    NormTStructureTheoremPackage
      construction.transportedTStructure.traceTStructure
      construction.transportedTStructure.traceTStructure.packetCut :=
  construction.transportedTStructure.theoremPackage

def classicalHeartTheorems
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (construction : InternalSemisimplePureHeartTStructureConstruction structuralRecognition) :
    ClassicalMMQHeartTheorems
      construction.transportedTStructure.traceTStructure
      (TraceMotivicHeart.ofTStructure construction.transportedTStructure.traceTStructure) :=
  construction.comparisonAgreement.classicalHeartTheorems

def recognizesClassicalMMQ
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (construction : InternalSemisimplePureHeartTStructureConstruction structuralRecognition) :
    RecognizesClassicalMMQ
      construction.transportedTStructure.traceTStructure
      (TraceMotivicHeart.ofTStructure construction.transportedTStructure.traceTStructure) :=
  construction.comparisonAgreement.recognizesClassicalMMQ

end InternalSemisimplePureHeartTStructureConstruction

/-- Combined theorem-target package for the canonical weight structure and
Campaign 12B normalization-induced `t`-structure, explicitly downstream of
structural recognition. -/
structure MotivicTStructurePackage where
  structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}
  weightStructure : WeightStructureTarget structuralRecognition
  traceMotivicTStructure : TraceMotivicTStructureData structuralRecognition
  tStructure : TStructureTarget structuralRecognition
  heart : HeartCandidate structuralRecognition
  abelianHeart : AbelianHeartTarget heart
  mmqHeart : MMQHeartTarget abelianHeart
  weightTStructureCompatibilityTarget : Prop
  heartRealizationCompatibilityTarget : Prop

/-- Exact remaining Campaign 12B normalization theorem surface: the canonical
threshold cut on the normalized packet DAG is admissible and reconstructible. -/
structure CanonicalPacketCutIsAdmissible
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    (traceNative :
      TraceNativeWeightDevissageData structuralRecognition traceCategory assignmentTable closure
        compactGenerationTransport)
    (threshold : Nat) where
  thresholdLe : threshold ≤ traceNative.reconstructionLength
  canonicalCut :
    (packet : LegacyCompletedRecord traceNative.reconstructionLength) →
      LegacyCanonicalThresholdCut packet threshold
  lowerPacketSubset :
    LegacyCompletedRecord traceNative.reconstructionLength → Type z
  upperPacketSubset :
    LegacyCompletedRecord traceNative.reconstructionLength → Type z
  canonicalThresholdCut :
    CanonicalThresholdCutData
      (fun _ : LegacyCompletedRecord traceNative.reconstructionLength => Fin traceNative.reconstructionLength)
      (fun _ degree => Int.ofNat degree.val)
      (fun _ degree => NatLtWitness degree.val threshold)
      (fun _ degree => NatLeWitness threshold degree.val)
  boundaryDependencyClosure :
    BoundaryDependencyClosureData
      (fun _ : LegacyCompletedRecord traceNative.reconstructionLength => Fin traceNative.reconstructionLength)
      (fun _ degree => NatLtWitness degree.val threshold)
  lowerCutAdmissibility :
    LowerCutAdmissibilityData
      (fun _ : LegacyCompletedRecord traceNative.reconstructionLength => Fin traceNative.reconstructionLength)
      (fun _ degree => Int.ofNat degree.val)
      (fun _ degree => NatLtWitness degree.val threshold)
  gluingClosure :
    GluingClosureData
      (fun _ : LegacyCompletedRecord traceNative.reconstructionLength => Fin traceNative.reconstructionLength)
      (fun _ degree => NatLeWitness threshold degree.val)
  upperCutAdmissibility :
    UpperCutAdmissibilityData
      (fun _ : LegacyCompletedRecord traceNative.reconstructionLength => Fin traceNative.reconstructionLength)
      (fun _ degree => Int.ofNat degree.val)
      (fun _ degree => NatLtWitness degree.val threshold)
      (fun _ degree => NatLeWitness threshold degree.val)

namespace CanonicalPacketCutIsAdmissible

def ofCompletedRecordThreshold
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    (traceNative :
      TraceNativeWeightDevissageData structuralRecognition traceCategory assignmentTable closure
        compactGenerationTransport)
    (threshold : Nat)
    (hThreshold : threshold ≤ traceNative.reconstructionLength) :
    CanonicalPacketCutIsAdmissible traceNative threshold where
  thresholdLe := hThreshold
  canonicalCut := fun packet =>
    completedRecordThresholdCut packet hThreshold
  lowerPacketSubset := fun _ =>
    ULift (LegacyCompletedRecord threshold)
  upperPacketSubset := fun _ =>
    ULift
      (LegacyCompletedRecord (traceNative.reconstructionLength - threshold))
  canonicalThresholdCut :=
    { cutoff := Int.ofNat threshold
      lower_of_degree_lt := by
        intro X degree hDegree
        exact ⟨Int.ofNat_lt.mp hDegree⟩
      lower_degree_bound := by
        intro X degree hLower
        exact Int.ofNat_lt.mpr hLower.lt_proof
      upper_of_cutoff_le := by
        intro X degree hDegree
        exact ⟨Int.ofNat_le.mp hDegree⟩
      upper_cutoff_bound := by
        intro X degree hUpper
        exact Int.ofNat_le.mpr hUpper.le_proof }
  boundaryDependencyClosure :=
    { dependencyEdge := fun packet sourcePacket targetPacket =>
        PLift (sourcePacket ∈ packet.requires targetPacket)
      lower_closed_under_dependencies := by
        intro packet sourcePacket targetPacket hEdge hLower
        have hTargetLower :
            targetPacket ∈
              (completedRecordThresholdCut packet hThreshold).lowerSet := by
          exact (completedRecordThresholdCut_lower_mem_iff packet hThreshold targetPacket).2 hLower.lt_proof
        have hSourceLower :=
          completedRecordThresholdCut_lower_dependency_closed packet hThreshold hTargetLower
            hEdge.down
        exact ⟨(completedRecordThresholdCut_lower_mem_iff packet hThreshold sourcePacket).1 hSourceLower⟩ }
  lowerCutAdmissibility :=
    { cutoff := Int.ofNat threshold
      lower_cut_degree := by
        intro X degree hLower
        exact Int.ofNat_lt.mpr hLower.lt_proof }
  gluingClosure :=
    { gluePacket := fun degree _ => degree
      glue_preserves_upper := by
        intro X degree hUpper
        simpa using hUpper }
  upperCutAdmissibility :=
    { cutoff := Int.ofNat threshold
      upper_cut_degree := by
        intro X degree hUpper
        exact Int.ofNat_le.mpr hUpper.le_proof
      cut_partition := by
        intro X degree
        by_cases hLower : degree.val < threshold
        · exact Sum.inl ⟨hLower⟩
        · exact Sum.inr ⟨Nat.le_of_not_gt hLower⟩
      cut_disjoint := by
        intro X degree hLower hUpper
        exact Nat.not_lt.mpr hUpper.le_proof hLower.lt_proof }

end CanonicalPacketCutIsAdmissible

/-- Exact remaining Campaign 12B truncation theorem surface: the cofiber of the
canonical lower cut realizes the upper truncation object. -/
structure CanonicalCutCofiberIdentifiesUpperTruncation
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z})
    (packetCut : NormalizationPacketCutData structuralRecognition) where
  lowerTruncationCarrier :
    structuralRecognition.recognition.recognizedCategory.Object → Type z
  upperTruncationCarrier :
    structuralRecognition.recognition.recognizedCategory.Object → Type z
  totalObject :
    structuralRecognition.recognition.recognizedCategory.Object →
      structuralRecognition.recognition.recognizedCategory.Object
  lowerTruncationObject :
    structuralRecognition.recognition.recognizedCategory.Object →
      structuralRecognition.recognition.recognizedCategory.Object
  upperTruncationObject :
    structuralRecognition.recognition.recognizedCategory.Object →
      structuralRecognition.recognition.recognizedCategory.Object
  lowerInclusion :
    (X : structuralRecognition.recognition.recognizedCategory.Object) →
      structuralRecognition.recognition.recognizedCategory.Hom
        (lowerTruncationObject X)
        (totalObject X)
  upperProjection :
    (X : structuralRecognition.recognition.recognizedCategory.Object) →
      structuralRecognition.recognition.recognizedCategory.Hom
        (totalObject X)
        (upperTruncationObject X)
  cofiberSequenceWitness :
    structuralRecognition.recognition.recognizedCategory.Object → Type z
  cofiberIdentifiesUpper :
    structuralRecognition.recognition.recognizedCategory.Object → Prop
  lowerCutRealization :
    LowerCutRealizationData structuralRecognition packetCut
      lowerTruncationCarrier lowerTruncationObject
  upperCutCofiberRealization :
    UpperCutCofiberRealizationData structuralRecognition packetCut
      upperTruncationCarrier upperTruncationObject cofiberSequenceWitness cofiberIdentifiesUpper
  canonicalInclusion :
    CanonicalInclusionData structuralRecognition packetCut
      lowerTruncationCarrier totalObject lowerTruncationObject lowerInclusion
  truncationTriangle :
    TruncationTriangleWitnessData structuralRecognition
      lowerTruncationObject totalObject upperTruncationObject lowerInclusion upperProjection
  cofiberIdentifiesUpperCut :
    CofiberIdentifiesUpperCutData structuralRecognition packetCut
      upperTruncationObject cofiberSequenceWitness cofiberIdentifiesUpper
  truncationFunctoriality :
    TruncationFunctorialityData structuralRecognition
      lowerTruncationObject upperTruncationObject

namespace NormalizationPacketCutData

def canonicalAdmissibleCut
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    (traceNative :
      TraceNativeWeightDevissageData structuralRecognition traceCategory assignmentTable closure
        compactGenerationTransport)
    (threshold : Nat)
    (hThreshold : threshold ≤ traceNative.reconstructionLength) :
    CanonicalPacketCutIsAdmissible traceNative threshold :=
  CanonicalPacketCutIsAdmissible.ofCompletedRecordThreshold traceNative threshold hThreshold

structure FromTraceNativeWeightDevissageBridge
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    (traceNative :
      TraceNativeWeightDevissageData structuralRecognition traceCategory assignmentTable closure
        compactGenerationTransport)
    (threshold : Nat)
    (admissibleCut : CanonicalPacketCutIsAdmissible traceNative threshold) where
  packetSupportBelowThreshold_weightClassNonpositive :
    ∀ (X : structuralRecognition.recognition.recognizedCategory.Object)
      (sourcePacket : ULift (Fin traceNative.reconstructionLength))
      (n : Int),
      Int.ofNat sourcePacket.down.val ≤ n →
        traceNative.weightClasses.weightClassNonpositive X
  packetSupportAboveThreshold_weightClassNonnegative :
    ∀ (Y : structuralRecognition.recognition.recognizedCategory.Object)
      (targetPacket : ULift (Fin traceNative.reconstructionLength))
      (n : Int),
      n < Int.ofNat targetPacket.down.val →
        traceNative.weightClasses.weightClassNonnegative Y

abbrev CanonicalCutBridge
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    (traceNative :
      TraceNativeWeightDevissageData structuralRecognition traceCategory assignmentTable closure
        compactGenerationTransport)
    (threshold : Nat)
    (hThreshold : threshold ≤ traceNative.reconstructionLength) :=
  FromTraceNativeWeightDevissageBridge traceNative threshold
    (canonicalAdmissibleCut traceNative threshold hThreshold)

noncomputable def ofTraceNativeWeightDevissage
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    (traceNative :
      TraceNativeWeightDevissageData structuralRecognition traceCategory assignmentTable closure
        compactGenerationTransport)
    {threshold : Nat}
    (admissibleCut : CanonicalPacketCutIsAdmissible traceNative threshold)
    (bridge : FromTraceNativeWeightDevissageBridge traceNative threshold admissibleCut) :
    NormalizationPacketCutData structuralRecognition where
  packetRecord := fun _ => ULift (Fin traceNative.reconstructionLength)
  packetDegree := fun _ packet => Int.ofNat packet.down.val
  PacketHom := fun {X Y} _ _ => structuralRecognition.recognition.recognizedCategory.Hom X Y
  packetHomUnderlying := fun packetHom => packetHom
  IsZeroPacketHom := fun {X Y} {sourcePacket} {targetPacket} packetHom =>
    ∃ (n : Int)
      (hSource : Int.ofNat sourcePacket.down.val ≤ n)
      (hTarget : n < Int.ofNat targetPacket.down.val),
        traceNative.weightOrthogonality.traceDevissageZeroWitnessTarget
          (traceNative.weightOrthogonality.separatedWeightWitness
            (bridge.packetSupportBelowThreshold_weightClassNonpositive X sourcePacket n hSource)
            (bridge.packetSupportAboveThreshold_weightClassNonnegative Y targetPacket n hTarget))
          packetHom
  packetZeroTransports := by
    intro X Y sourcePacket targetPacket packetHom _hZero
    exact
      { isZero :=
          ∃ (n : Int)
            (hSource : Int.ofNat sourcePacket.down.val ≤ n)
            (hTarget : n < Int.ofNat targetPacket.down.val),
              traceNative.weightOrthogonality.traceDevissageZeroWitnessTarget
                (traceNative.weightOrthogonality.separatedWeightWitness
                  (bridge.packetSupportBelowThreshold_weightClassNonpositive X sourcePacket n hSource)
                  (bridge.packetSupportAboveThreshold_weightClassNonnegative Y targetPacket n hTarget))
                packetHom }
  packetDegreeRefinement :=
    (show PacketDegreeRefinementData
        (fun _ : structuralRecognition.recognition.recognizedCategory.Object =>
          ULift.{z, 0} (Fin traceNative.reconstructionLength))
        (fun _ packet => Int.ofNat packet.down.val) from
    { RefinedPacketIndex := fun _ => ULift.{z, 0} (Fin traceNative.reconstructionLength)
      refinedToPacket := fun _ index => index
      refinedDegree := fun _ index => Int.ofNat index.down.val
      degree_compatible := by
        intro X i
        rfl
      packet_covered := by
        intro X p
        exact ⟨p, rfl⟩ })
  packetDegreeShift :=
    (show PacketDegreeShiftData
        (fun _ : structuralRecognition.recognition.recognizedCategory.Object =>
          ULift.{z, 0} (Fin traceNative.reconstructionLength))
        (fun _ packet => Int.ofNat packet.down.val) from
    { ShiftStep := fun _ p q => NatStepWitness p.down.val q.down.val
      shift_degree := by
        intro X p q hStep
        have hEq : q.down.val = p.down.val + 1 := hStep.eq_succ
        calc
          Int.ofNat q.down.val = Int.ofNat (p.down.val + 1) := by simp [hEq]
          _ = Int.ofNat p.down.val + 1 := by simp [Int.ofNat_add] })
  finitePacketAmplitude :=
    (show FinitePacketAmplitudeData
        (fun _ : structuralRecognition.recognition.recognizedCategory.Object =>
          ULift.{z, 0} (Fin traceNative.reconstructionLength))
        (fun _ packet => Int.ofNat packet.down.val) from
    { lowerBound := fun _ => 0
      upperBound := fun _ => Int.ofNat traceNative.reconstructionLength
      lower_bound := by
        intro X p
        simpa using Int.ofNat_nonneg p.down.val
      upper_bound := by
        intro X p
        exact Int.ofNat_le.mpr (Nat.le_of_lt p.down.isLt) })
  lowerCutRecord := fun _ packet => NatLtWitness packet.down.val threshold
  upperCutRecord := fun _ packet => NatLeWitness threshold packet.down.val
  finiteDegreeLabeledPacketDAG :=
    (show FiniteDegreeLabeledPacketDAGData
        (fun _ : structuralRecognition.recognition.recognizedCategory.Object =>
          ULift.{z, 0} (Fin traceNative.reconstructionLength))
        (fun _ packet => Int.ofNat packet.down.val) from
    { Edge := fun _ p q => NatLeWitness p.down.val q.down.val
      edge_degree_mono := by
        intro X p q hEdge
        exact Int.ofNat_le.mpr hEdge.le_proof
      finitePacketIndex := fun _ => ULift.{z, 0} (Fin traceNative.reconstructionLength)
      finitePacketIndexToPacket := fun _ index => index
      packetCovered := by
        intro X p
        exact ⟨p, rfl⟩ })
  separatedDegreePacketVanishing := by
    intro X Y sourcePacket targetPacket packetHom n hSource hTarget
    exact ⟨n, hSource, hTarget,
      traceNative.weightOrthogonality.traceDevissageZeroWitness_holds
        (traceNative.weightOrthogonality.separatedWeightWitness
          (bridge.packetSupportBelowThreshold_weightClassNonpositive X sourcePacket n hSource)
          (bridge.packetSupportAboveThreshold_weightClassNonnegative Y targetPacket n hTarget))
        packetHom⟩
  recognizedHomPacketComponent := by
    intro X Y sourcePacket targetPacket f
    exact f
  packetComponentsDetectZero := by
    intro X Y f sourceSupports targetSupports sourceSupportWitness targetSupportWitness componentVanishes
    let sourcePacket := sourceSupportWitness.1
    let targetPacket := targetSupportWitness.1
    have hSourcePacket : sourceSupports sourcePacket := sourceSupportWitness.2
    have hTargetPacket : targetSupports targetPacket := targetSupportWitness.2
    exact
      { isZero :=
          ∃ (n : Int)
            (hSource : Int.ofNat sourcePacket.down.val ≤ n)
            (hTarget : n < Int.ofNat targetPacket.down.val),
              traceNative.weightOrthogonality.traceDevissageZeroWitnessTarget
                (traceNative.weightOrthogonality.separatedWeightWitness
                  (bridge.packetSupportBelowThreshold_weightClassNonpositive X sourcePacket n hSource)
                  (bridge.packetSupportAboveThreshold_weightClassNonnegative Y targetPacket n hTarget))
                f }
  canonicalThresholdCut :=
    { cutoff := Int.ofNat threshold
      lower_of_degree_lt := by
        intro X packet hPacket
        exact ⟨Int.ofNat_lt.mp hPacket⟩
      lower_degree_bound := by
        intro X packet hLower
        exact Int.ofNat_lt.mpr hLower.lt_proof
      upper_of_cutoff_le := by
        intro X packet hPacket
        exact ⟨Int.ofNat_le.mp hPacket⟩
      upper_cutoff_bound := by
        intro X packet hUpper
        exact Int.ofNat_le.mpr hUpper.le_proof }
  lowerCutAdmissibility :=
    { cutoff := Int.ofNat threshold
      lower_cut_degree := by
        intro X packet hLower
        exact Int.ofNat_lt.mpr hLower.lt_proof }
  upperCutAdmissibility :=
    { cutoff := Int.ofNat threshold
      upper_cut_degree := by
        intro X packet hUpper
        exact Int.ofNat_le.mpr hUpper.le_proof
      cut_partition := by
        intro X packet
        by_cases hLt : packet.down.val < threshold
        · exact Sum.inl ⟨hLt⟩
        · exact Sum.inr ⟨Nat.ge_of_not_lt hLt⟩
      cut_disjoint := by
        intro X packet hLower hUpper
        exact Nat.not_lt_of_ge hUpper.le_proof hLower.lt_proof }
  boundaryDependencyClosure :=
    { dependencyEdge := fun _ sourcePacket targetPacket => NatLeWitness sourcePacket.down.val targetPacket.down.val
      lower_closed_under_dependencies := by
        intro X sourcePacket targetPacket hEdge hLower
        exact ⟨lt_of_le_of_lt hEdge.le_proof hLower.lt_proof⟩ }
  gluingClosure :=
    { gluePacket := fun packet _ => packet
      glue_preserves_upper := by
        intro X packet hUpper
        exact hUpper }
  canonicalReconstructionCompatibility :=
    { reconstructPacket := fun packet => packet
      reconstruction_preserves_degree := by
        intro X packet
        rfl }
  campaign11WeightDevissageCompatibility :=
    { weightIndex := fun packet => Int.ofNat packet.down.val
      weight_matches_packet_degree := by
        intro X packet
        rfl }

noncomputable def ofCanonicalReconstructionAndWeights
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    (traceNative :
      TraceNativeWeightDevissageData structuralRecognition traceCategory assignmentTable closure
        compactGenerationTransport)
    (threshold : Nat)
    (hThreshold : threshold ≤ traceNative.reconstructionLength)
    (bridge : CanonicalCutBridge traceNative threshold hThreshold) :
    NormalizationPacketCutData structuralRecognition :=
  ofTraceNativeWeightDevissage traceNative
    (canonicalAdmissibleCut traceNative threshold hThreshold)
    bridge

end NormalizationPacketCutData

namespace TraceNativeWeightDevissageData

def canonicalPacketCutSeparatedZeroWitness
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    (traceNative :
      TraceNativeWeightDevissageData structuralRecognition traceCategory assignmentTable closure
        compactGenerationTransport)
    (threshold : Nat)
    (hThreshold : threshold ≤ traceNative.reconstructionLength)
    (f : structuralRecognition.recognition.recognizedCategory.Hom
      (TraceNativeWeightDevissageData.canonicalPacketCutLowerRecognizedObject
        traceNative (TraceNativeWeightDevissageData.canonicalPacketCut traceNative threshold hThreshold))
      (TraceNativeWeightDevissageData.canonicalPacketCutUpperRecognizedObject
        traceNative (TraceNativeWeightDevissageData.canonicalPacketCut traceNative threshold hThreshold))) :
    TraceMotivicZeroMorphismWitness structuralRecognition f :=
  { isZero :=
      traceNative.weightOrthogonality.traceDevissageZeroWitnessTarget
        (TraceNativeWeightDevissageData.canonicalPacketCutSeparatedWeightData
          traceNative
          (TraceNativeWeightDevissageData.canonicalPacketCut traceNative threshold hThreshold))
        f }

end TraceNativeWeightDevissageData

namespace CanonicalCutCofiberIdentifiesUpperTruncation

def ofCanonicalPacketCutSourceProofs
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    (traceNative :
      TraceNativeWeightDevissageData structuralRecognition traceCategory assignmentTable closure
        compactGenerationTransport)
    (threshold : Nat)
    (hThreshold : threshold ≤ traceNative.reconstructionLength)
    (packetCutBridge : NormalizationPacketCutData.CanonicalCutBridge
      traceNative threshold hThreshold) :
    CanonicalCutCofiberIdentifiesUpperTruncation structuralRecognition
      (NormalizationPacketCutData.ofCanonicalReconstructionAndWeights
        traceNative threshold hThreshold packetCutBridge) := by
  let admissibleCut :=
    NormalizationPacketCutData.canonicalAdmissibleCut traceNative threshold hThreshold
  let packetCut :=
    NormalizationPacketCutData.ofTraceNativeWeightDevissage traceNative admissibleCut packetCutBridge
  let canonicalCut := admissibleCut.canonicalCut traceNative.completedRecord
  change CanonicalCutCofiberIdentifiesUpperTruncation structuralRecognition packetCut
  refine {
    lowerTruncationCarrier := fun _ => admissibleCut.lowerPacketSubset traceNative.completedRecord
    upperTruncationCarrier := fun _ => admissibleCut.upperPacketSubset traceNative.completedRecord
    totalObject :=
      fun _ =>
        TraceNativeWeightDevissageData.canonicalPacketCutTotalRecognizedObject
          traceNative canonicalCut
    lowerTruncationObject :=
      fun _ =>
        TraceNativeWeightDevissageData.canonicalPacketCutLowerRecognizedObject
          traceNative canonicalCut
    upperTruncationObject :=
      fun _ =>
        TraceNativeWeightDevissageData.canonicalPacketCutUpperRecognizedObject
          traceNative canonicalCut
    lowerInclusion :=
      fun _ =>
        TraceNativeWeightDevissageData.canonicalPacketCutLowerInclusionRecognized
          traceNative canonicalCut
    upperProjection :=
      fun _ =>
        TraceNativeWeightDevissageData.canonicalPacketCutUpperProjectionRecognized
          traceNative canonicalCut
    cofiberSequenceWitness :=
      fun _ => ULift (TraceNativeWeightDevissageData.canonicalPacketCutCofiberSequenceData traceNative canonicalCut)
    cofiberIdentifiesUpper :=
      fun _ =>
        ∀ i : Fin (traceNative.reconstructionLength - threshold),
          canonicalCut.cofiberSequence.totalToUpper (canonicalCut.upperEmbedding i) = some i
    lowerCutRealization :=
      { lower_packets_compatible :=
          ⟨NormalizationPacketCutData.canonical_threshold_cut_statement_holds packetCut,
            NormalizationPacketCutData.lower_cut_admissibility_statement_holds packetCut,
            NormalizationPacketCutData.boundary_dependency_closure_statement_holds packetCut⟩ }
    upperCutCofiberRealization :=
      { upper_packets_compatible :=
          NormalizationPacketCutData.upper_cut_admissibility_statement_holds packetCut
        cofiber_sequence_data := by
          intro X
          exact ⟨canonicalCut.cofiberSequence⟩
        cofiber_agrees_with_upper := by
          intro X
          intro i
          exact canonicalCut.cofiberIdentifiesUpper i }
    canonicalInclusion :=
      { inclusion_matches_cut :=
          ⟨NormalizationPacketCutData.canonical_threshold_cut_statement_holds packetCut,
            NormalizationPacketCutData.lower_cut_admissibility_statement_holds packetCut⟩ }
    truncationTriangle :=
      { distinguished_triangle :=
          structuralRecognition.structuralPackage.triangulated.distinguishedTrianglesTarget
        tensor_triangle_compatibility :=
          structuralRecognition.structuralPackage.tensorExactness.triangleCompatibilityTarget }
    cofiberIdentifiesUpperCut :=
      { upper_cut_and_gluing_compatible :=
          ⟨NormalizationPacketCutData.upper_cut_admissibility_statement_holds packetCut,
            NormalizationPacketCutData.gluing_closure_statement_holds packetCut⟩
        cofiber_sequence_data := by
          intro X
          exact ⟨canonicalCut.cofiberSequence⟩
        cofiber_identifies_upper_cut := by
          intro X
          intro i
          exact canonicalCut.cofiberIdentifiesUpper i
        distinguished_triangle :=
          structuralRecognition.structuralPackage.triangulated.distinguishedTrianglesTarget
        cone_functoriality :=
          structuralRecognition.structuralPackage.triangulated.coneFunctorialityTarget
        tensor_triangle_compatibility :=
          structuralRecognition.structuralPackage.tensorExactness.triangleCompatibilityTarget }
    truncationFunctoriality :=
      { cone_functoriality :=
          structuralRecognition.structuralPackage.triangulated.coneFunctorialityTarget } }

end CanonicalCutCofiberIdentifiesUpperTruncation

/-- General Campaign 12C assembly surface for the standard fact that the heart
of a completed trace motivic `t`-structure is abelian. -/
structure HeartOfTraceTStructureIsAbelian
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition) where
  exactnessData :
    ∀ {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject},
      (morphism :
        TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
          sourceObject targetObject) →
        TraceMotivicHeartExactPackage (TraceMotivicHeart.ofTStructure tStructure) morphism
  kernelData : Type z
  cokernelData : Type z
  imageData : Type z
  coimageData : Type z
  imageCoimageComparison : Type z
  kernelTarget :
    ∀ {sourceObject targetObject}
      (morphism :
        TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
          sourceObject targetObject)
      (witness : (exactnessData morphism).ExactnessWitness),
        Type z
  cokernelTarget :
    ∀ {sourceObject targetObject}
      (morphism :
        TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
          sourceObject targetObject)
      (witness : (exactnessData morphism).ExactnessWitness),
        Type z
  imageCoimageTarget :
    ∀ {sourceObject targetObject}
      (morphism :
        TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
          sourceObject targetObject)
      (witness : (exactnessData morphism).ExactnessWitness),
        Type z
  abelianCategoryTarget :
    Type (z + 1)

namespace HeartOfTraceTStructureIsAbelian

def ofTransportedExactData
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (exactnessData :
      ∀ {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject},
        (morphism :
          TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
            sourceObject targetObject) →
          TraceMotivicHeartExactPackage (TraceMotivicHeart.ofTStructure tStructure) morphism) :
    HeartOfTraceTStructureIsAbelian tStructure where
  exactnessData := exactnessData
  kernelData :=
    Σ sourceObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject,
      Σ targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject,
        Σ morphism :
          TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
            sourceObject targetObject,
          (exactnessData morphism).ExactnessWitness
  cokernelData :=
    Σ sourceObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject,
      Σ targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject,
        Σ morphism :
          TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
            sourceObject targetObject,
          (exactnessData morphism).ExactnessWitness
  imageData :=
    Σ sourceObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject,
      Σ targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject,
        Σ morphism :
          TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
            sourceObject targetObject,
          (exactnessData morphism).ExactnessWitness
  coimageData :=
    Σ sourceObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject,
      Σ targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject,
        Σ morphism :
          TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
            sourceObject targetObject,
          (exactnessData morphism).ExactnessWitness
  imageCoimageComparison :=
    Σ sourceObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject,
      Σ targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject,
        Σ morphism :
          TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
            sourceObject targetObject,
          (exactnessData morphism).ExactnessWitness
  kernelTarget := by
    intro sourceObject targetObject morphism witness
    exact ((exactnessData morphism).realize witness).kernelWitness
  cokernelTarget := by
    intro sourceObject targetObject morphism witness
    exact ((exactnessData morphism).realize witness).cokernelWitness
  imageCoimageTarget := by
    intro sourceObject targetObject morphism witness
    exact ((exactnessData morphism).realize witness).imageWitness ×
      (((exactnessData morphism).realize witness).coimageWitness) ×
        ((exactnessData morphism).realize witness).imageCoimageComparisonWitness
  abelianCategoryTarget := by
    exact PUnit

def ofConstructiveExactnessSystem
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition)
    (system : TraceMotivicHeartConstructiveExactnessSystem tStructure) :
    HeartOfTraceTStructureIsAbelian tStructure :=
  let exactnessData :=
    fun {sourceObject targetObject}
      (morphism :
        TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
          sourceObject targetObject) =>
        TraceMotivicHeartExactPackage.heartExactPackage_from_recognizedFiberCofiber
          system morphism
  { exactnessData := exactnessData
    kernelData :=
      TraceMotivicHeartExactWitnessData (TraceMotivicHeart.ofTStructure tStructure)
        exactnessData
    cokernelData :=
      TraceMotivicHeartExactWitnessData (TraceMotivicHeart.ofTStructure tStructure)
        exactnessData
    imageData :=
      TraceMotivicHeartExactWitnessData (TraceMotivicHeart.ofTStructure tStructure)
        exactnessData
    coimageData :=
      TraceMotivicHeartExactWitnessData (TraceMotivicHeart.ofTStructure tStructure)
        exactnessData
    imageCoimageComparison :=
      TraceMotivicHeartExactWitnessData (TraceMotivicHeart.ofTStructure tStructure)
        exactnessData
    kernelTarget := by
        intro sourceObject targetObject morphism witness
        exact TraceMotivicHeartKernelWitness system morphism
    cokernelTarget := by
        intro sourceObject targetObject morphism witness
        exact TraceMotivicHeartCokernelWitness system morphism
    imageCoimageTarget := by
        intro sourceObject targetObject morphism witness
        exact TraceMotivicHeartImageWitness system morphism ×
          (TraceMotivicHeartCoimageWitness system morphism ×
            TraceMotivicHeartImageCoimageComparisonWitness system morphism)
    abelianCategoryTarget := by
        exact PUnit }

end HeartOfTraceTStructureIsAbelian

namespace NormalizationTruncationTriangle

def ofPacketCut
    {structuralRecognition :
      _root_.TraceCalc.MotivicRecognition.DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      _root_.TraceCalc.MotivicRecognition.FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    (traceNative :
      _root_.TraceCalc.MotivicRecognition.TraceNativeWeightDevissageData structuralRecognition
        traceCategory assignmentTable closure compactGenerationTransport)
    (packetCut : _root_.TraceCalc.MotivicRecognition.NormalizationPacketCutData structuralRecognition)
    (cofiberIdentification :
      _root_.TraceCalc.MotivicRecognition.CanonicalCutCofiberIdentifiesUpperTruncation
        structuralRecognition packetCut) :
    _root_.TraceCalc.MotivicRecognition.NormalizationTruncationTriangle structuralRecognition packetCut where
  lowerTruncationCarrier := cofiberIdentification.lowerTruncationCarrier
  upperTruncationCarrier := cofiberIdentification.upperTruncationCarrier
  totalObject := cofiberIdentification.totalObject
  lowerTruncationObject := cofiberIdentification.lowerTruncationObject
  upperTruncationObject := cofiberIdentification.upperTruncationObject
  lowerInclusion := cofiberIdentification.lowerInclusion
  upperProjection := cofiberIdentification.upperProjection
  cofiberSequenceWitness := cofiberIdentification.cofiberSequenceWitness
  cofiberIdentifiesUpper := cofiberIdentification.cofiberIdentifiesUpper
  lowerCutRealization := cofiberIdentification.lowerCutRealization
  upperCutCofiberRealization := cofiberIdentification.upperCutCofiberRealization
  canonicalInclusion := cofiberIdentification.canonicalInclusion
  truncationTriangle := cofiberIdentification.truncationTriangle
  cofiberIdentifiesUpperCut := cofiberIdentification.cofiberIdentifiesUpperCut
  truncationFunctoriality := cofiberIdentification.truncationFunctoriality
  orthogonalityFromSeparatedDegrees := by
    intro X Y sourcePacket targetPacket f hSource hTarget
    let sourceDegree := packetCut.packetDegree X sourcePacket
    have hSourceCutoff :
        sourceDegree < packetCut.canonicalThresholdCut.cutoff :=
      packetCut.canonicalThresholdCut.lower_degree_bound sourcePacket hSource
    have hTargetCutoff :
        packetCut.canonicalThresholdCut.cutoff ≤ packetCut.packetDegree Y targetPacket :=
      packetCut.canonicalThresholdCut.upper_cutoff_bound targetPacket hTarget
    have hSeparated :
        sourceDegree < packetCut.packetDegree Y targetPacket :=
      lt_of_lt_of_le hSourceCutoff hTargetCutoff
    exact
      _root_.TraceCalc.MotivicRecognition.orthogonality_from_hom_packet_decomposition
        packetCut.toHomPacketComponentData
        packetCut.toHomPacketExtensionality
        packetCut.toHomPacketSeparatedVanishing
        f
        (fun packet => packet = sourcePacket)
        (fun packet => packet = targetPacket)
        ⟨sourcePacket, rfl⟩
        ⟨targetPacket, rfl⟩
        (by
          intro packet hPacket
          cases hPacket
          exact le_rfl)
        (by
          intro packet hPacket
          cases hPacket
          exact Int.add_one_le_iff.mpr hSeparated)
  recognitionCompatibility :=
    { recognized_triangle_transport :=
        cofiberIdentification.truncationTriangle.distinguished_triangle }
  campaign11WeightDevissageCompatibility :=
    { packet_weight_compatibility :=
        NormalizationPacketCutData.campaign11_weight_devissage_compatibility_statement_holds packetCut }

noncomputable def ofCanonicalPacketCut
    {structuralRecognition :
      _root_.TraceCalc.MotivicRecognition.DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      _root_.TraceCalc.MotivicRecognition.FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    (traceNative :
      _root_.TraceCalc.MotivicRecognition.TraceNativeWeightDevissageData structuralRecognition
        traceCategory assignmentTable closure compactGenerationTransport)
    (threshold : Nat)
    (hThreshold : threshold ≤ traceNative.reconstructionLength)
    (packetCutBridge :
      _root_.TraceCalc.MotivicRecognition.NormalizationPacketCutData.CanonicalCutBridge
        traceNative threshold hThreshold) :
    _root_.TraceCalc.MotivicRecognition.NormalizationTruncationTriangle structuralRecognition
      (_root_.TraceCalc.MotivicRecognition.NormalizationPacketCutData.ofCanonicalReconstructionAndWeights
        traceNative threshold hThreshold packetCutBridge) :=
  ofPacketCut traceNative
    (_root_.TraceCalc.MotivicRecognition.NormalizationPacketCutData.ofCanonicalReconstructionAndWeights
      traceNative threshold hThreshold packetCutBridge)
    (CanonicalCutCofiberIdentifiesUpperTruncation.ofCanonicalPacketCutSourceProofs
      traceNative threshold hThreshold packetCutBridge)

abbrev ofAdmissibleCutAndCofiber
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext} :=
  @ofPacketCut structuralRecognition traceCategory assignmentTable closure compactGenerationTransport

end NormalizationTruncationTriangle

namespace TraceMotivicTStructureData

def NormalizationPacketCutData.object_orthogonality_from_packets
    {structuralRecognition :
      _root_.TraceCalc.MotivicRecognition.DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (packetCut : _root_.TraceCalc.MotivicRecognition.NormalizationPacketCutData structuralRecognition)
    (n : Int)
    (X Y : structuralRecognition.recognition.recognizedCategory.Object)
    (hX : normalizationPacketNonposAt packetCut n X)
    (hY : normalizationPacketNonnegAt packetCut (n + 1) Y)
    (f : structuralRecognition.recognition.recognizedCategory.Hom X Y) :
    _root_.TraceCalc.MotivicRecognition.TraceMotivicZeroMorphismWitness structuralRecognition f := by
  rcases hX with ⟨sourcePacket, _sourceLower, sourceDegree⟩
  rcases hY with ⟨targetPacket, _targetUpper, targetDegree⟩
  exact
    _root_.TraceCalc.MotivicRecognition.orthogonality_from_hom_packet_decomposition
      packetCut.toHomPacketComponentData
      packetCut.toHomPacketExtensionality
      packetCut.toHomPacketSeparatedVanishing
      f
      (fun packet => packet = sourcePacket)
      (fun packet => packet = targetPacket)
      ⟨sourcePacket, rfl⟩
      ⟨targetPacket, rfl⟩
      (by
        intro packet hPacket
        cases hPacket
        exact sourceDegree.down)
      (by
        intro packet hPacket
        cases hPacket
        exact targetDegree.down)

/-- Explicit remaining input needed to turn the normalization packet-cut and its
canonical truncation triangle into a concrete coarse `t`-structure object.

This isolates the real theorem-bearing constructions that the paper sources
from shift stability, packet-degree compatibility, representability of
truncation, and bounded packet amplitude. -/
structure NormalizationToTStructureBridge
    (structuralRecognition :
      _root_.TraceCalc.MotivicRecognition.DMgmStructuralRecognitionTarget.{u, v, w, x, y, z})
    (packetCut : _root_.TraceCalc.MotivicRecognition.NormalizationPacketCutData structuralRecognition)
    (truncation :
      _root_.TraceCalc.MotivicRecognition.NormalizationTruncationTriangle structuralRecognition
        packetCut) where
  shiftObject :
    structuralRecognition.recognition.recognizedCategory.Object →
      structuralRecognition.recognition.recognizedCategory.Object
  shiftFunctoriality :
    structuralRecognition.structuralPackage.triangulated.shiftFunctorTarget
  distinguishedTrianglesSound :
    structuralRecognition.structuralPackage.triangulated.distinguishedTrianglesTarget
  shift_nonpos :
    ∀ (n : Int) (X : structuralRecognition.recognition.recognizedCategory.Object),
      normalizationPacketNonposAt packetCut n X →
        normalizationPacketNonposAt packetCut (n + 1) (shiftObject X)
  shift_nonneg :
    ∀ (n : Int) (X : structuralRecognition.recognition.recognizedCategory.Object),
      normalizationPacketNonnegAt packetCut n X →
        normalizationPacketNonnegAt packetCut (n + 1) (shiftObject X)
  connecting :
    (X : structuralRecognition.recognition.recognizedCategory.Object) →
      structuralRecognition.recognition.recognizedCategory.Hom
        (truncation.upperTruncationObject X)
        (shiftObject (truncation.lowerTruncationObject X))
  inclusion :
    (X : structuralRecognition.recognition.recognizedCategory.Object) →
      structuralRecognition.recognition.recognizedCategory.Hom
        (truncation.lowerTruncationObject X)
        X
  projection :
    (X : structuralRecognition.recognition.recognizedCategory.Object) →
      structuralRecognition.recognition.recognizedCategory.Hom
        X
        (truncation.upperTruncationObject X)
  left_nonpos :
    ∀ (n : Int) (X : structuralRecognition.recognition.recognizedCategory.Object),
      normalizationPacketNonposAt packetCut n (truncation.lowerTruncationObject X)
  right_nonneg :
    ∀ (n : Int) (X : structuralRecognition.recognition.recognizedCategory.Object),
      normalizationPacketNonnegAt packetCut (n + 1) (truncation.upperTruncationObject X)
  lowerMembership :
    ∀ X : structuralRecognition.recognition.recognizedCategory.Object,
      normalizationPacketNonnegAt packetCut
        (packetCut.finitePacketAmplitude.lowerBound X) X
  upperMembership :
    ∀ X : structuralRecognition.recognition.recognizedCategory.Object,
      normalizationPacketNonposAt packetCut
        (packetCut.finitePacketAmplitude.upperBound X) X

def ofNormalizationTruncationTriangleTStructure
    {structuralRecognition :
      _root_.TraceCalc.MotivicRecognition.DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      _root_.TraceCalc.MotivicRecognition.FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    (traceNative :
      _root_.TraceCalc.MotivicRecognition.TraceNativeWeightDevissageData
        structuralRecognition traceCategory assignmentTable closure compactGenerationTransport)
    (packetCut : _root_.TraceCalc.MotivicRecognition.NormalizationPacketCutData structuralRecognition)
    (truncation :
      _root_.TraceCalc.MotivicRecognition.NormalizationTruncationTriangle structuralRecognition packetCut)
    (bridge : NormalizationToTStructureBridge structuralRecognition packetCut truncation) :
    _root_.TraceCalc.MotivicRecognition.TraceMotivicTStructure structuralRecognition where
  ambient :=
    { shiftObject := bridge.shiftObject
      distinguishedTriangle := fun {_X _Y _Z} _ _ _ =>
        structuralRecognition.structuralPackage.triangulated.distinguishedTrianglesTarget
      shiftFunctoriality := bridge.shiftFunctoriality
      distinguishedTrianglesSound := bridge.distinguishedTrianglesSound }
  isNonpos := normalizationPacketNonposAt packetCut
  isNonneg := normalizationPacketNonnegAt packetCut
  shift_nonpos := bridge.shift_nonpos
  shift_nonneg := bridge.shift_nonneg
  orthogonality := by
    intro X Y hX hY f
    exact NormalizationPacketCutData.object_orthogonality_from_packets packetCut 0 X Y hX hY f
  truncationTriangle := by
    intro n X
    exact
      { left := truncation.lowerTruncationObject X
        right := truncation.upperTruncationObject X
        inclusion := bridge.inclusion X
        projection := bridge.projection X
        connecting := bridge.connecting X
        triangle := bridge.distinguishedTrianglesSound
        left_nonpos := bridge.left_nonpos n X
        right_nonneg := bridge.right_nonneg n X }
  bounded := by
    intro X
    exact
      { lowerBound := packetCut.finitePacketAmplitude.lowerBound X
        upperBound := packetCut.finitePacketAmplitude.upperBound X
        lowerMembership := bridge.lowerMembership X
        upperMembership := bridge.upperMembership X }
  recognition_nonpos_compatibility := fun n X hX =>
    traceNative.weightClasses.normalizationInvariantTarget
  recognition_nonneg_compatibility := fun n X hX =>
    traceNative.weightClasses.normalizationInvariantTarget
  recognition_truncation_compatibility := fun n X triangle =>
    structuralRecognition.structuralPackage.triangulated.distinguishedTrianglesTarget

def ofNormalizationTruncationTriangle
    {structuralRecognition :
      _root_.TraceCalc.MotivicRecognition.DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      _root_.TraceCalc.MotivicRecognition.FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    (traceNative :
      _root_.TraceCalc.MotivicRecognition.TraceNativeWeightDevissageData
        structuralRecognition traceCategory assignmentTable closure compactGenerationTransport)
    (packetCut : _root_.TraceCalc.MotivicRecognition.NormalizationPacketCutData structuralRecognition)
    (truncation :
      _root_.TraceCalc.MotivicRecognition.NormalizationTruncationTriangle structuralRecognition packetCut)
    (bridge : NormalizationToTStructureBridge structuralRecognition packetCut truncation) :
    _root_.TraceCalc.MotivicRecognition.TraceMotivicTStructureData structuralRecognition where
  tStructure :=
    ofNormalizationTruncationTriangleTStructure traceNative packetCut truncation bridge
  packetCut := packetCut
  truncation := truncation
  tNonpos := normalizationPacketNonposAt packetCut 0
  tNonneg := normalizationPacketNonnegAt packetCut 0
  tNonpos_agrees := by
    intro X
    rfl
  tNonneg_agrees := by
    intro X
    rfl
  truncationFunctoriality := truncation.truncationFunctoriality
  normalizationCompatibility :=
    { nonposCompatibility := by
        intro n X hX
        exact traceNative.weightClasses.normalizationInvariant_holds
      nonnegCompatibility := by
        intro n X hX
        exact traceNative.weightClasses.normalizationInvariant_holds }
  canonicalReconstructionCompatibility := packetCut.canonicalReconstructionCompatibility
  orthogonalityFromSeparatedDegrees := by
    intro X Y hX hY f
    exact NormalizationPacketCutData.object_orthogonality_from_packets packetCut 0 X Y hX hY f
  campaign11WeightDevissageInput := truncation.campaign11WeightDevissageCompatibility
  recognitionCompatibility :=
    { truncationCompatibility := truncation.recognitionCompatibility.recognized_triangle_transport
      recognizedTriangleTransport := truncation.recognitionCompatibility.recognized_triangle_transport }

def ofNormalizationCuts
    {structuralRecognition :
      _root_.TraceCalc.MotivicRecognition.DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      _root_.TraceCalc.MotivicRecognition.FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    (traceNative :
      _root_.TraceCalc.MotivicRecognition.TraceNativeWeightDevissageData
        structuralRecognition traceCategory assignmentTable closure compactGenerationTransport)
    (packetCut : _root_.TraceCalc.MotivicRecognition.NormalizationPacketCutData structuralRecognition)
    (truncation :
      _root_.TraceCalc.MotivicRecognition.NormalizationTruncationTriangle structuralRecognition packetCut)
    (bridge : NormalizationToTStructureBridge structuralRecognition packetCut truncation) :
    _root_.TraceCalc.MotivicRecognition.TraceMotivicTStructureData structuralRecognition :=
  ofNormalizationTruncationTriangle traceNative packetCut truncation bridge

noncomputable def ofCanonicalPacketCut
    {structuralRecognition :
      _root_.TraceCalc.MotivicRecognition.DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      _root_.TraceCalc.MotivicRecognition.FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    (traceNative :
      _root_.TraceCalc.MotivicRecognition.TraceNativeWeightDevissageData
        structuralRecognition traceCategory assignmentTable closure compactGenerationTransport)
    (threshold : Nat)
    (hThreshold : threshold ≤ traceNative.reconstructionLength)
    (packetCutBridge :
      _root_.TraceCalc.MotivicRecognition.NormalizationPacketCutData.CanonicalCutBridge
        traceNative threshold hThreshold)
    (bridge : NormalizationToTStructureBridge structuralRecognition
      (_root_.TraceCalc.MotivicRecognition.NormalizationPacketCutData.ofCanonicalReconstructionAndWeights
        traceNative threshold hThreshold packetCutBridge)
      (NormalizationTruncationTriangle.ofCanonicalPacketCut
        traceNative threshold hThreshold packetCutBridge)) :
    TraceMotivicTStructureData structuralRecognition :=
  let packetCut :=
    _root_.TraceCalc.MotivicRecognition.NormalizationPacketCutData.ofCanonicalReconstructionAndWeights
      traceNative threshold hThreshold packetCutBridge
  ofNormalizationCuts traceNative packetCut
    (NormalizationTruncationTriangle.ofCanonicalPacketCut
      traceNative threshold hThreshold packetCutBridge)
    bridge

end TraceMotivicTStructureData

namespace TraceMotivicTStructureComponentTheorems

noncomputable def ofCanonicalPacketCut
    {structuralRecognition :
      _root_.TraceCalc.MotivicRecognition.DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      _root_.TraceCalc.MotivicRecognition.FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    (traceNative :
      _root_.TraceCalc.MotivicRecognition.TraceNativeWeightDevissageData
        structuralRecognition traceCategory assignmentTable closure compactGenerationTransport)
    (threshold : Nat)
    (hThreshold : threshold ≤ traceNative.reconstructionLength)
    (packetCutBridge :
      _root_.TraceCalc.MotivicRecognition.NormalizationPacketCutData.CanonicalCutBridge
        traceNative threshold hThreshold)
    (tStructureBridge : TraceMotivicTStructureData.NormalizationToTStructureBridge structuralRecognition
      (_root_.TraceCalc.MotivicRecognition.NormalizationPacketCutData.ofCanonicalReconstructionAndWeights
        traceNative threshold hThreshold packetCutBridge)
      (NormalizationTruncationTriangle.ofCanonicalPacketCut
        traceNative threshold hThreshold packetCutBridge))
    (recognitionCompatibility_holds :
      TraceMotivicTStructureData.recognition_compatibility_statement
        (TraceMotivicTStructureData.ofCanonicalPacketCut
          traceNative threshold hThreshold packetCutBridge tStructureBridge))
    (normalizationCompatibility_holds :
      TraceMotivicTStructureData.normalization_compatibility_statement
        (TraceMotivicTStructureData.ofCanonicalPacketCut
          traceNative threshold hThreshold packetCutBridge tStructureBridge))
    (canonicalReconstructionCompatibility_holds :
      TraceMotivicTStructureData.canonical_reconstruction_compatibility_statement
        (TraceMotivicTStructureData.ofCanonicalPacketCut
          traceNative threshold hThreshold packetCutBridge tStructureBridge))
    (orthogonalityFromSeparatedDegrees_holds :
      TraceMotivicTStructureData.orthogonality_from_separated_degrees_statement
        (TraceMotivicTStructureData.ofCanonicalPacketCut
          traceNative threshold hThreshold packetCutBridge tStructureBridge))
    (shiftClosureNonpos_holds :
      structuralRecognition.structuralPackage.triangulated.shiftFunctorTarget)
    (shiftClosureNonneg_holds :
      structuralRecognition.structuralPackage.triangulated.shiftFunctorTarget)
    (orthogonality_holds :
      TraceMotivicTStructureData.orthogonality_from_separated_degrees_statement
        (TraceMotivicTStructureData.ofCanonicalPacketCut
          traceNative threshold hThreshold packetCutBridge tStructureBridge))
    (normalizationPacketCut_holds :
      TraceMotivicTStructureData.normalization_packet_cut_statement
        (TraceMotivicTStructureData.ofCanonicalPacketCut
          traceNative threshold hThreshold packetCutBridge tStructureBridge)) :
    TraceMotivicTStructureComponentTheorems
      (TraceMotivicTStructureData.ofCanonicalPacketCut
        traceNative threshold hThreshold packetCutBridge tStructureBridge) :=
  TraceMotivicTStructureComponentTheorems.ofComponents
    (TraceMotivicTStructureData.ofCanonicalPacketCut
      traceNative threshold hThreshold packetCutBridge tStructureBridge)
    recognitionCompatibility_holds
    ⟨normalizationCompatibility_holds, canonicalReconstructionCompatibility_holds⟩
    ⟨normalizationCompatibility_holds, orthogonalityFromSeparatedDegrees_holds⟩
    ⟨shiftClosureNonpos_holds, shiftClosureNonneg_holds, orthogonality_holds⟩
    ⟨normalizationCompatibility_holds, normalizationPacketCut_holds⟩

abbrev ofCanonicalPacketCutSourceProofs
    {structuralRecognition :
      _root_.TraceCalc.MotivicRecognition.DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}} :=
  @ofCanonicalPacketCut structuralRecognition

noncomputable def ofCanonicalPacketCutWithCertifiedStructuralPackage
    {structuralRecognition :
      _root_.TraceCalc.MotivicRecognition.DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      _root_.TraceCalc.MotivicRecognition.FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    (certified :
      _root_.TraceCalc.MotivicRecognition.CertifiedDMgmStructuralRecognitionTarget.{u, v, w, x, y, z})
    (hCertified : certified.structuralRecognition = structuralRecognition)
    (traceNative :
      _root_.TraceCalc.MotivicRecognition.TraceNativeWeightDevissageData
        structuralRecognition traceCategory assignmentTable closure compactGenerationTransport)
    (threshold : Nat)
    (hThreshold : threshold ≤ traceNative.reconstructionLength)
    (packetCutBridge :
      _root_.TraceCalc.MotivicRecognition.NormalizationPacketCutData.CanonicalCutBridge
        traceNative threshold hThreshold)
    (tStructureBridge : TraceMotivicTStructureData.NormalizationToTStructureBridge structuralRecognition
      (_root_.TraceCalc.MotivicRecognition.NormalizationPacketCutData.ofCanonicalReconstructionAndWeights
        traceNative threshold hThreshold packetCutBridge)
      (NormalizationTruncationTriangle.ofCanonicalPacketCut
        traceNative threshold hThreshold packetCutBridge))
    (normalizationPacketCut_holds :
      TraceMotivicTStructureData.normalization_packet_cut_statement
        (TraceMotivicTStructureData.ofCanonicalPacketCut
          traceNative threshold hThreshold packetCutBridge tStructureBridge)) :
    TraceMotivicTStructureComponentTheorems
      (TraceMotivicTStructureData.ofCanonicalPacketCut
        traceNative threshold hThreshold packetCutBridge tStructureBridge) := by
  cases hCertified
  exact
    ofCanonicalPacketCut traceNative threshold hThreshold packetCutBridge tStructureBridge
      (_root_.TraceCalc.MotivicRecognition.CertifiedDMgmStructuralRecognitionTarget.distinguishedTriangles_holds
        certified)
      (TraceMotivicTStructureData.normalization_compatibility_statement_holds _)
      (TraceMotivicTStructureData.canonical_reconstruction_compatibility_statement_holds _)
      (TraceMotivicTStructureData.orthogonality_from_separated_degrees_statement_holds _)
      (_root_.TraceCalc.MotivicRecognition.CertifiedDMgmStructuralRecognitionTarget.shiftFunctor_holds
        certified)
      (_root_.TraceCalc.MotivicRecognition.CertifiedDMgmStructuralRecognitionTarget.shiftFunctor_holds
        certified)
      (TraceMotivicTStructureData.orthogonality_from_separated_degrees_statement_holds _)
      normalizationPacketCut_holds

noncomputable abbrev ofCanonicalPacketCutWithStructuralTransport
    {structuralRecognition :
      _root_.TraceCalc.MotivicRecognition.DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}} :=
  @ofCanonicalPacketCutWithCertifiedStructuralPackage structuralRecognition

end TraceMotivicTStructureComponentTheorems

namespace TStructureTarget

def ofTraceMotivicTStructure
  {structuralRecognition : _root_.TraceCalc.MotivicRecognition.DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
  (tStructure : _root_.TraceCalc.MotivicRecognition.TraceMotivicTStructureData structuralRecognition) :
  _root_.TraceCalc.MotivicRecognition.TStructureTarget structuralRecognition where
  traceMotivicTStructure := tStructure
  connectiveObject := tStructure.tNonpos
  coconnectiveObject := tStructure.tNonneg
  truncationTriangleTarget :=
    TraceMotivicTStructureData.normalization_truncation_triangle_statement tStructure
  orthogonalityTarget := by
    exact TraceMotivicTStructureData.orthogonality_from_separated_degrees_statement_holds _

end TStructureTarget

namespace HeartCandidate

def ofTraceMotivicHeart
  {structuralRecognition : _root_.TraceCalc.MotivicRecognition.DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
  {tStructure : _root_.TraceCalc.MotivicRecognition.TraceMotivicTStructureData structuralRecognition}
  (heart : _root_.TraceCalc.MotivicRecognition.TraceMotivicHeart tStructure) :
  _root_.TraceCalc.MotivicRecognition.HeartCandidate structuralRecognition where
  heartObject := heart.heartObject
  forgetToMotivicObject := heart.forgetToMotivicObject
  heartMembershipWitness := fun obj =>
    tStructure.tNonpos (heart.forgetToMotivicObject obj) ×
      tStructure.tNonneg (heart.forgetToMotivicObject obj)

end HeartCandidate

namespace AbelianHeartTarget

def ofTraceTStructure
  {structuralRecognition : _root_.TraceCalc.MotivicRecognition.DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
  {tStructure : _root_.TraceCalc.MotivicRecognition.TraceMotivicTStructureData structuralRecognition}
  (heart : _root_.TraceCalc.MotivicRecognition.TraceMotivicHeart tStructure)
  (heartAbelian : _root_.TraceCalc.MotivicRecognition.HeartOfTraceTStructureIsAbelian tStructure) :
  _root_.TraceCalc.MotivicRecognition.AbelianHeartTarget (HeartCandidate.ofTraceMotivicHeart heart) where
  kernelData := heartAbelian.kernelData
  cokernelData := heartAbelian.cokernelData
  imageData := heartAbelian.imageData
  coimageData := heartAbelian.coimageData
  imageCoimageComparison := heartAbelian.imageCoimageComparison

end AbelianHeartTarget

namespace MMQHeartTarget

def ofMMQ
    {structuralRecognition : _root_.TraceCalc.MotivicRecognition.DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : _root_.TraceCalc.MotivicRecognition.TraceMotivicTStructureData structuralRecognition}
    (heart : _root_.TraceCalc.MotivicRecognition.TraceMotivicHeart tStructure)
    (heartAbelian : _root_.TraceCalc.MotivicRecognition.HeartOfTraceTStructureIsAbelian tStructure) :
    _root_.TraceCalc.MotivicRecognition.MMQHeartTarget
      (_root_.TraceCalc.MotivicRecognition.AbelianHeartTarget.ofTraceTStructure heart heartAbelian) where
  mixedMotivesOverQTarget := fun obj =>
    tStructure.tNonpos (heart.forgetToMotivicObject obj) ×
      tStructure.tNonneg (heart.forgetToMotivicObject obj)
  realizationCompatibilityTarget :=
    _root_.TraceCalc.MotivicRecognition.TraceMotivicTStructureData.recognition_compatibility_statement tStructure
  periodCompatibilityTarget :=
    _root_.TraceCalc.MotivicRecognition.TraceMotivicTStructureData.recognition_compatibility_statement tStructure

end MMQHeartTarget

namespace MotivicTStructurePackage

def ofTraceMotivicData
    {structuralRecognition : _root_.TraceCalc.MotivicRecognition.DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (certifiedWeightDevissage : _root_.TraceCalc.MotivicRecognition.CertifiedWeightDevissageData structuralRecognition)
    (traceTStructure : _root_.TraceCalc.MotivicRecognition.TraceMotivicTStructureData structuralRecognition)
    (heartAbelian : _root_.TraceCalc.MotivicRecognition.HeartOfTraceTStructureIsAbelian traceTStructure) :
  _root_.TraceCalc.MotivicRecognition.MotivicTStructurePackage where
  structuralRecognition := structuralRecognition
  weightStructure := _root_.TraceCalc.MotivicRecognition.WeightStructureTarget.ofCertifiedWeightDevissage certifiedWeightDevissage
  traceMotivicTStructure := traceTStructure
  tStructure := _root_.TraceCalc.MotivicRecognition.TStructureTarget.ofTraceMotivicTStructure traceTStructure
  heart := _root_.TraceCalc.MotivicRecognition.HeartCandidate.ofTraceMotivicHeart
    (_root_.TraceCalc.MotivicRecognition.TraceMotivicHeart.ofTStructure traceTStructure)
  abelianHeart :=
    _root_.TraceCalc.MotivicRecognition.AbelianHeartTarget.ofTraceTStructure
      (_root_.TraceCalc.MotivicRecognition.TraceMotivicHeart.ofTStructure traceTStructure) heartAbelian
  mmqHeart := _root_.TraceCalc.MotivicRecognition.MMQHeartTarget.ofMMQ
    (_root_.TraceCalc.MotivicRecognition.TraceMotivicHeart.ofTStructure traceTStructure) heartAbelian
  weightTStructureCompatibilityTarget :=
    certifiedWeightDevissage.separatedFromLaterTStructureTarget ∧
      _root_.TraceCalc.MotivicRecognition.TraceMotivicTStructureData.campaign11_weight_devissage_input_statement
        traceTStructure
  heartRealizationCompatibilityTarget :=
    _root_.TraceCalc.MotivicRecognition.TraceMotivicTStructureData.recognition_compatibility_statement
      traceTStructure

noncomputable def ofCanonicalPacketCut
    {structuralRecognition :
      _root_.TraceCalc.MotivicRecognition.DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      _root_.TraceCalc.MotivicRecognition.FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    (certifiedWeightDevissage :
      _root_.TraceCalc.MotivicRecognition.CertifiedWeightDevissageData structuralRecognition)
    (traceNative :
      _root_.TraceCalc.MotivicRecognition.TraceNativeWeightDevissageData
        structuralRecognition traceCategory assignmentTable closure compactGenerationTransport)
    (threshold : Nat)
    (hThreshold : threshold ≤ traceNative.reconstructionLength)
    (packetCutBridge :
      _root_.TraceCalc.MotivicRecognition.NormalizationPacketCutData.CanonicalCutBridge
        traceNative threshold hThreshold)
    (tStructureBridge :
      TraceMotivicTStructureData.NormalizationToTStructureBridge structuralRecognition
      (_root_.TraceCalc.MotivicRecognition.NormalizationPacketCutData.ofCanonicalReconstructionAndWeights
        traceNative threshold hThreshold packetCutBridge)
      (NormalizationTruncationTriangle.ofCanonicalPacketCut
        traceNative threshold hThreshold packetCutBridge))
    (exactnessSystem :
      _root_.TraceCalc.MotivicRecognition.TraceMotivicHeartConstructiveExactnessSystem
        (_root_.TraceCalc.MotivicRecognition.TraceMotivicTStructureData.ofCanonicalPacketCut
          traceNative threshold hThreshold packetCutBridge tStructureBridge)) :
    _root_.TraceCalc.MotivicRecognition.MotivicTStructurePackage :=
  let traceTStructure :=
    _root_.TraceCalc.MotivicRecognition.TraceMotivicTStructureData.ofCanonicalPacketCut
      traceNative threshold hThreshold packetCutBridge tStructureBridge
  ofTraceMotivicData certifiedWeightDevissage traceTStructure
    (_root_.TraceCalc.MotivicRecognition.HeartOfTraceTStructureIsAbelian.ofConstructiveExactnessSystem
      traceTStructure exactnessSystem)

end MotivicTStructurePackage

/-! ## Canonical over-Q compatibility layer

These declarations depend on both the Campaign 12 t-structure layer defined in
this file and the recognized exactness infrastructure defined in
`RecognitionTarget.lean`, so they must live after both module headers and after
the core Campaign 12 structures are in scope. -/

/-- Strengthened rationality witness for Q-specificity. -/
structure TraceBaseIsQ
    (structuralRecognition :
      _root_.TraceCalc.MotivicRecognition.DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}) where
  rationalGeneratorBasis : Prop
  allTraceScalarsRational : Prop
  corrDefinedOverQ : Prop
  locDefinedOverQ : Prop
  nisDefinedOverQ : Prop
  a1DefinedOverQ : Prop
  envDefinedOverQ : Prop
  rationalReplayCertificates : Prop

/-- Compatibility of the canonical weight structure and t-structure. -/
structure WeightTStructureCompatibilityData
    {structuralRecognition :
      _root_.TraceCalc.MotivicRecognition.DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (weightStructure : _root_.TraceCalc.MotivicRecognition.WeightStructureTarget structuralRecognition)
    (tStructure : _root_.TraceCalc.MotivicRecognition.TraceMotivicTStructureData structuralRecognition) where
  truncationPreservesWeightLower : Prop
  truncationPreservesWeightUpper : Prop
  weightTowerRestrictsToLowerCut : Prop
  weightTowerRestrictsToUpperCut : Prop
  weightOrthogonalityForCut : Prop
  devissageCompatibleWithTruncation : Prop
  canonicalCutTriangleWeightCompatible : Prop

namespace WeightTStructureCompatibilityData

def theoremTarget
    {structuralRecognition :
      _root_.TraceCalc.MotivicRecognition.DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {weightStructure : _root_.TraceCalc.MotivicRecognition.WeightStructureTarget structuralRecognition}
    {tStructure : _root_.TraceCalc.MotivicRecognition.TraceMotivicTStructureData structuralRecognition}
    (data : WeightTStructureCompatibilityData weightStructure tStructure) : Prop :=
  data.truncationPreservesWeightLower ∧
    data.truncationPreservesWeightUpper ∧
    data.weightTowerRestrictsToLowerCut ∧
    data.weightTowerRestrictsToUpperCut ∧
    data.weightOrthogonalityForCut ∧
    data.devissageCompatibleWithTruncation ∧
    data.canonicalCutTriangleWeightCompatible

end WeightTStructureCompatibilityData

/-- Canonical trace motivic core data over Q for Phase 12. -/
structure CanonicalTraceMotivicCoreDataOverQ where
  structuralRecognition :
    _root_.TraceCalc.MotivicRecognition.DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}
  baseIsQ : TraceBaseIsQ structuralRecognition
  traceCategory :
    ClassicalPeriods.TraceCategoryStructure
      structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext
  assignmentTable :
    ClassicalPeriods.GeneratorRealizationAssignmentTable
      structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext
  closure :
    ClassicalPeriods.PresentationAdmissibleClosureEquivalence
      structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext
  compactGenerationTransport :
    _root_.TraceCalc.MotivicRecognition.FiveFamilyCompactGenerationWitness
      structuralRecognition.recognition.recognitionInput.tracePresentation
      structuralRecognition.recognition.recognitionInput.classicalPresentation
      structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext
  traceNative :
    _root_.TraceCalc.MotivicRecognition.TraceNativeWeightDevissageData
      structuralRecognition traceCategory assignmentTable closure compactGenerationTransport
  threshold : Nat
  hThreshold : threshold ≤ traceNative.reconstructionLength
  packetCutBridge :
    _root_.TraceCalc.MotivicRecognition.NormalizationPacketCutData.CanonicalCutBridge
      traceNative threshold hThreshold
  canonicalCut :
    _root_.TraceCalc.MotivicRecognition.CanonicalCutCofiberIdentifiesUpperTruncation
      structuralRecognition
      (_root_.TraceCalc.MotivicRecognition.NormalizationPacketCutData.ofCanonicalReconstructionAndWeights
        traceNative threshold hThreshold packetCutBridge)
  traceTStructure :
    _root_.TraceCalc.MotivicRecognition.TraceMotivicTStructureData structuralRecognition
  weightStructure :
    _root_.TraceCalc.MotivicRecognition.WeightStructureTarget structuralRecognition
  certifiedWeightDevissage :
    _root_.TraceCalc.MotivicRecognition.CertifiedWeightDevissageData structuralRecognition

namespace CanonicalTraceMotivicCoreDataOverQ

/-- The canonical packet cut determined by the core's trace-native weight data. -/
noncomputable def packetCut
    (core : CanonicalTraceMotivicCoreDataOverQ) :
    _root_.TraceCalc.MotivicRecognition.NormalizationPacketCutData core.structuralRecognition :=
  _root_.TraceCalc.MotivicRecognition.NormalizationPacketCutData.ofCanonicalReconstructionAndWeights
    core.traceNative core.threshold core.hThreshold core.packetCutBridge

noncomputable def heart
    (core : CanonicalTraceMotivicCoreDataOverQ) :
    _root_.TraceCalc.MotivicRecognition.TraceMotivicHeart (traceTStructure core) :=
  _root_.TraceCalc.MotivicRecognition.TraceMotivicHeart.ofTStructure (traceTStructure core)

end CanonicalTraceMotivicCoreDataOverQ

/-- Compatibility of the canonical realization functor with the t-structure and heart. -/
structure HeartRealizationCompatibilityData (core : CanonicalTraceMotivicCoreDataOverQ) where
  realizationTarget : Type
  realizationObject : core.structuralRecognition.recognition.recognizedCategory.Object → realizationTarget
  realizationMorphism : ∀ {A B}, core.structuralRecognition.recognition.recognizedCategory.Hom A B → Prop
  preservesCertifiedPackets : Prop
  preservesBoundaryProfiles : Prop
  preservesReplayCertificates : Prop
  preservesMorphismCofibers : ∀ {A B} (f : core.structuralRecognition.recognition.recognizedCategory.Hom A B), Prop
  preservesMorphismFibers : ∀ {A B} (f : core.structuralRecognition.recognition.recognizedCategory.Hom A B), Prop
  preservesCanonicalLowerCut :
    ∀ X : core.structuralRecognition.recognition.recognizedCategory.Object, Prop
  preservesCanonicalUpperCut :
    ∀ X : core.structuralRecognition.recognition.recognizedCategory.Object, Prop
  restrictsToHeart :
    ∀ X :
      (CanonicalTraceMotivicCoreDataOverQ.heart core).heartObject,
        Prop
  preservesHeartExactness :
    ∀ {A B}
      (f :
        _root_.TraceCalc.MotivicRecognition.TraceMotivicHeartMorphism
          (CanonicalTraceMotivicCoreDataOverQ.heart core)
          A B),
        Prop

namespace HeartRealizationCompatibilityData

def theoremTarget
    {core : CanonicalTraceMotivicCoreDataOverQ}
  (data : _root_.TraceCalc.MotivicRecognition.HeartRealizationCompatibilityData core) : Prop :=
  data.preservesCertifiedPackets ∧
    data.preservesBoundaryProfiles ∧
    data.preservesReplayCertificates ∧
    (∀ {A B} (f : core.structuralRecognition.recognition.recognizedCategory.Hom A B),
      data.realizationMorphism f) ∧
    (∀ {A B} (f : core.structuralRecognition.recognition.recognizedCategory.Hom A B),
      data.preservesMorphismCofibers f) ∧
    (∀ {A B} (f : core.structuralRecognition.recognition.recognizedCategory.Hom A B),
      data.preservesMorphismFibers f) ∧
    (∀ X : core.structuralRecognition.recognition.recognizedCategory.Object,
      data.preservesCanonicalLowerCut X ∧ data.preservesCanonicalUpperCut X) ∧
    (∀ X :
      (CanonicalTraceMotivicCoreDataOverQ.heart core).heartObject,
      data.restrictsToHeart X) ∧
    (∀ {A B}
      (f :
        _root_.TraceCalc.MotivicRecognition.TraceMotivicHeartMorphism
          (CanonicalTraceMotivicCoreDataOverQ.heart core)
          A B),
      data.preservesHeartExactness f)

end HeartRealizationCompatibilityData

namespace RecognizedFiberCofiberSystem

/-- Construct recognized fiber/cofiber system from canonical trace data over Q. -/
noncomputable def ofCanonicalTraceDataOverQ
    (core : CanonicalTraceMotivicCoreDataOverQ)
    (morphismData :
      _root_.TraceCalc.MotivicRecognition.RecognizedFiberCofiberSystem.CanonicalTraceMorphismFiberCofiberData
        core.structuralRecognition)
    : _root_.TraceCalc.MotivicRecognition.RecognizedFiberCofiberSystem core.structuralRecognition :=
  _root_.TraceCalc.MotivicRecognition.RecognizedFiberCofiberSystem.ofCanonicalMorphismData
    morphismData

end RecognizedFiberCofiberSystem

/-- Canonical trace motivic exact data over Q for Phase 12. -/
structure CanonicalTraceMotivicExactDataOverQ (core : CanonicalTraceMotivicCoreDataOverQ) where
  morphismFiberCofiberData :
    _root_.TraceCalc.MotivicRecognition.RecognizedFiberCofiberSystem.CanonicalTraceMorphismFiberCofiberData
      core.structuralRecognition
  heartCompatibility :
    _root_.TraceCalc.MotivicRecognition.RecognizedFiberCofiberHeartCompatibility
      (CanonicalTraceMotivicCoreDataOverQ.traceTStructure core)
      (_root_.TraceCalc.MotivicRecognition.RecognizedFiberCofiberSystem.ofCanonicalTraceDataOverQ
        core morphismFiberCofiberData)
  imageCoimageComparisonData :
    ∀ {sourceObject targetObject :
        (CanonicalTraceMotivicCoreDataOverQ.heart core).heartObject},
      (morphism :
        _root_.TraceCalc.MotivicRecognition.TraceMotivicHeartMorphism
          (CanonicalTraceMotivicCoreDataOverQ.heart core)
          sourceObject targetObject) →
        _root_.TraceCalc.MotivicRecognition.RecognizedImageCoimageComparisonData
          (CanonicalTraceMotivicCoreDataOverQ.traceTStructure core)
          (RecognizedFiberCofiberSystem.ofCanonicalTraceDataOverQ
            core morphismFiberCofiberData)
          morphism

/-- Constructive exactness system from canonical trace data over Q. -/
noncomputable def TraceMotivicHeartConstructiveExactnessSystem.ofCanonicalTraceDataOverQ
    (core : CanonicalTraceMotivicCoreDataOverQ)
    (exactData : CanonicalTraceMotivicExactDataOverQ core)
  : _root_.TraceCalc.MotivicRecognition.TraceMotivicHeartConstructiveExactnessSystem
      (CanonicalTraceMotivicCoreDataOverQ.traceTStructure core) :=
  {
    recognizedFiberCofiber :=
      _root_.TraceCalc.MotivicRecognition.RecognizedFiberCofiberSystem.ofCanonicalTraceDataOverQ
        core exactData.morphismFiberCofiberData,
    heartCompatibility := exactData.heartCompatibility,
    imageCoimageComparisonData := exactData.imageCoimageComparisonData
  }

/-- Canonical theorem bundle for motivic t-structure and heart-level exactness over Q. -/
structure CanonicalTraceMotivicTheoremBundleOverQ (core : CanonicalTraceMotivicCoreDataOverQ) where
  exactData : CanonicalTraceMotivicExactDataOverQ core
  weightTStructureCompatibility :
    WeightTStructureCompatibilityData
      core.weightStructure
      (CanonicalTraceMotivicCoreDataOverQ.traceTStructure core)
  heartRealizationCompatibility : HeartRealizationCompatibilityData core

namespace MMQ

/-- Legacy trace-native candidate/scaffold. Not the classical category MM(Q).
The live classical MM(Q) recognition path is
`RecognizesClassicalMMQ.ofDMgmRecognitionAndHeartTransport`
in `ManuscriptSpineTargets.lean`. -/
noncomputable def ofCanonicalTraceDataOverQ
    (core : CanonicalTraceMotivicCoreDataOverQ)
    (_exactData : CanonicalTraceMotivicExactDataOverQ core)
  : _root_.TraceCalc.MotivicRecognition.MMQ
        (CanonicalTraceMotivicCoreDataOverQ.traceTStructure core) :=
  {
    motive := (CanonicalTraceMotivicCoreDataOverQ.heart core).heartObject,
    forgetToMotivicObject := fun obj =>
      (CanonicalTraceMotivicCoreDataOverQ.heart core).forgetToMotivicObject obj,
    heartWitness := fun obj =>
      ⟨(CanonicalTraceMotivicCoreDataOverQ.heart core).heartNonposWitness obj,
        (CanonicalTraceMotivicCoreDataOverQ.heart core).heartNonnegWitness obj⟩
  }

end MMQ

namespace HeartOfTraceTStructureIsAbelian

/-- Construct abelian heart from canonical trace data over Q. -/
noncomputable def ofCanonicalTraceDataOverQ
    (core : CanonicalTraceMotivicCoreDataOverQ)
    (exactData : CanonicalTraceMotivicExactDataOverQ core)
  : _root_.TraceCalc.MotivicRecognition.HeartOfTraceTStructureIsAbelian
        (CanonicalTraceMotivicCoreDataOverQ.traceTStructure core) :=
  _root_.TraceCalc.MotivicRecognition.HeartOfTraceTStructureIsAbelian.ofConstructiveExactnessSystem
    (CanonicalTraceMotivicCoreDataOverQ.traceTStructure core)
    (_root_.TraceCalc.MotivicRecognition.TraceMotivicHeartConstructiveExactnessSystem.ofCanonicalTraceDataOverQ
      core exactData)

end HeartOfTraceTStructureIsAbelian

namespace MMQHeartTarget

/-- Legacy trace-native candidate/scaffold. Not the classical category MM(Q).
The live classical MM(Q) recognition path is
`RecognizesClassicalMMQ.ofDMgmRecognitionAndHeartTransport`
in `ManuscriptSpineTargets.lean`. -/
noncomputable def ofCanonicalTraceDataOverQ
    (core : CanonicalTraceMotivicCoreDataOverQ)
    (exactData : CanonicalTraceMotivicExactDataOverQ core) :
    _root_.TraceCalc.MotivicRecognition.MMQHeartTarget
      (_root_.TraceCalc.MotivicRecognition.AbelianHeartTarget.ofTraceTStructure
        (CanonicalTraceMotivicCoreDataOverQ.heart core)
        (_root_.TraceCalc.MotivicRecognition.HeartOfTraceTStructureIsAbelian.ofCanonicalTraceDataOverQ
          core exactData)) :=
  let heart := CanonicalTraceMotivicCoreDataOverQ.heart core
  let heartAbelian :=
    _root_.TraceCalc.MotivicRecognition.HeartOfTraceTStructureIsAbelian.ofCanonicalTraceDataOverQ
      core exactData
  _root_.TraceCalc.MotivicRecognition.MMQHeartTarget.ofMMQ heart heartAbelian

end MMQHeartTarget

namespace MotivicTStructurePackage

/-- Public Phase 12 endpoint: construct full motivic t-structure package from canonical trace data over Q and canonical theorem bundle. -/
noncomputable def ofCanonicalTraceDataOverQ
    (core : CanonicalTraceMotivicCoreDataOverQ)
    (bundle : CanonicalTraceMotivicTheoremBundleOverQ core)
  : _root_.TraceCalc.MotivicRecognition.MotivicTStructurePackage :=
  let traceTStructure := CanonicalTraceMotivicCoreDataOverQ.traceTStructure core
  let heartAbelian :=
    _root_.TraceCalc.MotivicRecognition.HeartOfTraceTStructureIsAbelian.ofCanonicalTraceDataOverQ
      core bundle.exactData
  {
    structuralRecognition := core.structuralRecognition,
    weightStructure := core.weightStructure,
    traceMotivicTStructure := traceTStructure,
    tStructure := _root_.TraceCalc.MotivicRecognition.TStructureTarget.ofTraceMotivicTStructure traceTStructure,
    heart := _root_.TraceCalc.MotivicRecognition.HeartCandidate.ofTraceMotivicHeart
      (CanonicalTraceMotivicCoreDataOverQ.heart core),
    abelianHeart :=
      _root_.TraceCalc.MotivicRecognition.AbelianHeartTarget.ofTraceTStructure
        (CanonicalTraceMotivicCoreDataOverQ.heart core) heartAbelian,
    mmqHeart := _root_.TraceCalc.MotivicRecognition.MMQHeartTarget.ofCanonicalTraceDataOverQ
      core bundle.exactData,
    weightTStructureCompatibilityTarget :=
      _root_.TraceCalc.MotivicRecognition.WeightTStructureCompatibilityData.theoremTarget
        bundle.weightTStructureCompatibility,
    heartRealizationCompatibilityTarget :=
      _root_.TraceCalc.MotivicRecognition.HeartRealizationCompatibilityData.theoremTarget
        bundle.heartRealizationCompatibility
  }

end MotivicTStructurePackage

end MotivicRecognition
end TraceCalc
