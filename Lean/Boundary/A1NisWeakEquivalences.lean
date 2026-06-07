import Boundary.A1Locality
/-!
This file was split out of `Boundary.A1Geometry`; declarations remain in
namespace `Boundary` under their mathematical owner layer.
-/

universe u

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open Polynomial
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open Geometry

namespace Boundary

noncomputable section

variable {k : Type u} [Field k] [PerfectField k]
def IsA1NisLocalEquivalence
    {category : SmCorQ (k := k)}
    {F G : LinearPST category}
    (φ : F ⟶ G) :=
  ∀ (L : LinearA1NisLocalPST category),
    Function.Bijective (fun η : G ⟶ L.toLinearPST => φ ≫ η)

namespace IsA1NisLocalEquivalence

theorem id
    {category : SmCorQ (k := k)}
    (F : LinearPST category) :
    IsA1NisLocalEquivalence (𝟙 F) := by
  intro L
  constructor
  · intro η₁ η₂ hη
    exact hη
  · intro η
    refine ⟨η, ?_⟩
    simp

theorem comp
    {category : SmCorQ (k := k)}
    {F G H : LinearPST category}
    {φ : F ⟶ G} {ψ : G ⟶ H}
    (hφ : IsA1NisLocalEquivalence φ)
    (hψ : IsA1NisLocalEquivalence ψ) :
    IsA1NisLocalEquivalence (φ ≫ ψ) := by
  intro L
  let bφ : Function.Bijective (fun η : G ⟶ L.toLinearPST => φ ≫ η) := hφ L
  let bψ : Function.Bijective (fun η : H ⟶ L.toLinearPST => ψ ≫ η) := hψ L
  constructor
  · intro η₁ η₂ hη
    apply bψ.1
    apply bφ.1
    simpa [Category.assoc] using hη
  · intro η
    rcases bφ.2 η with ⟨θ, hθ⟩
    rcases bψ.2 θ with ⟨μ, hμ⟩
    refine ⟨μ, ?_⟩
    calc
      (φ ≫ ψ) ≫ μ = φ ≫ (ψ ≫ μ) := by simp [Category.assoc]
      _ = φ ≫ θ := by exact congrArg (fun t => φ ≫ t) hμ
      _ = η := hθ

theorem of_comp_left
    {category : SmCorQ (k := k)}
    {F G H : LinearPST category}
    {φ : F ⟶ G} {ψ : G ⟶ H}
    (hψ : IsA1NisLocalEquivalence ψ)
    (hcomp : IsA1NisLocalEquivalence (φ ≫ ψ)) :
    IsA1NisLocalEquivalence φ := by
  intro L
  let bφ : Function.Bijective (fun η : G ⟶ L.toLinearPST => φ ≫ η) := by
    refine ⟨?_, ?_⟩
    · intro η₁ η₂ hη
      rcases (hψ L).2 η₁ with ⟨μ₁, hμ₁⟩
      rcases (hψ L).2 η₂ with ⟨μ₂, hμ₂⟩
      have hcompEq : (φ ≫ ψ) ≫ μ₁ = (φ ≫ ψ) ≫ μ₂ := by
        calc
          (φ ≫ ψ) ≫ μ₁ = φ ≫ η₁ := by
            simpa [Category.assoc] using congrArg (fun t => φ ≫ t) hμ₁
          _ = φ ≫ η₂ := hη
          _ = (φ ≫ ψ) ≫ μ₂ := by
            simpa [Category.assoc] using congrArg (fun t => φ ≫ t) hμ₂.symm
      have hμμ : μ₁ = μ₂ := (hcomp L).1 hcompEq
      calc
        η₁ = ψ ≫ μ₁ := hμ₁.symm
        _ = ψ ≫ μ₂ := by exact congrArg (fun t => ψ ≫ t) hμμ
        _ = η₂ := hμ₂
    · intro η
      rcases (hcomp L).2 η with ⟨μ, hμ⟩
      refine ⟨ψ ≫ μ, ?_⟩
      simpa [Category.assoc] using hμ
  exact bφ

theorem of_comp_right
    {category : SmCorQ (k := k)}
    {F G H : LinearPST category}
    {φ : F ⟶ G} {ψ : G ⟶ H}
    (hφ : IsA1NisLocalEquivalence φ)
    (hcomp : IsA1NisLocalEquivalence (φ ≫ ψ)) :
    IsA1NisLocalEquivalence ψ := by
  intro L
  let bψ : Function.Bijective (fun η : H ⟶ L.toLinearPST => ψ ≫ η) := by
    refine ⟨?_, ?_⟩
    · intro η₁ η₂ hη
      have hcompEq : (φ ≫ ψ) ≫ η₁ = (φ ≫ ψ) ≫ η₂ := by
        simpa [Category.assoc] using congrArg (fun t => φ ≫ t) hη
      exact (hcomp L).1 hcompEq
    · intro η
      rcases (hcomp L).2 (φ ≫ η) with ⟨μ, hμ⟩
      refine ⟨μ, ?_⟩
      apply (hφ L).1
      simpa [Category.assoc] using hμ
  exact bψ

theorem of_isIso
    {category : SmCorQ (k := k)}
    {F G : LinearPST category}
    (φ : F ⟶ G)
    [CategoryTheory.IsIso φ] :
    IsA1NisLocalEquivalence φ := by
  intro L
  constructor
  · intro η₁ η₂ hη
    calc
      η₁ = inv φ ≫ (φ ≫ η₁) := by simp [Category.assoc]
      _ = inv φ ≫ (φ ≫ η₂) := by
        exact congrArg (fun t => inv φ ≫ t) hη
      _ = η₂ := by simp [Category.assoc]
  · intro η
    refine ⟨inv φ ≫ η, ?_⟩
    simp [Category.assoc]

/-- If `φ : F ⟶ G` admits a left inverse `r : G ⟶ F` (i.e., `φ ≫ r = 𝟙 F`)
that is itself a local equivalence, then `φ` is a local equivalence.

A split mono with a local-equivalence retraction is a local equivalence
because composition with a fixed local equivalence preserves the class
(two-out-of-three via `of_comp_left`). -/
theorem of_hasLeftInverse
    {category : SmCorQ (k := k)}
    {F G : LinearPST category}
    {φ : F ⟶ G}
    (r : G ⟶ F)
    (hsplit : φ ≫ r = 𝟙 F)
    (hr : IsA1NisLocalEquivalence r) :
    IsA1NisLocalEquivalence φ :=
  of_comp_left hr (hsplit ▸ id F)

/-- If `φ : F ⟶ G` admits a right inverse `r : G ⟶ F` (i.e., `r ≫ φ = 𝟙 G`)
that is itself a local equivalence, then `φ` is a local equivalence.

A split epi with a local-equivalence section is a local equivalence
because composition with a fixed local equivalence preserves the class
(two-out-of-three via `of_comp_right`). -/
theorem of_hasRightInverse
    {category : SmCorQ (k := k)}
    {F G : LinearPST category}
    {φ : F ⟶ G}
    (r : G ⟶ F)
    (hsplit : r ≫ φ = 𝟙 G)
    (hr : IsA1NisLocalEquivalence r) :
    IsA1NisLocalEquivalence φ :=
  of_comp_right hr (hsplit ▸ id G)

/-- Every local object inverts a local equivalence: precomposition with a local
equivalence `φ : F ⟶ G` induces a bijection `(G ⟶ L) → (F ⟶ L)` for any
`L : LinearA1NisLocalPST`.

This is the point-wise statement that `φ ∈ W_loc` means `Hom(G, L) ≅ Hom(F, L)`
for all local `L`, which later feeds the universal-property formulation. -/
theorem inverted_by_local_object
    {category : SmCorQ (k := k)}
    {F G : LinearPST category}
    {φ : F ⟶ G}
    (hφ : IsA1NisLocalEquivalence φ)
    (L : LinearA1NisLocalPST category) :
    Function.Bijective (fun η : G ⟶ L.toLinearPST => φ ≫ η) :=
  hφ L

/-- The local-equivalence predicate is *exactly* the test against local objects:
`φ` is a local equivalence iff every `L : LinearA1NisLocalPST` inverts `φ`.

This is the definition unfolded as a biconditional. -/
theorem iff_inverted_by_local_objects
    {category : SmCorQ (k := k)}
    {F G : LinearPST category}
    (φ : F ⟶ G) :
    IsA1NisLocalEquivalence φ ↔
      ∀ L : LinearA1NisLocalPST category,
        Function.Bijective (fun η : G ⟶ L.toLinearPST => φ ≫ η) :=
  Iff.rfl

end IsA1NisLocalEquivalence

/-- The Nisnevich descent generator is an `A1`+Nisnevich-local equivalence. -/
theorem nisnevichDescentGenerator_isA1NisLocalEquivalence
    {category : SmCorQ (k := k)}
    (square : NisnevichDistinguishedSquareDataQ category) :
    IsA1NisLocalEquivalence
    (F := square.descentCompatiblePairObjectLinear)
      (G := QtrLinear (category := category) square.base)
    (square.nisnevichDescentGeneratorMapLinear) := by
  intro L
  let hDescent := ((IsA1NisLocal_iff_QtrLinear_local L.toLinearPST).mp L.isA1NisLocal).2
  constructor
  · intro η₁ η₂ hcomp
    let η₁P : (QtrLinear (category := category) square.base).toPST ⟶ L.toPST := η₁
    let η₂P : (QtrLinear (category := category) square.base).toPST ⟶ L.toPST := η₂
    let ηopen₁ : (QtrLinear (category := category) square.openPiece).toPST ⟶ L.toPST :=
      (QtrMap (category := category) square.openToBaseTransfer) ≫ η₁P
    let ηpatch₁ : (QtrLinear (category := category) square.patchPiece).toPST ⟶ L.toPST :=
      (QtrMap (category := category) square.patchToBaseTransfer) ≫ η₁P
    let ηopen₂ : (QtrLinear (category := category) square.openPiece).toPST ⟶ L.toPST :=
      (QtrMap (category := category) square.openToBaseTransfer) ≫ η₂P
    let ηpatch₂ : (QtrLinear (category := category) square.patchPiece).toPST ⟶ L.toPST :=
      (QtrMap (category := category) square.patchToBaseTransfer) ≫ η₂P
    have hcompat₁ :
        (QtrMap (category := category) square.overlapToOpenTransfer) ≫ ηopen₁ =
          (QtrMap (category := category) square.overlapToPatchTransfer) ≫ ηpatch₁ := by
      simpa [ηopen₁, ηpatch₁, Category.assoc] using
        (NisnevichDistinguishedSquareDataQ.baseSection_overlap_compatible
          (square := square) (F := L.toPST) (ηbase := η₁P))
    rcases hDescent square ηopen₁ ηpatch₁ hcompat₁ with ⟨ηbase, hbase, huniq⟩
    have hcompP :
        square.nisnevichDescentGeneratorMapLinear ≫ η₁P =
          square.nisnevichDescentGeneratorMapLinear ≫ η₂P := by
      simpa [η₁P, η₂P] using hcomp
    have hopenEq : ηopen₁ = ηopen₂ := by
      calc
        ηopen₁ = (QtrMap (category := category) square.openToBaseTransfer) ≫ η₁P := by
            rfl
        _ = (square.descentTargetOpenInclusion ≫
              square.descentCompatiblePairQuotientMap ≫
              square.nisnevichDescentGeneratorMapLinear) ≫ η₁P := by
            rw [← Category.assoc]
            rw [Boundary.descentTargetOpenInclusion_comp_quotient_comp_generatorLinear (square := square)]
        _ = (square.descentTargetOpenInclusion ≫
              square.descentCompatiblePairQuotientMap ≫
              square.nisnevichDescentGeneratorMapLinear) ≫ η₂P := by
            simpa [Category.assoc] using
              congrArg
                (fun t => (square.descentTargetOpenInclusion ≫
                    square.descentCompatiblePairQuotientMap) ≫ t)
                hcompP
        _ = (QtrMap (category := category) square.openToBaseTransfer) ≫ η₂P := by
            rw [← Category.assoc]
            rw [Boundary.descentTargetOpenInclusion_comp_quotient_comp_generatorLinear (square := square)]
        _ = ηopen₂ := by rfl
    have hpatchEq : ηpatch₁ = ηpatch₂ := by
      calc
        ηpatch₁ = (QtrMap (category := category) square.patchToBaseTransfer) ≫ η₁P := by
            rfl
        _ = (square.descentTargetPatchInclusion ≫
              square.descentCompatiblePairQuotientMap ≫
              square.nisnevichDescentGeneratorMapLinear) ≫ η₁P := by
            rw [← Category.assoc]
            rw [Boundary.descentTargetPatchInclusion_comp_quotient_comp_generatorLinear (square := square)]
        _ = (square.descentTargetPatchInclusion ≫
              square.descentCompatiblePairQuotientMap ≫
              square.nisnevichDescentGeneratorMapLinear) ≫ η₂P := by
            simpa [Category.assoc] using
              congrArg
                (fun t => (square.descentTargetPatchInclusion ≫
                    square.descentCompatiblePairQuotientMap) ≫ t)
                hcompP
        _ = (QtrMap (category := category) square.patchToBaseTransfer) ≫ η₂P := by
            rw [← Category.assoc]
            rw [Boundary.descentTargetPatchInclusion_comp_quotient_comp_generatorLinear (square := square)]
        _ = ηpatch₂ := by rfl
    have hη₁ : η₁P = ηbase := by
      apply huniq
      constructor <;> rfl
    have hη₂ : η₂P = ηbase := by
      apply huniq
      constructor
      · simpa [ηopen₂] using hopenEq.symm
      · simpa [ηpatch₂] using hpatchEq.symm
    simpa [η₁P, η₂P] using hη₁.trans hη₂.symm
  · intro η
    let ηopen : (QtrLinear (category := category) square.openPiece).toPST ⟶ L.toPST :=
      square.descentTargetOpenInclusion ≫
        square.descentCompatiblePairQuotientMap ≫ η
    let ηpatch : (QtrLinear (category := category) square.patchPiece).toPST ⟶ L.toPST :=
      square.descentTargetPatchInclusion ≫
        square.descentCompatiblePairQuotientMap ≫ η
    have hcompat :
        (QtrMap (category := category) square.overlapToOpenTransfer) ≫ ηopen =
          (QtrMap (category := category) square.overlapToPatchTransfer) ≫ ηpatch := by
      simpa [ηopen, ηpatch, Category.assoc] using
        (NisnevichDistinguishedSquareDataQ.descentCompatiblePairObject_overlap_compat
          (square := square) (L := L.toLinearPST) η)
    rcases hDescent square ηopen ηpatch hcompat with ⟨ηbase, hbase, _⟩
    have hηlegs :
        square.descentTargetOpenInclusion ≫
            square.descentCompatiblePairQuotientMap ≫ η = ηopen ∧
          square.descentTargetPatchInclusion ≫
            square.descentCompatiblePairQuotientMap ≫ η = ηpatch := by
      constructor <;> rfl
    have hgenlegs :
        square.descentTargetOpenInclusion ≫
            square.descentCompatiblePairQuotientMap ≫
            (square.nisnevichDescentGeneratorMapLinear ≫ ηbase) = ηopen ∧
          square.descentTargetPatchInclusion ≫
            square.descentCompatiblePairQuotientMap ≫
            (square.nisnevichDescentGeneratorMapLinear ≫ ηbase) = ηpatch := by
      constructor
      · calc
          square.descentTargetOpenInclusion ≫
              square.descentCompatiblePairQuotientMap ≫
              (square.nisnevichDescentGeneratorMapLinear ≫ ηbase)
            = (square.descentTargetOpenInclusion ≫
                square.descentCompatiblePairQuotientMap ≫
                square.nisnevichDescentGeneratorMapLinear) ≫ ηbase := by
                  simp [Category.assoc]
        _ = (QtrMap (category := category) square.openToBaseTransfer) ≫ ηbase := by
              rw [Boundary.descentTargetOpenInclusion_comp_quotient_comp_generatorLinear (square := square)]
        _ = ηopen := by simpa [ηopen] using hbase.1
      · calc
          square.descentTargetPatchInclusion ≫
              square.descentCompatiblePairQuotientMap ≫
              (square.nisnevichDescentGeneratorMapLinear ≫ ηbase)
            = (square.descentTargetPatchInclusion ≫
                square.descentCompatiblePairQuotientMap ≫
                square.nisnevichDescentGeneratorMapLinear) ≫ ηbase := by
                  simp [Category.assoc]
        _ = (QtrMap (category := category) square.patchToBaseTransfer) ≫ ηbase := by
              rw [Boundary.descentTargetPatchInclusion_comp_quotient_comp_generatorLinear (square := square)]
        _ = ηpatch := by simpa [ηpatch] using hbase.2
    rcases (NisnevichDistinguishedSquareDataQ.descentCompatiblePair_desc
      (square := square) (L := L.toLinearPST) (ηU := ηopen) (ηV := ηpatch) hcompat) with
      ⟨ξ, hξ, hξuniq⟩
    have hηeq : η = ξ := hξuniq η hηlegs
    have hgeneq : square.nisnevichDescentGeneratorMapLinear ≫ ηbase = ξ :=
      hξuniq (square.nisnevichDescentGeneratorMapLinear ≫ ηbase)
        hgenlegs
    refine ⟨ηbase, ?_⟩
    calc
      square.nisnevichDescentGeneratorMapLinear ≫ ηbase = ξ := hgeneq
      _ = η := hηeq.symm

/-- The representable `A1`-projection generator is an `A1`+Nisnevich-local
equivalence on the honest `LinearPST` surface. -/
theorem representableA1Projection_isA1NisLocalEquivalence
    {category : SmCorQ (k := k)}
    (X : Geometry.SmSchemeOver k)
    (D : FiniteIrreducibleComponentDecomposition (productWithA1 X)) :
    IsA1NisLocalEquivalence
      (F := QtrLinear (category := category) (productWithA1 X))
      (G := QtrLinear (category := category) X)
      (show QtrLinear (category := category) (productWithA1 X) ⟶
          QtrLinear (category := category) X from
        projectionToBase_QtrMapOfDecomposition category X D) := by
  intro L
  exact
    ((IsA1NisLocal_iff_QtrLinear_local L.toLinearPST).mp L.isA1NisLocal).1 X D

/-- Both basic geometric generator families land in `IsA1NisLocalEquivalence`.

These are the two fundamental generator maps from which the motivic
localization is built:

* **A¹ projection generators**: `Q_tr(X × A¹) → Q_tr(X)`.
* **Nisnevich descent generators**: `Comp(U,V;W) → Q_tr(X)` arising from a
  Nisnevich distinguished square.

Neither the localization functor nor motives are defined here; this is purely
the statement that the generators already constructed satisfy the
local-equivalence predicate. -/
theorem basicGenerators_areA1NisLocalEquivalences
    {category : SmCorQ (k := k)} :
    (∀ (X : Geometry.SmSchemeOver k)
       (D : FiniteIrreducibleComponentDecomposition (productWithA1 X)),
        IsA1NisLocalEquivalence
          (F := QtrLinear (category := category) (productWithA1 X))
          (G := QtrLinear (category := category) X)
          (projectionToBase_QtrMapOfDecomposition category X D)) ∧
    (∀ (square : NisnevichDistinguishedSquareDataQ category),
        IsA1NisLocalEquivalence
          (F := square.descentCompatiblePairObjectLinear)
          (G := QtrLinear (category := category) square.base)
          square.nisnevichDescentGeneratorMapLinear) :=
  ⟨fun X D => representableA1Projection_isA1NisLocalEquivalence X D,
   fun square => nisnevichDescentGenerator_isA1NisLocalEquivalence square⟩

/-- Canonical-route bundled linear presheaves with transfers that are both
`A1`-local and Nisnevich-local. -/
abbrev CanonicalA1NisLocalPST
    (composition : Boundary.CanonicalCompositionData (k := k)) :=
  LinearA1NisLocalPST (Boundary.canonicalCategory composition)

/-- Canonical-route local equivalences on `LinearPST (canonicalSmCorQ)`. -/
def IsCanonicalA1NisLocalEquivalence
    (composition : Boundary.CanonicalCompositionData (k := k))
    {F G : LinearPST (Boundary.canonicalCategory composition)}
  (φ : F ⟶ G) :=
  IsA1NisLocalEquivalence φ

/-- The representable `A1`-projection generator is a canonical
`A1`+Nisnevich-local equivalence. -/
theorem representableA1Projection_isCanonicalA1NisLocalEquivalence
    (composition : Boundary.CanonicalCompositionData (k := k))
    (X : Geometry.SmSchemeOver k)
    (D : FiniteIrreducibleComponentDecomposition (productWithA1 X)) :
    IsCanonicalA1NisLocalEquivalence composition
      (F := QtrLinear (category := Boundary.canonicalCategory composition) (productWithA1 X))
      (G := QtrLinear (category := Boundary.canonicalCategory composition) X)
      (show QtrLinear (category := Boundary.canonicalCategory composition) (productWithA1 X) ⟶
          QtrLinear (category := Boundary.canonicalCategory composition) X from
        projectionToBase_QtrMapOfDecomposition
          (Boundary.canonicalCategory composition) X D) :=
  representableA1Projection_isA1NisLocalEquivalence
    (category := Boundary.canonicalCategory composition) X D

/-- The canonical Nisnevich descent generator is a canonical `A1`+Nisnevich-local
equivalence. -/
theorem canonicalNisnevichDescentGenerator_isCanonicalA1NisLocalEquivalence
    (composition : Boundary.CanonicalCompositionData (k := k))
    (square : NisnevichDistinguishedSquareDataQ (Boundary.canonicalCategory composition)) :
    IsCanonicalA1NisLocalEquivalence composition
      (F := square.descentCompatiblePairObjectLinear)
      (G := QtrLinear (category := Boundary.canonicalCategory composition) square.base)
      square.nisnevichDescentGeneratorMapLinear :=
  nisnevichDescentGenerator_isA1NisLocalEquivalence
    (category := Boundary.canonicalCategory composition) square

/-- On the canonical route, both basic generator families land in the canonical
`A1`+Nisnevich local-equivalence class. -/
theorem canonicalBasicGenerators_areA1NisLocalEquivalences
    (composition : Boundary.CanonicalCompositionData (k := k)) :
    (∀ (X : Geometry.SmSchemeOver k)
       (D : FiniteIrreducibleComponentDecomposition (productWithA1 X)),
        IsCanonicalA1NisLocalEquivalence composition
          (F := QtrLinear (category := Boundary.canonicalCategory composition) (productWithA1 X))
          (G := QtrLinear (category := Boundary.canonicalCategory composition) X)
          (projectionToBase_QtrMapOfDecomposition
            (Boundary.canonicalCategory composition) X D)) ∧
    (∀ (square : NisnevichDistinguishedSquareDataQ (Boundary.canonicalCategory composition)),
        IsCanonicalA1NisLocalEquivalence composition
          (F := square.descentCompatiblePairObjectLinear)
          (G := QtrLinear (category := Boundary.canonicalCategory composition) square.base)
          square.nisnevichDescentGeneratorMapLinear) :=
  ⟨fun X D => representableA1Projection_isCanonicalA1NisLocalEquivalence composition X D,
   fun square => canonicalNisnevichDescentGenerator_isCanonicalA1NisLocalEquivalence
     composition square⟩

/-- Primitive canonical-route `A1` and Nisnevich generators over
`canonicalSmCorQ`. -/
inductive CanonicalA1NisGenerator
    (composition : Boundary.CanonicalCompositionData (k := k)) where
  | a1Projection (X : Geometry.SmSchemeOver k)
      (D : FiniteIrreducibleComponentDecomposition (productWithA1 X))
  | nisnevichDescent
      (square : NisnevichDistinguishedSquareDataQ
        (Boundary.canonicalCategory composition))

/-- The canonical generator presentation for the `A1` projections and
Nisnevich descent maps over `canonicalSmCorQ`. -/
def canonicalA1NisGenerators
    (composition : Boundary.CanonicalCompositionData (k := k)) :
    LocalizingMorphismPresentationQ (Boundary.canonicalCategory composition) where
  Generator := CanonicalA1NisGenerator composition
  data := fun
    | .a1Projection X D =>
        ⟨Qtr (category := Boundary.canonicalCategory composition) (productWithA1 X),
          Qtr (category := Boundary.canonicalCategory composition) X,
          projectionToBase_QtrMapOfDecomposition
            (Boundary.canonicalCategory composition) X D⟩
    | .nisnevichDescent square =>
        ⟨square.descentCompatiblePairObject,
          Qtr (category := Boundary.canonicalCategory composition) square.base,
          square.nisnevichDescentGeneratorMapCanonical⟩

/-- The canonical `W_{A1,Nis}` local-equivalence predicate on
`LinearPST (canonicalSmCorQ)`, expressed through the Bousfield-`W` class of the
bundled canonical local objects. -/
def canonicalA1NisLocalEquivalences
    (composition : Boundary.CanonicalCompositionData (k := k))
    {F G : LinearPST (Boundary.canonicalCategory composition)}
    (φ : F ⟶ G) :=
  Localization.LeftBousfield.W
    (· ∈ Set.range
      (LinearA1NisLocalPST.inclusion (Boundary.canonicalCategory composition)).obj) φ

/-- The generated canonical weak-equivalence class
`W_{A1,Nis}^{can} = \langle X × A1 → X, \text{Nis descent} \rangle`. -/
def canonicalA1NisWeakEquivalences
    (composition : Boundary.CanonicalCompositionData (k := k))
    {F G : PST (Boundary.canonicalCategory composition)}
  (φ : F ⟶ G) :=
  Nonempty (GeneratedWeakEquivalenceQ (canonicalA1NisGenerators composition) φ)

/-- A retract datum between two morphisms in the arrow category, written out
concretely so the generated weak-equivalence closure does not hide retract
stability behind a naming convention. -/
structure WeakEquivalenceRetract
    {C : Type*} [Category C]
    {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') where
  leftTo : X ⟶ X'
  leftFrom : X' ⟶ X
  rightTo : Y ⟶ Y'
  rightFrom : Y' ⟶ Y
  left_retract : leftTo ≫ leftFrom = 𝟙 X
  right_retract : rightTo ≫ rightFrom = 𝟙 Y
  square_to : f ≫ rightTo = leftTo ≫ g
  square_from : g ≫ rightFrom = leftFrom ≫ f

/-- Closure operations imposed on the A1/Nis generated weak-equivalence class.
For `LinearPST` these operations are proved for the Bousfield biorthogonal
class generated by the primitive A1/Nis maps. -/
structure CanonicalA1NisWeakEquivalenceClosure
    (composition : Boundary.CanonicalCompositionData (k := k))
    (W : MorphismProperty (LinearPST (Boundary.canonicalCategory composition))) : Prop where
  contains_generators :
    ∀ {F G : LinearPST (Boundary.canonicalCategory composition)} (φ : F ⟶ G),
      canonicalA1NisWeakEquivalences composition (F := F.toPST) (G := G.toPST) φ →
        W φ
  identities :
    ∀ X : LinearPST (Boundary.canonicalCategory composition), W (𝟙 X)
  closed_under_composition :
    ∀ {X Y Z : LinearPST (Boundary.canonicalCategory composition)}
      (f : X ⟶ Y) (g : Y ⟶ Z), W f → W g → W (f ≫ g)
  two_out_of_three_left :
    ∀ {X Y Z : LinearPST (Boundary.canonicalCategory composition)}
      (f : X ⟶ Y) (g : Y ⟶ Z), W g → W (f ≫ g) → W f
  two_out_of_three_right :
    ∀ {X Y Z : LinearPST (Boundary.canonicalCategory composition)}
      (f : X ⟶ Y) (g : Y ⟶ Z), W f → W (f ≫ g) → W g
  retracts :
    ∀ {X Y X' Y' : LinearPST (Boundary.canonicalCategory composition)}
      {f : X ⟶ Y} {g : X' ⟶ Y'},
        WeakEquivalenceRetract f g → W g → W f

/-- Linear presheaves that are local for the primitive canonical `A1` and
Nisnevich generators.  This is the right orthogonal side of the Bousfield
class generated by the maps in `canonicalA1NisGenerators`: the first clause says
that every `A1` projection generator is inverted, and the second clause is the
Yoneda form of inverting every Nisnevich descent generator. -/
def canonicalA1NisGeneratedLocalObject
    (composition : Boundary.CanonicalCompositionData (k := k))
    (L : LinearPST (Boundary.canonicalCategory composition)) : Prop :=
  (∀ (X : Geometry.SmSchemeOver k)
    (D : FiniteIrreducibleComponentDecomposition (productWithA1 X)),
    Function.Bijective
      (fun η : (QtrLinear (category := Boundary.canonicalCategory composition) X).toPST ⟶
          L.toPST =>
        (projectionToBase_QtrMapOfDecomposition
          (Boundary.canonicalCategory composition) X D) ≫ η)) ∧
  (∀ square : NisnevichDistinguishedSquareDataQ (Boundary.canonicalCategory composition),
    ∀ (ηopen : (QtrLinear (category := Boundary.canonicalCategory composition)
        square.openPiece).toPST ⟶ L.toPST)
      (ηpatch : (QtrLinear (category := Boundary.canonicalCategory composition)
        square.patchPiece).toPST ⟶ L.toPST),
      (QtrMap (category := Boundary.canonicalCategory composition)
          square.overlapToOpenTransfer) ≫ ηopen =
        (QtrMap (category := Boundary.canonicalCategory composition)
          square.overlapToPatchTransfer) ≫ ηpatch →
      ∃! ηbase : (QtrLinear (category := Boundary.canonicalCategory composition)
          square.base).toPST ⟶ L.toPST,
        (QtrMap (category := Boundary.canonicalCategory composition)
            square.openToBaseTransfer) ≫ ηbase = ηopen ∧
          (QtrMap (category := Boundary.canonicalCategory composition)
            square.patchToBaseTransfer) ≫ ηbase = ηpatch)

/-- Generated-local objects are exactly the existing canonical `A1`/Nis-local
linear presheaves.  The proof unfolds both sides to the primitive `A1`
projection and Nisnevich descent conditions. -/
theorem canonicalA1NisGeneratedLocalObject_iff_isLocal
    (composition : Boundary.CanonicalCompositionData (k := k))
    (L : LinearPST (Boundary.canonicalCategory composition)) :
    canonicalA1NisGeneratedLocalObject composition L ↔
      IsLinearA1NisLocal L := by
  change canonicalA1NisGeneratedLocalObject composition L ↔
    IsA1NisLocal L.toPST
  exact (IsCanonicalA1NisLocal_iff_QtrLinear_local composition L).symm

/-- The generated A1/Nis weak-equivalence class in the Bousfield sense: a map is
generated-weak-equivalent when every object local for the primitive canonical
generators inverts it.  This is a genuine biorthogonal construction from the
generator-local objects; its equivalence with `canonicalA1NisLocalEquivalences`
is proved below. -/
def canonicalA1NisGeneratedWeakEquivalences
    (composition : Boundary.CanonicalCompositionData (k := k))
    {F G : LinearPST (Boundary.canonicalCategory composition)}
  (φ : F ⟶ G) :=
  ∀ L : LinearPST (Boundary.canonicalCategory composition),
    canonicalA1NisGeneratedLocalObject composition L →
      Function.Bijective (fun η : G ⟶ L => φ ≫ η)

private def canonicalA1NisLocalEquivalencesProperty
    (composition : Boundary.CanonicalCompositionData (k := k)) :
    MorphismProperty (LinearPST (Boundary.canonicalCategory composition)) :=
  fun _ _ φ => canonicalA1NisLocalEquivalences composition φ

private def canonicalA1NisWeakEquivalencesProperty
    (composition : Boundary.CanonicalCompositionData (k := k)) :
    MorphismProperty (LinearPST (Boundary.canonicalCategory composition)) :=
  fun F G φ =>
    canonicalA1NisWeakEquivalences composition (F := F.toPST) (G := G.toPST) φ

private def canonicalA1NisGeneratedWeakEquivalencesProperty
    (composition : Boundary.CanonicalCompositionData (k := k)) :
    MorphismProperty (LinearPST (Boundary.canonicalCategory composition)) :=
  fun _ _ φ => canonicalA1NisGeneratedWeakEquivalences composition φ

/-- The honest canonical `A1`/Nisnevich localization of
`LinearPST (canonicalSmCorQ)`, formed by Mathlib's localization construction at
the canonical local-equivalence class. -/
abbrev canonicalA1NisLocalization
    (composition : Boundary.CanonicalCompositionData (k := k)) :=
  (canonicalA1NisLocalEquivalencesProperty composition).Localization

/-- The canonical localization functor
`LinearPST (canonicalSmCorQ) ⥤ canonicalA1NisLocalization`. -/
def canonicalA1NisLocalizationFunctor

theorem canonicalA1NisLocalEquivalences_iff
    (composition : Boundary.CanonicalCompositionData (k := k))
    {F G : LinearPST (Boundary.canonicalCategory composition)}
    (φ : F ⟶ G) :
    canonicalA1NisLocalEquivalences composition φ ↔
      IsCanonicalA1NisLocalEquivalence composition φ := by
  constructor
  · intro hφ L
    exact hφ ((LinearA1NisLocalPST.inclusion
      (Boundary.canonicalCategory composition)).obj L) ⟨L, rfl⟩
  · intro hφ Z ⟨L, hL⟩
    rw [← hL]
    exact hφ L

/-- Universal property of the canonical `A1`/Nisnevich localization: for every
target category `D`, precomposition with the canonical localization functor is
an equivalence from functors out of the localization to functors that invert
the canonical local-equivalence class. -/
def canonicalA1NisLocalization_universalProperty
    (composition : Boundary.CanonicalCompositionData (k := k))
    (D : Type*) [Category D] :
    (canonicalA1NisLocalization composition ⥤ D) ≌
      (canonicalA1NisLocalEquivalencesProperty composition).FunctorsInverting D :=
  CategoryTheory.Localization.functorEquivalence
    (canonicalA1NisLocalizationFunctor composition)
    (canonicalA1NisLocalEquivalencesProperty composition)
    D


private theorem generatedWeakEquivalence_invertedByCanonicalLocal
    (composition : Boundary.CanonicalCompositionData (k := k))
    {F G : PST (Boundary.canonicalCategory composition)}
    {φ : F ⟶ G}
    (hφ : GeneratedWeakEquivalenceQ (canonicalA1NisGenerators composition) φ) :
    ∀ (L : CanonicalA1NisLocalPST composition),
      Function.Bijective (fun η : G ⟶ L.toPST => φ ≫ η) := by
  induction hφ with
  | ofGenerator g =>
      cases g with
      | a1Projection X D =>
          intro L
          have hloc :
              canonicalA1NisLocalEquivalences composition
                (F := QtrLinear (category := Boundary.canonicalCategory composition) (productWithA1 X))
                (G := QtrLinear (category := Boundary.canonicalCategory composition) X)
                (show QtrLinear (category := Boundary.canonicalCategory composition) (productWithA1 X) ⟶
                    QtrLinear (category := Boundary.canonicalCategory composition) X from
                  projectionToBase_QtrMapOfDecomposition
                    (Boundary.canonicalCategory composition) X D) := by
            rw [canonicalA1NisLocalEquivalences_iff]
            exact representableA1Projection_isCanonicalA1NisLocalEquivalence composition X D
          exact hloc
            ((LinearA1NisLocalPST.inclusion (Boundary.canonicalCategory composition)).obj L)
            ⟨L, rfl⟩
      | nisnevichDescent square =>
          intro L
          have hloc :
              canonicalA1NisLocalEquivalences composition
                (F := square.descentCompatiblePairObjectLinear)
                (G := QtrLinear (category := Boundary.canonicalCategory composition) square.base)
                square.nisnevichDescentGeneratorMapLinear := by
            rw [canonicalA1NisLocalEquivalences_iff]
            exact canonicalNisnevichDescentGenerator_isCanonicalA1NisLocalEquivalence
              composition square
          simpa [NisnevichDistinguishedSquareDataQ.nisnevichDescentGeneratorMapLinear,
            NisnevichDistinguishedSquareDataQ.nisnevichDescentGeneratorMapCanonical] using
            hloc ((LinearA1NisLocalPST.inclusion (Boundary.canonicalCategory composition)).obj L)
              ⟨L, rfl⟩
  | id X =>
      intro L
      constructor
      · intro η₁ η₂ hη
        exact hη
      · intro η
        refine ⟨η, ?_⟩
        simp
  | comp hf hg ihf ihg =>
      intro L
      rename_i X Y Z f g
      let bf := ihf L
      let bg := ihg L
      constructor
      · intro η₁ η₂ hη
        apply bg.1
        apply bf.1
        simpa [Category.assoc] using hη
      · intro η
        rcases bf.2 η with ⟨θ, hθ⟩
        rcases bg.2 θ with ⟨μ, hμ⟩
        refine ⟨μ, ?_⟩
        calc
          (fun η => (f ≫ g) ≫ η) μ = f ≫ ((fun η => g ≫ η) μ) := by
            simp [Category.assoc]
          _ = f ≫ θ := by simpa [Category.assoc] using congrArg (fun t => f ≫ t) hμ
          _ = η := hθ

/-- Every generator-built canonical weak equivalence between linear presheaves
is already a canonical local equivalence. -/
theorem canonicalA1NisWeakEquivalences_le_localEquivalences
    (composition : Boundary.CanonicalCompositionData (k := k)) :
    ∀ {F G : LinearPST (Boundary.canonicalCategory composition)} (φ : F ⟶ G),
      canonicalA1NisWeakEquivalences composition (F := F.toPST) (G := G.toPST) φ →
        canonicalA1NisLocalEquivalences composition φ := by
  intro F G φ hφ
  rcases hφ with ⟨hφ⟩
  intro Z hZ
  rcases hZ with ⟨L, rfl⟩
  exact generatedWeakEquivalence_invertedByCanonicalLocal composition hφ L

/-- The raw generator-built class sits inside the Bousfield-generated
weak-equivalence class. -/
theorem canonicalA1NisWeakEquivalences_le_generatedWeakEquivalences
    (composition : Boundary.CanonicalCompositionData (k := k)) :
    ∀ {F G : LinearPST (Boundary.canonicalCategory composition)} (φ : F ⟶ G),
      canonicalA1NisWeakEquivalences composition (F := F.toPST) (G := G.toPST) φ →
        canonicalA1NisGeneratedWeakEquivalences composition φ := by
  intro F G φ hφ
  rcases hφ with ⟨hφ⟩
  intro L hL
  have hLocal : IsLinearA1NisLocal L :=
    (canonicalA1NisGeneratedLocalObject_iff_isLocal composition L).mp hL
  exact
    generatedWeakEquivalence_invertedByCanonicalLocal composition hφ
      (⟨L, hLocal⟩ : CanonicalA1NisLocalPST composition)

/-- The Bousfield-generated A1/Nis weak-equivalence class is exactly closed
under the requested finite weak-equivalence operations in `LinearPST`. -/
theorem canonicalA1NisGeneratedWeakEquivalences_closure
    (composition : Boundary.CanonicalCompositionData (k := k)) :
    CanonicalA1NisWeakEquivalenceClosure composition
      (canonicalA1NisGeneratedWeakEquivalencesProperty composition) := by
  refine
    { contains_generators := ?_
      identities := ?_
      closed_under_composition := ?_
      two_out_of_three_left := ?_
      two_out_of_three_right := ?_
      retracts := ?_ }
  · intro F G φ hφ
    exact canonicalA1NisWeakEquivalences_le_generatedWeakEquivalences composition φ hφ
  · intro X
    intro L _hL
    constructor
    · intro η₁ η₂ hη
      exact hη
    · intro η
      refine ⟨η, ?_⟩
      simp
  · intro X Y Z f g hf hg
    intro L hL
    let bf : Function.Bijective (fun η : Y ⟶ L => f ≫ η) := hf L hL
    let bg : Function.Bijective (fun η : Z ⟶ L => g ≫ η) := hg L hL
    constructor
    · intro η₁ η₂ hη
      apply bg.1
      apply bf.1
      simpa [Category.assoc] using hη
    · intro η
      rcases bf.2 η with ⟨θ, hθ⟩
      rcases bg.2 θ with ⟨μ, hμ⟩
      refine ⟨μ, ?_⟩
      calc
        (f ≫ g) ≫ μ = f ≫ (g ≫ μ) := by simp [Category.assoc]
        _ = f ≫ θ := by exact congrArg (fun t => f ≫ t) hμ
        _ = η := hθ
  · intro X Y Z f g hg hfg
    intro L hL
    let bg : Function.Bijective (fun η : Z ⟶ L => g ≫ η) := hg L hL
    let bfg : Function.Bijective (fun η : Z ⟶ L => (f ≫ g) ≫ η) := hfg L hL
    constructor
    · intro η₁ η₂ hη
      rcases bg.2 η₁ with ⟨μ₁, hμ₁⟩
      rcases bg.2 η₂ with ⟨μ₂, hμ₂⟩
      have hcomp : (f ≫ g) ≫ μ₁ = (f ≫ g) ≫ μ₂ := by
        calc
          (f ≫ g) ≫ μ₁ = f ≫ η₁ := by
            simpa [Category.assoc] using congrArg (fun t => f ≫ t) hμ₁
          _ = f ≫ η₂ := hη
          _ = (f ≫ g) ≫ μ₂ := by
            simpa [Category.assoc] using congrArg (fun t => f ≫ t) hμ₂.symm
      have hμ : μ₁ = μ₂ := bfg.1 hcomp
      calc
        η₁ = g ≫ μ₁ := hμ₁.symm
        _ = g ≫ μ₂ := by exact congrArg (fun t => g ≫ t) hμ
        _ = η₂ := hμ₂
    · intro η
      rcases bfg.2 η with ⟨μ, hμ⟩
      refine ⟨g ≫ μ, ?_⟩
      simpa [Category.assoc] using hμ
  · intro X Y Z f g hf hfg
    intro L hL
    let bf : Function.Bijective (fun η : Y ⟶ L => f ≫ η) := hf L hL
    let bfg : Function.Bijective (fun η : Z ⟶ L => (f ≫ g) ≫ η) := hfg L hL
    constructor
    · intro η₁ η₂ hη
      have hcomp : (f ≫ g) ≫ η₁ = (f ≫ g) ≫ η₂ := by
        simpa [Category.assoc] using congrArg (fun t => f ≫ t) hη
      exact bfg.1 hcomp
    · intro η
      rcases bfg.2 (f ≫ η) with ⟨μ, hμ⟩
      refine ⟨μ, ?_⟩
      apply bf.1
      simpa [Category.assoc] using hμ
  · intro X Y X' Y' f g r hg
    intro L hL
    let bg : Function.Bijective
        (fun η : Y' ⟶ L => g ≫ η) := hg L hL
    constructor
    · intro η₁ η₂ hη
      have hright :
          r.rightFrom ≫ η₁ = r.rightFrom ≫ η₂ := by
        apply bg.1
        calc
          g ≫ (r.rightFrom ≫ η₁)
              = r.leftFrom ≫ (f ≫ η₁) := by
                simpa [Category.assoc] using congrArg (fun t => t ≫ η₁) r.square_from
          _ = r.leftFrom ≫ (f ≫ η₂) := by simpa [Category.assoc] using congrArg (fun t => r.leftFrom ≫ t) hη
          _ = g ≫ (r.rightFrom ≫ η₂) := by
                simpa [Category.assoc] using
                  (congrArg (fun t => t ≫ η₂) r.square_from).symm
      calc
        η₁ = r.rightTo ≫ (r.rightFrom ≫ η₁) := by
          simpa [Category.assoc] using congrArg (fun t => t ≫ η₁) r.right_retract.symm
        _ = r.rightTo ≫ (r.rightFrom ≫ η₂) := by rw [hright]
        _ = (r.rightTo ≫ r.rightFrom) ≫ η₂ := by simp [Category.assoc]
        _ = η₂ := by simpa [Category.assoc] using congrArg (fun t => t ≫ η₂) r.right_retract
    · intro α
      rcases bg.2 (r.leftFrom ≫ α) with ⟨μ, hμ⟩
      refine ⟨r.rightTo ≫ μ, ?_⟩
      calc
        f ≫ (r.rightTo ≫ μ) = r.leftTo ≫ (g ≫ μ) := by
          simpa [Category.assoc] using congrArg (fun t => t ≫ μ) r.square_to
        _ = r.leftTo ≫ (r.leftFrom ≫ α) := by simpa [Category.assoc] using congrArg (fun t => r.leftTo ≫ t) hμ
        _ = (r.leftTo ≫ r.leftFrom) ≫ α := by simp [Category.assoc]
        _ = α := by simpa [Category.assoc] using congrArg (fun t => t ≫ α) r.left_retract

/-- The primitive generator-built maps lie in the Bousfield-generated
canonical weak-equivalence class. -/
theorem canonicalA1NisGenerators_le_generatedWeakEquivalences
    (composition : Boundary.CanonicalCompositionData (k := k)) :
    ∀ {F G : LinearPST (Boundary.canonicalCategory composition)} (φ : F ⟶ G),
      canonicalA1NisWeakEquivalences composition (F := F.toPST) (G := G.toPST) φ →
        canonicalA1NisGeneratedWeakEquivalences composition φ :=
  canonicalA1NisWeakEquivalences_le_generatedWeakEquivalences composition

/-- Identities are generated canonical `A1`/Nis weak equivalences. -/
theorem canonicalA1NisGeneratedWeakEquivalences_id
    (composition : Boundary.CanonicalCompositionData (k := k))
    (X : LinearPST (Boundary.canonicalCategory composition)) :
    canonicalA1NisGeneratedWeakEquivalences composition (𝟙 X) :=
  (canonicalA1NisGeneratedWeakEquivalences_closure composition).identities X

/-- Generated canonical `A1`/Nis weak equivalences are closed under
composition. -/
theorem canonicalA1NisGeneratedWeakEquivalences_comp
    (composition : Boundary.CanonicalCompositionData (k := k))
    {X Y Z : LinearPST (Boundary.canonicalCategory composition)}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : canonicalA1NisGeneratedWeakEquivalences composition f)
    (hg : canonicalA1NisGeneratedWeakEquivalences composition g) :
    canonicalA1NisGeneratedWeakEquivalences composition (f ≫ g) :=
  (canonicalA1NisGeneratedWeakEquivalences_closure composition).closed_under_composition
    f g hf hg

/-- Generated canonical `A1`/Nis weak equivalences satisfy two-out-of-three. -/
theorem canonicalA1NisGeneratedWeakEquivalences_two_of_three
    (composition : Boundary.CanonicalCompositionData (k := k))
    {X Y Z : LinearPST (Boundary.canonicalCategory composition)}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (canonicalA1NisGeneratedWeakEquivalences composition g →
      canonicalA1NisGeneratedWeakEquivalences composition (f ≫ g) →
        canonicalA1NisGeneratedWeakEquivalences composition f) ∧
    (canonicalA1NisGeneratedWeakEquivalences composition f →
      canonicalA1NisGeneratedWeakEquivalences composition (f ≫ g) →
        canonicalA1NisGeneratedWeakEquivalences composition g) :=
  ⟨(canonicalA1NisGeneratedWeakEquivalences_closure composition).two_out_of_three_left f g,
   (canonicalA1NisGeneratedWeakEquivalences_closure composition).two_out_of_three_right f g⟩

/-- Generated canonical `A1`/Nis weak equivalences are stable under retracts in
the arrow category. -/
theorem canonicalA1NisGeneratedWeakEquivalences_retract
    (composition : Boundary.CanonicalCompositionData (k := k))
    {X Y X' Y' : LinearPST (Boundary.canonicalCategory composition)}
    {f : X ⟶ Y} {g : X' ⟶ Y'}
    (r : WeakEquivalenceRetract f g)
    (hg : canonicalA1NisGeneratedWeakEquivalences composition g) :
    canonicalA1NisGeneratedWeakEquivalences composition f :=
  (canonicalA1NisGeneratedWeakEquivalences_closure composition).retracts r hg

/-- The Bousfield-generated A1/Nis weak-equivalence class is contained in the
canonical local-equivalence class. -/
theorem canonicalA1NisGenerators_le_localEquivalences
    (composition : Boundary.CanonicalCompositionData (k := k)) :
    ∀ {F G : LinearPST (Boundary.canonicalCategory composition)} (φ : F ⟶ G),
      canonicalA1NisGeneratedWeakEquivalences composition φ →
        canonicalA1NisLocalEquivalences composition φ := by
  intro F G φ hφ
  rw [canonicalA1NisLocalEquivalences_iff]
  intro L
  exact hφ L.toLinearPST
    ((canonicalA1NisGeneratedLocalObject_iff_isLocal composition L.toLinearPST).mpr L.2)

/-- Conversely, the canonical local-equivalence class is contained in the
Bousfield-generated A1/Nis weak-equivalence class. -/
theorem canonicalA1NisLocalEquivalences_le_generatedWeakEquivalences
    (composition : Boundary.CanonicalCompositionData (k := k)) :
    ∀ {F G : LinearPST (Boundary.canonicalCategory composition)} (φ : F ⟶ G),
      canonicalA1NisLocalEquivalences composition φ →
        canonicalA1NisGeneratedWeakEquivalences composition φ := by
  intro F G φ hφ
  intro L hL
  have hLocal : IsLinearA1NisLocal L :=
    (canonicalA1NisGeneratedLocalObject_iff_isLocal composition L).mp hL
  exact ((canonicalA1NisLocalEquivalences_iff composition φ).mp hφ)
    (⟨L, hLocal⟩ : CanonicalA1NisLocalPST composition)

/-- The Bousfield-generated A1/Nis weak-equivalence class and the canonical
local-equivalence class coincide on the canonical route. -/
theorem canonicalA1NisGeneratedWeakEquivalences_eq_localEquivalences
    (composition : Boundary.CanonicalCompositionData (k := k)) :
    ∀ {F G : LinearPST (Boundary.canonicalCategory composition)} (φ : F ⟶ G),
      canonicalA1NisGeneratedWeakEquivalences composition φ ↔
        canonicalA1NisLocalEquivalences composition φ := by
  intro F G φ
  constructor
  · exact canonicalA1NisGenerators_le_localEquivalences composition φ
  · exact canonicalA1NisLocalEquivalences_le_generatedWeakEquivalences composition φ

/-- The universal property of the canonical localization can be restated using
the Bousfield-generated A1/Nis weak-equivalence class. -/
def canonicalA1NisLocalization_universalProperty_generated
    (composition : Boundary.CanonicalCompositionData (k := k))
    (D : Type*) [Category D] :
    (canonicalA1NisLocalization composition ⥤ D) ≌
      (canonicalA1NisGeneratedWeakEquivalencesProperty composition).FunctorsInverting D := by
  let hgen_le_hloc : canonicalA1NisGeneratedWeakEquivalencesProperty composition ≤
      canonicalA1NisLocalEquivalencesProperty composition := by
    intro F G φ hφ
    exact canonicalA1NisGenerators_le_localEquivalences composition φ hφ
  let hloc_le_hgen : canonicalA1NisLocalEquivalencesProperty composition ≤
      canonicalA1NisGeneratedWeakEquivalencesProperty composition := by
    intro F G φ hφ
    exact canonicalA1NisLocalEquivalences_le_generatedWeakEquivalences composition φ hφ
  let transport :
      (canonicalA1NisLocalEquivalencesProperty composition).FunctorsInverting D ≌
        (canonicalA1NisGeneratedWeakEquivalencesProperty composition).FunctorsInverting D := by
    refine
      { functor :=
          { obj := fun F =>
              MorphismProperty.FunctorsInverting.mk F.1
                (MorphismProperty.IsInvertedBy.of_le _ _ F.1 F.2 hgen_le_hloc)
            map := fun η => η }
        inverse :=
          { obj := fun F =>
              MorphismProperty.FunctorsInverting.mk F.1
                (MorphismProperty.IsInvertedBy.of_le _ _ F.1 F.2 hloc_le_hgen)
            map := fun η => η }
        unitIso := NatIso.ofComponents (fun F => Iso.refl F) (fun η => by
          ext X
          change η.app X ≫ 𝟙 _ = 𝟙 _ ≫ η.app X
          exact ((Category.comp_id (η.app X)).trans (Category.id_comp (η.app X)).symm))
        counitIso := NatIso.ofComponents (fun F => Iso.refl F) (fun η => by
          ext X
          change η.app X ≫ 𝟙 _ = 𝟙 _ ≫ η.app X
          exact ((Category.comp_id (η.app X)).trans (Category.id_comp (η.app X)).symm))
        functor_unitIso_comp := by
          intro F
          ext X
          change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
          simp }
  let uprop :
      (canonicalA1NisLocalization composition ⥤ D) ≌
        (canonicalA1NisLocalEquivalencesProperty composition).FunctorsInverting D :=
    canonicalA1NisLocalization_universalProperty composition D
  exact uprop.trans transport

/-- The primitive canonical `A1` and Nisnevich generator maps are members of
the generated weak-equivalence class `W_{A1,Nis}^{can}`. -/
theorem canonicalA1NisGenerators_generate_canonicalA1NisWeakEquivalences
    (composition : Boundary.CanonicalCompositionData (k := k)) :
    (∀ (X : Geometry.SmSchemeOver k)
       (D : FiniteIrreducibleComponentDecomposition (productWithA1 X)),
        canonicalA1NisWeakEquivalences composition
          (projectionToBase_QtrMapOfDecomposition
            (Boundary.canonicalCategory composition) X D)) ∧
    (∀ (square : NisnevichDistinguishedSquareDataQ (Boundary.canonicalCategory composition)),
        canonicalA1NisWeakEquivalences composition
          square.nisnevichDescentGeneratorMapCanonical) := by
  constructor
  · intro X D
    change canonicalA1NisWeakEquivalences composition
      ((canonicalA1NisGenerators composition).map
        (CanonicalA1NisGenerator.a1Projection X D))
    exact ⟨GeneratedWeakEquivalenceQ.ofGenerator
      (presentation := canonicalA1NisGenerators composition)
      (CanonicalA1NisGenerator.a1Projection X D)⟩
  · intro square
    change canonicalA1NisWeakEquivalences composition
      ((canonicalA1NisGenerators composition).map
        (CanonicalA1NisGenerator.nisnevichDescent square))
    exact ⟨GeneratedWeakEquivalenceQ.ofGenerator
      (presentation := canonicalA1NisGenerators composition)
      (CanonicalA1NisGenerator.nisnevichDescent square)⟩

/-- The primitive canonical `A1` and Nisnevich generators already lie in the
canonical local-equivalence class seen by canonical local objects. -/
theorem canonicalA1NisGenerators_areCanonicalLocalEquivalences
    (composition : Boundary.CanonicalCompositionData (k := k)) :
    (∀ (X : Geometry.SmSchemeOver k)
       (D : FiniteIrreducibleComponentDecomposition (productWithA1 X)),
        canonicalA1NisLocalEquivalences composition
          (F := QtrLinear (category := Boundary.canonicalCategory composition) (productWithA1 X))
          (G := QtrLinear (category := Boundary.canonicalCategory composition) X)
          (show QtrLinear (category := Boundary.canonicalCategory composition) (productWithA1 X) ⟶
              QtrLinear (category := Boundary.canonicalCategory composition) X from
            projectionToBase_QtrMapOfDecomposition
              (Boundary.canonicalCategory composition) X D)) ∧
    (∀ (square : NisnevichDistinguishedSquareDataQ (Boundary.canonicalCategory composition)),
        canonicalA1NisLocalEquivalences composition
          (F := square.descentCompatiblePairObjectLinear)
          (G := QtrLinear (category := Boundary.canonicalCategory composition) square.base)
          square.nisnevichDescentGeneratorMapLinear) := by
  constructor
  · intro X D
    rw [canonicalA1NisLocalEquivalences_iff]
    exact representableA1Projection_isCanonicalA1NisLocalEquivalence composition X D
  · intro square
    rw [canonicalA1NisLocalEquivalences_iff]
    exact canonicalNisnevichDescentGenerator_isCanonicalA1NisLocalEquivalence
      composition square

/-- The primitive canonical `A1` and Nisnevich generators lie in the
Bousfield-generated weak-equivalence class on the canonical route. -/
theorem canonicalA1NisGenerators_areGeneratedWeakEquivalences
    (composition : Boundary.CanonicalCompositionData (k := k)) :
    (∀ (X : Geometry.SmSchemeOver k)
       (D : FiniteIrreducibleComponentDecomposition (productWithA1 X)),
        canonicalA1NisGeneratedWeakEquivalences composition
          (F := QtrLinear (category := Boundary.canonicalCategory composition) (productWithA1 X))
          (G := QtrLinear (category := Boundary.canonicalCategory composition) X)
          (show QtrLinear (category := Boundary.canonicalCategory composition) (productWithA1 X) ⟶
              QtrLinear (category := Boundary.canonicalCategory composition) X from
            projectionToBase_QtrMapOfDecomposition
              (Boundary.canonicalCategory composition) X D)) ∧
    (∀ (square : NisnevichDistinguishedSquareDataQ (Boundary.canonicalCategory composition)),
        canonicalA1NisGeneratedWeakEquivalences composition
          (F := square.descentCompatiblePairObjectLinear)
          (G := QtrLinear (category := Boundary.canonicalCategory composition) square.base)
          square.nisnevichDescentGeneratorMapLinear) := by
  constructor
  · intro X D
    exact (canonicalA1NisGeneratedWeakEquivalences_eq_localEquivalences
      composition
      (show QtrLinear (category := Boundary.canonicalCategory composition) (productWithA1 X) ⟶
          QtrLinear (category := Boundary.canonicalCategory composition) X from
        projectionToBase_QtrMapOfDecomposition
          (Boundary.canonicalCategory composition) X D)).mpr
      ((canonicalA1NisGenerators_areCanonicalLocalEquivalences composition).1 X D)
  · intro square
    exact (canonicalA1NisGeneratedWeakEquivalences_eq_localEquivalences
      composition square.nisnevichDescentGeneratorMapLinear).mpr
      ((canonicalA1NisGenerators_areCanonicalLocalEquivalences composition).2 square)

/-- Alignment: `IsA1NisLocalEquivalence` is exactly
`Localization.LeftBousfield.W` for objects in the essential image of
`LinearA1NisLocalPST.inclusion`.

This is the bridge between our predicate definition and Mathlib's Bousfield
localization API.  It makes `Localization.LeftBousfield.isLocalization`
applicable directly once a sheafification adjunction is provided. -/
theorem isA1NisLocalEquivalence_iff_bousfieldW
    {category : SmCorQ (k := k)}
    {F G : LinearPST category}
    (φ : F ⟶ G) :
    IsA1NisLocalEquivalence φ ↔
      Localization.LeftBousfield.W
        (· ∈ Set.range (LinearA1NisLocalPST.inclusion category).obj) φ := by
  constructor
  · intro hφ Z ⟨L, hL⟩
    rw [← hL]
    exact hφ L
  · intro hφ L
    exact hφ ((LinearA1NisLocalPST.inclusion category).obj L) ⟨L, rfl⟩

end Boundary
