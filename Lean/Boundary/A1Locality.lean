import Boundary.A1ProjectionCorrespondence
import Boundary.NisnevichPullbackTransfer
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
def IsA1Local {category : SmCorQ (k := k)}
    (F : PST category) := by
  letI := SmCorQCat category
  exact ∀ (X : Geometry.SmSchemeOver k)
    (D : FiniteIrreducibleComponentDecomposition (productWithA1 X)),
      CategoryTheory.IsIso (projectionToBase_PSTMapOfDecomposition F X D)

namespace IsA1Local

/-- The `A1`-locality condition for the projection map is independent of the
chosen finite irreducible-component decomposition. -/
theorem decomposition_independent
    {category : SmCorQ (k := k)}
    {F : PST category} {X : Geometry.SmSchemeOver k}
    {D₁ D₂ : FiniteIrreducibleComponentDecomposition (productWithA1 X)}
    (h : CategoryTheory.IsIso (projectionToBase_PSTMapOfDecomposition F X D₁)) :
    CategoryTheory.IsIso (projectionToBase_PSTMapOfDecomposition F X D₂) := by
  rw [← projectionToBase_PSTMap_independent F X D₁ D₂]
  exact h

/-- Every `A1`-local presheaf with transfers inverts the representable
`A1`-projection generator on values. This is exactly the map appearing in the
definition of `IsA1Local`, induced by the same projection correspondence as
`projectionToBase_QtrMapOfDecomposition`. -/
theorem inverts_representableA1Projection
    {category : SmCorQ (k := k)} {F : PST category}
    (hF : IsA1Local F)
    (X : Geometry.SmSchemeOver k)
    (D : FiniteIrreducibleComponentDecomposition (productWithA1 X)) :
    CategoryTheory.IsIso (projectionToBase_PSTMapOfDecomposition F X D) :=
  hF X D

/-- If a presheaf with transfers inverts every representable `A1`-projection
generator on values, then it is `A1`-local. -/
theorem of_inverts_representableA1Projection
    {category : SmCorQ (k := k)} {F : PST category}
    (hF : ∀ (X : Geometry.SmSchemeOver k)
      (D : FiniteIrreducibleComponentDecomposition (productWithA1 X)),
        CategoryTheory.IsIso (projectionToBase_PSTMapOfDecomposition F X D)) :
    IsA1Local F :=
  hF

/-- A presheaf with transfers is `A1`-local exactly when it inverts every
representable `A1`-projection generator on values. -/
theorem isA1Local_iff_inverts_representableA1Projection
    {category : SmCorQ (k := k)} {F : PST category} :
    IsA1Local F ↔
      ∀ (X : Geometry.SmSchemeOver k)
        (D : FiniteIrreducibleComponentDecomposition (productWithA1 X)),
          CategoryTheory.IsIso (projectionToBase_PSTMapOfDecomposition F X D) := by
  constructor
  · exact inverts_representableA1Projection
  · exact of_inverts_representableA1Projection

end IsA1Local

/-- For a bundled linear presheaf with transfers, `A1`-locality is equivalent
to inverting the representable `A1`-projection generator on the current
Yoneda-carried morphism type. -/
theorem IsA1Local_iff_QtrLinear_inverts_A1Projection
    {category : SmCorQ (k := k)}
    (F : LinearPST category) :
    IsA1Local F.toPST ↔
      ∀ (X : Geometry.SmSchemeOver k)
        (D : FiniteIrreducibleComponentDecomposition (productWithA1 X)),
        Function.Bijective
          (fun η : (QtrLinear (category := category) X).toPST ⟶ F.toPST =>
            (projectionToBase_QtrMapOfDecomposition category X D) ≫ η) := by
  letI := SmCorQCat category
  constructor
  · intro hF X D
    let p := projectionToBase_PSTMapOfDecomposition F.toPST X D
    have hpIso : CategoryTheory.IsIso p :=
      (IsA1Local.isA1Local_iff_inverts_representableA1Projection
        (F := F.toPST)).mp hF X D
    let ep : F.toPST.obj (Opposite.op X) ≃ₗ[ℚ] F.toPST.obj (Opposite.op (productWithA1 X)) :=
      (asIso p).toLinearEquiv
    have hpBij : Function.Bijective p := by
      exact ep.bijective
    refine ⟨?_, ?_⟩
    · intro η₁ η₂ hη
      apply (QtrLinear_yoneda F X).injective
      have h₁ := QtrLinear_yoneda_representableA1Projection (F := F) X D η₁
      have h₂ := QtrLinear_yoneda_representableA1Projection (F := F) X D η₂
      apply hpBij.1
      calc
        p (QtrLinear_yoneda F X η₁)
          = QtrLinear_yoneda F (productWithA1 X)
              ((projectionToBase_QtrMapOfDecomposition category X D) ≫ η₁) := by
                symm
                exact h₁
        _ = QtrLinear_yoneda F (productWithA1 X)
              ((projectionToBase_QtrMapOfDecomposition category X D) ≫ η₂) := by
                exact congrArg (QtrLinear_yoneda F (productWithA1 X)) hη
        _ = p (QtrLinear_yoneda F X η₂) := h₂
    · intro θ
      rcases hpBij.2 (QtrLinear_yoneda F (productWithA1 X) θ) with ⟨x, hx⟩
      refine ⟨(QtrLinear_yoneda F X).invFun x, ?_⟩
      apply (QtrLinear_yoneda F (productWithA1 X)).injective
      calc
        QtrLinear_yoneda F (productWithA1 X)
            ((projectionToBase_QtrMapOfDecomposition category X D) ≫
              (QtrLinear_yoneda F X).invFun x)
          = p (QtrLinear_yoneda F X ((QtrLinear_yoneda F X).invFun x)) :=
              QtrLinear_yoneda_representableA1Projection
                (F := F) X D ((QtrLinear_yoneda F X).invFun x)
        _ = p x := by
              exact congrArg p ((QtrLinear_yoneda F X).right_inv x)
        _ = QtrLinear_yoneda F (productWithA1 X) θ := hx
  · intro hF
    rw [IsA1Local.isA1Local_iff_inverts_representableA1Projection]
    intro X D
    let p := projectionToBase_PSTMapOfDecomposition F.toPST X D
    have hpre := hF X D
    have hpBij : Function.Bijective p := by
      refine ⟨?_, ?_⟩
      · intro x₁ x₂ hx
        let η₁ : (QtrLinear (category := category) X).toPST ⟶ F.toPST :=
          (QtrLinear_yoneda F X).invFun x₁
        let η₂ : (QtrLinear (category := category) X).toPST ⟶ F.toPST :=
          (QtrLinear_yoneda F X).invFun x₂
        have hpreEq :
            (projectionToBase_QtrMapOfDecomposition category X D) ≫ η₁ =
              (projectionToBase_QtrMapOfDecomposition category X D) ≫ η₂ := by
          apply (QtrLinear_yoneda F (productWithA1 X)).injective
          calc
            QtrLinear_yoneda F (productWithA1 X)
                ((projectionToBase_QtrMapOfDecomposition category X D) ≫ η₁)
              = p x₁ := by
                  calc
                    QtrLinear_yoneda F (productWithA1 X)
                        ((projectionToBase_QtrMapOfDecomposition category X D) ≫ η₁)
                      = p (QtrLinear_yoneda F X η₁) :=
                          QtrLinear_yoneda_representableA1Projection (F := F) X D η₁
                    _ = p x₁ := by
                          exact congrArg p (by simpa [η₁] using (QtrLinear_yoneda F X).right_inv x₁)
            _ = p x₂ := hx
            _ = QtrLinear_yoneda F (productWithA1 X)
                ((projectionToBase_QtrMapOfDecomposition category X D) ≫ η₂) := by
                  calc
                    p x₂ = p (QtrLinear_yoneda F X η₂) := by
                      exact congrArg p (by simpa [η₂] using ((QtrLinear_yoneda F X).right_inv x₂).symm)
                    _ = QtrLinear_yoneda F (productWithA1 X)
                        ((projectionToBase_QtrMapOfDecomposition category X D) ≫ η₂) :=
                          (QtrLinear_yoneda_representableA1Projection (F := F) X D η₂).symm
        have hη : η₁ = η₂ := hpre.1 hpreEq
        have hx' := congrArg (QtrLinear_yoneda F X) hη
        simpa [η₁, η₂] using hx'
      · intro y
        let θ : (QtrLinear (category := category) (productWithA1 X)).toPST ⟶ F.toPST :=
          (QtrLinear_yoneda F (productWithA1 X)).invFun y
        rcases hpre.2 θ with ⟨η, hη⟩
        refine ⟨QtrLinear_yoneda F X η, ?_⟩
        calc
          p (QtrLinear_yoneda F X η)
            = QtrLinear_yoneda F (productWithA1 X)
                ((projectionToBase_QtrMapOfDecomposition category X D) ≫ η) := by
                  symm
                  exact QtrLinear_yoneda_representableA1Projection (F := F) X D η
          _ = QtrLinear_yoneda F (productWithA1 X) θ := by
                exact congrArg (QtrLinear_yoneda F (productWithA1 X)) hη
          _ = y := (QtrLinear_yoneda F (productWithA1 X)).right_inv y
    exact
      (LinearEquiv.toModuleIso'
        (LinearEquiv.ofBijective p hpBij)).isIso_hom

/-- Bundled `A1`-local presheaves with transfers. -/
abbrev A1LocalPST (category : SmCorQ (k := k)) :=
  { F : PST category // IsA1Local F }

namespace A1LocalPST

/-- Forget the `A1`-locality proof and view a bundled object as a presheaf with
transfers. -/
abbrev toPST {category : SmCorQ (k := k)}
    (F : A1LocalPST category) : PST category :=
  F.1

/-- A bundled `A1`-local presheaf with transfers carries its locality proof. -/
theorem isA1Local {category : SmCorQ (k := k)}
    (F : A1LocalPST category) : IsA1Local F.toPST :=
  F.2

end A1LocalPST

/-- A presheaf with transfers is both `A1`-local and Nisnevich-local. -/
def IsA1NisLocal {category : SmCorQ (k := k)}
  (F : PST category) :=
  IsA1Local F ∧ IsNisnevichLocal F

namespace IsA1NisLocal

/-- A combined `A1`+Nisnevich-local presheaf is `A1`-local. -/
theorem isA1Local {category : SmCorQ (k := k)} {F : PST category}
    (hF : IsA1NisLocal F) : IsA1Local F :=
  hF.1

/-- A combined `A1`+Nisnevich-local presheaf is Nisnevich-local. -/
theorem isNisnevichLocal {category : SmCorQ (k := k)} {F : PST category}
    (hF : IsA1NisLocal F) : IsNisnevichLocal F :=
  hF.2

/-- If a presheaf with transfers is both `A1`-local and Nisnevich-local, then
it is combined `A1`+Nisnevich-local. -/
theorem of_localities {category : SmCorQ (k := k)} {F : PST category}
    (hA1 : IsA1Local F) (hNis : IsNisnevichLocal F) : IsA1NisLocal F :=
  ⟨hA1, hNis⟩

/-- A presheaf with transfers is combined `A1`+Nisnevich-local exactly when it
is both `A1`-local and Nisnevich-local. -/
theorem iff_localities {category : SmCorQ (k := k)} {F : PST category} :
    IsA1NisLocal F ↔ IsA1Local F ∧ IsNisnevichLocal F :=
  Iff.rfl

end IsA1NisLocal

/-- For a bundled linear presheaf with transfers, combined `A1` and Nisnevich
locality is equivalent to the conjunction of the two Yoneda-form local
conditions already established separately. -/
theorem IsA1NisLocal_iff_QtrLinear_local
    {category : SmCorQ (k := k)}
    (F : LinearPST category) :
    IsA1NisLocal F.toPST ↔
      (∀ (X : Geometry.SmSchemeOver k)
        (D : FiniteIrreducibleComponentDecomposition (productWithA1 X)),
        Function.Bijective
          (fun η : (QtrLinear (category := category) X).toPST ⟶ F.toPST =>
            (projectionToBase_QtrMapOfDecomposition category X D) ≫ η)) ∧
      (∀ square : NisnevichDistinguishedSquareDataQ category,
        ∀ (ηopen : (QtrLinear (category := category) square.openPiece).toPST ⟶ F.toPST)
          (ηpatch : (QtrLinear (category := category) square.patchPiece).toPST ⟶ F.toPST),
          (QtrMap (category := category) square.overlapToOpenTransfer) ≫ ηopen =
            (QtrMap (category := category) square.overlapToPatchTransfer) ≫ ηpatch →
          ∃! ηbase : (QtrLinear (category := category) square.base).toPST ⟶ F.toPST,
            (QtrMap (category := category) square.openToBaseTransfer) ≫ ηbase = ηopen ∧
              (QtrMap (category := category) square.patchToBaseTransfer) ≫ ηbase = ηpatch) := by
  rw [IsA1NisLocal.iff_localities,
    IsA1Local_iff_QtrLinear_inverts_A1Projection,
    IsNisnevichLocal_iff_QtrLinear_satisfies_descent]

/-- Canonical-route Nisnevich locality for presheaves with transfers on
`canonicalSmCorQ`. This is just the existing squarewise descent condition,
specialized to the canonical rational correspondence category attached to the
chosen composition package. -/
def IsCanonicalNisnevichLocal
    (composition : Boundary.CanonicalCompositionData (k := k))
  (F : PST (Boundary.canonicalCategory composition)) :=
  IsNisnevichLocal F

/-- On the canonical route, Nisnevich locality is exactly the usual unique
gluing condition for canonical distinguished-square descent generators. -/
theorem IsCanonicalNisnevichLocal_iff_QtrLinear_satisfies_descent
    (composition : Boundary.CanonicalCompositionData (k := k))
    (F : LinearPST (Boundary.canonicalCategory composition)) :
    IsCanonicalNisnevichLocal composition F.toPST ↔
      ∀ square : NisnevichDistinguishedSquareDataQ (Boundary.canonicalCategory composition),
        ∀ (ηopen : (QtrLinear (category := Boundary.canonicalCategory composition)
            square.openPiece).toPST ⟶ F.toPST)
          (ηpatch : (QtrLinear (category := Boundary.canonicalCategory composition)
            square.patchPiece).toPST ⟶ F.toPST),
          (QtrMap (category := Boundary.canonicalCategory composition)
              square.overlapToOpenTransfer) ≫ ηopen =
            (QtrMap (category := Boundary.canonicalCategory composition)
              square.overlapToPatchTransfer) ≫ ηpatch →
          ∃! ηbase : (QtrLinear (category := Boundary.canonicalCategory composition)
              square.base).toPST ⟶ F.toPST,
            (QtrMap (category := Boundary.canonicalCategory composition)
                square.openToBaseTransfer) ≫ ηbase = ηopen ∧
              (QtrMap (category := Boundary.canonicalCategory composition)
                square.patchToBaseTransfer) ≫ ηbase = ηpatch :=
  IsNisnevichLocal_iff_QtrLinear_satisfies_descent F

/-- Canonical-route `A1`-locality for presheaves with transfers on
`canonicalSmCorQ`. This is the existing `A1`-locality predicate specialized to
the canonical rational correspondence category determined by `composition`. -/
def IsCanonicalA1Local
    (composition : Boundary.CanonicalCompositionData (k := k))
  (F : PST (Boundary.canonicalCategory composition)) :=
  IsA1Local F

/-- Canonical-route combined `A1`+Nisnevich locality on `canonicalSmCorQ`. -/
def IsCanonicalA1NisLocal
    (composition : Boundary.CanonicalCompositionData (k := k))
  (F : PST (Boundary.canonicalCategory composition)) :=
  IsCanonicalA1Local composition F ∧ IsCanonicalNisnevichLocal composition F

namespace IsCanonicalA1NisLocal

/-- A canonical `A1`+Nisnevich-local presheaf is canonically `A1`-local. -/
theorem isA1Local
    {composition : Boundary.CanonicalCompositionData (k := k)}
    {F : PST (Boundary.canonicalCategory composition)}
    (hF : IsCanonicalA1NisLocal composition F) :
    IsCanonicalA1Local composition F :=
  hF.1

/-- A canonical `A1`+Nisnevich-local presheaf is canonically Nisnevich-local. -/
theorem isNisnevichLocal
    {composition : Boundary.CanonicalCompositionData (k := k)}
    {F : PST (Boundary.canonicalCategory composition)}
    (hF : IsCanonicalA1NisLocal composition F) :
    IsCanonicalNisnevichLocal composition F :=
  hF.2

/-- Canonical combined locality is exactly the conjunction of the canonical
`A1`- and Nisnevich-locality predicates. -/
theorem iff_localities
    {composition : Boundary.CanonicalCompositionData (k := k)}
    {F : PST (Boundary.canonicalCategory composition)} :
    IsCanonicalA1NisLocal composition F ↔
      IsCanonicalA1Local composition F ∧
        IsCanonicalNisnevichLocal composition F :=
  Iff.rfl

end IsCanonicalA1NisLocal

/-- On the canonical route, combined `A1`+Nisnevich locality is equivalent to
the conjunction of the canonical `A1`-projection and distinguished-square
descent conditions on the honest `QtrLinear` surface. -/
theorem IsCanonicalA1NisLocal_iff_QtrLinear_local
    (composition : Boundary.CanonicalCompositionData (k := k))
    (F : LinearPST (Boundary.canonicalCategory composition)) :
    IsCanonicalA1NisLocal composition F.toPST ↔
      (∀ (X : Geometry.SmSchemeOver k)
        (D : FiniteIrreducibleComponentDecomposition (productWithA1 X)),
        Function.Bijective
          (fun η : (QtrLinear (category := Boundary.canonicalCategory composition) X).toPST ⟶
              F.toPST =>
            (projectionToBase_QtrMapOfDecomposition
              (Boundary.canonicalCategory composition) X D) ≫ η)) ∧
      (∀ square : NisnevichDistinguishedSquareDataQ (Boundary.canonicalCategory composition),
        ∀ (ηopen : (QtrLinear (category := Boundary.canonicalCategory composition)
            square.openPiece).toPST ⟶ F.toPST)
          (ηpatch : (QtrLinear (category := Boundary.canonicalCategory composition)
            square.patchPiece).toPST ⟶ F.toPST),
          (QtrMap (category := Boundary.canonicalCategory composition)
              square.overlapToOpenTransfer) ≫ ηopen =
            (QtrMap (category := Boundary.canonicalCategory composition)
              square.overlapToPatchTransfer) ≫ ηpatch →
          ∃! ηbase : (QtrLinear (category := Boundary.canonicalCategory composition)
              square.base).toPST ⟶ F.toPST,
            (QtrMap (category := Boundary.canonicalCategory composition)
                square.openToBaseTransfer) ≫ ηbase = ηopen ∧
              (QtrMap (category := Boundary.canonicalCategory composition)
                square.patchToBaseTransfer) ≫ ηbase = ηpatch) := by
  change IsA1NisLocal F.toPST ↔
      (∀ (X : Geometry.SmSchemeOver k)
        (D : FiniteIrreducibleComponentDecomposition (productWithA1 X)),
        Function.Bijective
          (fun η : (QtrLinear (category := Boundary.canonicalCategory composition) X).toPST ⟶
              F.toPST =>
            (projectionToBase_QtrMapOfDecomposition
              (Boundary.canonicalCategory composition) X D) ≫ η)) ∧
      (∀ square : NisnevichDistinguishedSquareDataQ (Boundary.canonicalCategory composition),
        ∀ (ηopen : (QtrLinear (category := Boundary.canonicalCategory composition)
            square.openPiece).toPST ⟶ F.toPST)
          (ηpatch : (QtrLinear (category := Boundary.canonicalCategory composition)
            square.patchPiece).toPST ⟶ F.toPST),
          (QtrMap (category := Boundary.canonicalCategory composition)
              square.overlapToOpenTransfer) ≫ ηopen =
            (QtrMap (category := Boundary.canonicalCategory composition)
              square.overlapToPatchTransfer) ≫ ηpatch →
          ∃! ηbase : (QtrLinear (category := Boundary.canonicalCategory composition)
              square.base).toPST ⟶ F.toPST,
            (QtrMap (category := Boundary.canonicalCategory composition)
                square.openToBaseTransfer) ≫ ηbase = ηopen ∧
              (QtrMap (category := Boundary.canonicalCategory composition)
                square.patchToBaseTransfer) ≫ ηbase = ηpatch)
  exact IsA1NisLocal_iff_QtrLinear_local F

/-- A bundled linear presheaf with transfers is `A1`+Nisnevich-local when its
underlying presheaf with transfers is both `A1`-local and Nisnevich-local. -/
def IsLinearA1NisLocal {category : SmCorQ (k := k)}
  (F : LinearPST category) :=
  IsA1NisLocal F.toPST

/-- Bundled `A1`+Nisnevich-local presheaves with transfers inside the honest
`LinearPST` surface. -/
abbrev LinearA1NisLocalPST (category : SmCorQ (k := k)) :=
  { F : LinearPST category // IsLinearA1NisLocal F }

namespace LinearA1NisLocalPST

/-- Forget the locality proof and view a bundled object as a linear presheaf
with transfers. -/
abbrev toLinearPST {category : SmCorQ (k := k)}
    (F : LinearA1NisLocalPST category) : LinearPST category :=
  F.1

instance {category : SmCorQ (k := k)} : Category (LinearA1NisLocalPST category) := by
  exact InducedCategory.category LinearA1NisLocalPST.toLinearPST

/-- Forget the linearity and locality proofs and view a bundled object as an
ordinary presheaf with transfers. -/
abbrev toPST {category : SmCorQ (k := k)}
    (F : LinearA1NisLocalPST category) : PST category :=
  F.toLinearPST.toPST

/-- A bundled linear `A1`+Nisnevich-local presheaf carries its combined
locality proof. -/
theorem isA1NisLocal {category : SmCorQ (k := k)}
    (F : LinearA1NisLocalPST category) : IsA1NisLocal F.toPST :=
  F.2

/-- A bundled linear `A1`+Nisnevich-local presheaf is `A1`-local. -/
theorem isA1Local {category : SmCorQ (k := k)}
    (F : LinearA1NisLocalPST category) : IsA1Local F.toPST :=
  F.2.1

/-- A bundled linear `A1`+Nisnevich-local presheaf is Nisnevich-local. -/
theorem isNisnevichLocal {category : SmCorQ (k := k)}
    (F : LinearA1NisLocalPST category) : IsNisnevichLocal F.toPST :=
  F.2.2

/-- The inclusion of `A1`+Nisnevich-local linear presheaves with transfers into
all linear presheaves with transfers.

This is a fully faithful embedding; its left adjoint (A¹/Nis sheafification)
is the Step 2 mathematical blocker. -/
def inclusion (category : SmCorQ (k := k)) :
    LinearA1NisLocalPST category ⥤ LinearPST category :=
  inducedFunctor LinearA1NisLocalPST.toLinearPST

@[simp] theorem inclusion_obj {category : SmCorQ (k := k)}
    (F : LinearA1NisLocalPST category) :
    (inclusion category).obj F = F.toLinearPST :=
  rfl

@[simp] theorem inclusion_map {category : SmCorQ (k := k)}
    {F G : LinearA1NisLocalPST category} (f : F ⟶ G) :
    (inclusion category).map f = f :=
  rfl

instance inclusion_full {category : SmCorQ (k := k)} :
    (inclusion category).Full := by
  change (inducedFunctor LinearA1NisLocalPST.toLinearPST).Full
  infer_instance

instance inclusion_faithful {category : SmCorQ (k := k)} :
    (inclusion category).Faithful := by
  change (inducedFunctor LinearA1NisLocalPST.toLinearPST).Faithful
  infer_instance

/-- The bundled local subcategory inherits the pointwise preadditive structure
from `LinearPST`. -/
instance preadditive {category : SmCorQ (k := k)}
    [Preadditive (LinearPST category)] :
    Preadditive (LinearA1NisLocalPST category) := by
  change Preadditive (InducedCategory (LinearPST category)
    LinearA1NisLocalPST.toLinearPST)
  infer_instance

/-- A1/Nis local linear presheaves are closed under ambient pullbacks.

The proof uses the Yoneda-style locality criterion: morphisms from a
representable into a pullback are compatible pairs of morphisms into the two
legs. A1 invertibility and Nisnevich descent are therefore inherited
componentwise from the three objects in the cospan. -/
theorem isLinearA1NisLocal_pullback
    {category : SmCorQ (k := k)}
    {F G H : LinearPST category} {f : F ⟶ H} {g : G ⟶ H}
    [CategoryTheory.Limits.HasPullback f g]
    (hF : IsLinearA1NisLocal F)
    (hG : IsLinearA1NisLocal G)
    (hH : IsLinearA1NisLocal H) :
    IsLinearA1NisLocal (CategoryTheory.Limits.pullback f g) := by
  classical
  letI := SmCorQCat category
  unfold IsLinearA1NisLocal
  rw [IsA1NisLocal_iff_QtrLinear_local]
  constructor
  · intro X D
    let p := projectionToBase_QtrMapOfDecomposition category X D
    let pLin : QtrLinear (category := category) (productWithA1 X) ⟶
        QtrLinear (category := category) X := p
    change Function.Bijective
      (fun η : QtrLinear (category := category) X ⟶
          CategoryTheory.Limits.pullback f g => pLin ≫ η)
    have hF' := (IsA1NisLocal_iff_QtrLinear_local F).mp hF
    have hG' := (IsA1NisLocal_iff_QtrLinear_local G).mp hG
    have hH' := (IsA1NisLocal_iff_QtrLinear_local H).mp hH
    have hFbij : Function.Bijective
        (fun η : QtrLinear (category := category) X ⟶ F => pLin ≫ η) := by
      simpa [pLin, p] using hF'.1 X D
    have hGbij : Function.Bijective
        (fun η : QtrLinear (category := category) X ⟶ G => pLin ≫ η) := by
      simpa [pLin, p] using hG'.1 X D
    have hHbij : Function.Bijective
        (fun η : QtrLinear (category := category) X ⟶ H => pLin ≫ η) := by
      simpa [pLin, p] using hH'.1 X D
    constructor
    · intro η₁ η₂ hη
      apply CategoryTheory.Limits.pullback.hom_ext
      · apply hFbij.1
        have h := congrArg
          (fun q => q ≫ CategoryTheory.Limits.pullback.fst f g) hη
        simpa [pLin, p, Category.assoc] using h
      · apply hGbij.1
        have h := congrArg
          (fun q => q ≫ CategoryTheory.Limits.pullback.snd f g) hη
        simpa [pLin, p, Category.assoc] using h
    · intro θ
      rcases hFbij.2
        (θ ≫ CategoryTheory.Limits.pullback.fst f g) with ⟨ηF, hηF⟩
      rcases hGbij.2
        (θ ≫ CategoryTheory.Limits.pullback.snd f g) with ⟨ηG, hηG⟩
      have hcompat : ηF ≫ f = ηG ≫ g := by
        apply hHbij.1
        calc
          pLin ≫ (ηF ≫ f)
              = θ ≫ CategoryTheory.Limits.pullback.fst f g ≫ f := by
                simpa [pLin, p, Category.assoc] using congrArg (fun q => q ≫ f) hηF
          _ = θ ≫ CategoryTheory.Limits.pullback.snd f g ≫ g := by
                calc
                  (θ ≫ CategoryTheory.Limits.pullback.fst f g) ≫ f
                      = θ ≫ (CategoryTheory.Limits.pullback.fst f g ≫ f) := by
                        rw [Category.assoc]
                  _ = θ ≫ (CategoryTheory.Limits.pullback.snd f g ≫ g) := by
                        rw [CategoryTheory.Limits.pullback.condition]
                  _ = (θ ≫ CategoryTheory.Limits.pullback.snd f g) ≫ g := by
                        rw [Category.assoc]
          _ = pLin ≫ (ηG ≫ g) := by
                simpa [pLin, p, Category.assoc] using
                  (congrArg (fun q => q ≫ g) hηG).symm
      refine
        ⟨CategoryTheory.Limits.pullback.lift ηF ηG hcompat, ?_⟩
      apply CategoryTheory.Limits.pullback.hom_ext
      · simpa [pLin, p, Category.assoc] using hηF
      · simpa [pLin, p, Category.assoc] using hηG
  · intro square
    let oLin : QtrLinear (category := category) square.overlap ⟶
        QtrLinear (category := category) square.openPiece :=
      QtrMap (category := category) square.overlapToOpenTransfer
    let qLin : QtrLinear (category := category) square.overlap ⟶
        QtrLinear (category := category) square.patchPiece :=
      QtrMap (category := category) square.overlapToPatchTransfer
    let uLin : QtrLinear (category := category) square.openPiece ⟶
        QtrLinear (category := category) square.base :=
      QtrMap (category := category) square.openToBaseTransfer
    let vLin : QtrLinear (category := category) square.patchPiece ⟶
        QtrLinear (category := category) square.base :=
      QtrMap (category := category) square.patchToBaseTransfer
    change ∀
      (ηopen : QtrLinear (category := category) square.openPiece ⟶
        CategoryTheory.Limits.pullback f g)
      (ηpatch : QtrLinear (category := category) square.patchPiece ⟶
        CategoryTheory.Limits.pullback f g),
        oLin ≫ ηopen = qLin ≫ ηpatch →
        ∃! ηbase : QtrLinear (category := category) square.base ⟶
          CategoryTheory.Limits.pullback f g,
          uLin ≫ ηbase = ηopen ∧ vLin ≫ ηbase = ηpatch
    intro ηopen ηpatch hoverlap
    have hF' := (IsA1NisLocal_iff_QtrLinear_local F).mp hF
    have hG' := (IsA1NisLocal_iff_QtrLinear_local G).mp hG
    have hH' := (IsA1NisLocal_iff_QtrLinear_local H).mp hH
    have hFdescent :
        ∀ (ηopen : QtrLinear (category := category) square.openPiece ⟶ F)
          (ηpatch : QtrLinear (category := category) square.patchPiece ⟶ F),
          oLin ≫ ηopen = qLin ≫ ηpatch →
          ∃! ηbase : QtrLinear (category := category) square.base ⟶ F,
            uLin ≫ ηbase = ηopen ∧ vLin ≫ ηbase = ηpatch := by
      simpa [oLin, qLin, uLin, vLin] using hF'.2 square
    have hGdescent :
        ∀ (ηopen : QtrLinear (category := category) square.openPiece ⟶ G)
          (ηpatch : QtrLinear (category := category) square.patchPiece ⟶ G),
          oLin ≫ ηopen = qLin ≫ ηpatch →
          ∃! ηbase : QtrLinear (category := category) square.base ⟶ G,
            uLin ≫ ηbase = ηopen ∧ vLin ≫ ηbase = ηpatch := by
      simpa [oLin, qLin, uLin, vLin] using hG'.2 square
    have hHdescent :
        ∀ (ηopen : QtrLinear (category := category) square.openPiece ⟶ H)
          (ηpatch : QtrLinear (category := category) square.patchPiece ⟶ H),
          oLin ≫ ηopen = qLin ≫ ηpatch →
          ∃! ηbase : QtrLinear (category := category) square.base ⟶ H,
            uLin ≫ ηbase = ηopen ∧ vLin ≫ ηbase = ηpatch := by
      simpa [oLin, qLin, uLin, vLin] using hH'.2 square
    have hoverlapF :
        oLin ≫ (ηopen ≫ CategoryTheory.Limits.pullback.fst f g) =
          qLin ≫ (ηpatch ≫ CategoryTheory.Limits.pullback.fst f g) := by
      simpa [oLin, qLin, Category.assoc] using
        congrArg (fun z => z ≫ CategoryTheory.Limits.pullback.fst f g) hoverlap
    have hoverlapG :
        oLin ≫ (ηopen ≫ CategoryTheory.Limits.pullback.snd f g) =
          qLin ≫ (ηpatch ≫ CategoryTheory.Limits.pullback.snd f g) := by
      simpa [oLin, qLin, Category.assoc] using
        congrArg (fun z => z ≫ CategoryTheory.Limits.pullback.snd f g) hoverlap
    rcases hFdescent
      (ηopen ≫ CategoryTheory.Limits.pullback.fst f g)
      (ηpatch ≫ CategoryTheory.Limits.pullback.fst f g)
      hoverlapF with ⟨ηF, hηF, huniqF⟩
    rcases hGdescent
      (ηopen ≫ CategoryTheory.Limits.pullback.snd f g)
      (ηpatch ≫ CategoryTheory.Limits.pullback.snd f g)
      hoverlapG with ⟨ηG, hηG, huniqG⟩
    have hcompat : ηF ≫ f = ηG ≫ g := by
      have hoverlapH :
          oLin ≫ (ηopen ≫ CategoryTheory.Limits.pullback.fst f g ≫ f) =
            qLin ≫ (ηpatch ≫ CategoryTheory.Limits.pullback.fst f g ≫ f) := by
        calc
          oLin ≫ (ηopen ≫ CategoryTheory.Limits.pullback.fst f g ≫ f)
              = (oLin ≫ ηopen) ≫ CategoryTheory.Limits.pullback.fst f g ≫ f := by
                simp [Category.assoc]
          _ = (qLin ≫ ηpatch) ≫ CategoryTheory.Limits.pullback.fst f g ≫ f := by
                rw [hoverlap]
          _ = qLin ≫ (ηpatch ≫ CategoryTheory.Limits.pullback.fst f g ≫ f) := by
                simp [Category.assoc]
      rcases hHdescent
        (ηopen ≫ CategoryTheory.Limits.pullback.fst f g ≫ f)
        (ηpatch ≫ CategoryTheory.Limits.pullback.fst f g ≫ f)
        hoverlapH with ⟨ηH, _hηH, huniqH⟩
      have hFsol :
          uLin ≫ (ηF ≫ f) =
              ηopen ≫ CategoryTheory.Limits.pullback.fst f g ≫ f ∧
            vLin ≫ (ηF ≫ f) =
              ηpatch ≫ CategoryTheory.Limits.pullback.fst f g ≫ f := by
        constructor
        · calc
            uLin ≫ (ηF ≫ f)
                = (uLin ≫ ηF) ≫ f := by simp [Category.assoc]
            _ = ηopen ≫ CategoryTheory.Limits.pullback.fst f g ≫ f := by
                  simpa [Category.assoc] using congrArg (fun z => z ≫ f) hηF.1
        · calc
            vLin ≫ (ηF ≫ f)
                = (vLin ≫ ηF) ≫ f := by simp [Category.assoc]
            _ = ηpatch ≫ CategoryTheory.Limits.pullback.fst f g ≫ f := by
                  simpa [Category.assoc] using congrArg (fun z => z ≫ f) hηF.2
      have hGsol :
          uLin ≫ (ηG ≫ g) =
              ηopen ≫ CategoryTheory.Limits.pullback.fst f g ≫ f ∧
            vLin ≫ (ηG ≫ g) =
              ηpatch ≫ CategoryTheory.Limits.pullback.fst f g ≫ f := by
        constructor
        · calc
            uLin ≫ (ηG ≫ g)
                = (uLin ≫ ηG) ≫ g := by simp [Category.assoc]
            _ = ηopen ≫ CategoryTheory.Limits.pullback.snd f g ≫ g := by
                  simpa [Category.assoc] using congrArg (fun z => z ≫ g) hηG.1
            _ = ηopen ≫ CategoryTheory.Limits.pullback.fst f g ≫ f := by
                  rw [← Category.assoc,
                    CategoryTheory.Limits.pullback.condition, Category.assoc]
        · calc
            vLin ≫ (ηG ≫ g)
                = (vLin ≫ ηG) ≫ g := by simp [Category.assoc]
            _ = ηpatch ≫ CategoryTheory.Limits.pullback.snd f g ≫ g := by
                  simpa [Category.assoc] using congrArg (fun z => z ≫ g) hηG.2
            _ = ηpatch ≫ CategoryTheory.Limits.pullback.fst f g ≫ f := by
                  rw [← Category.assoc,
                    CategoryTheory.Limits.pullback.condition, Category.assoc]
      calc
        ηF ≫ f = ηH := huniqH (ηF ≫ f) hFsol
        _ = ηG ≫ g := (huniqH (ηG ≫ g) hGsol).symm
    refine ⟨CategoryTheory.Limits.pullback.lift ηF ηG hcompat, ?_, ?_⟩
    · constructor
      · apply CategoryTheory.Limits.pullback.hom_ext
        · simpa [uLin, Category.assoc] using hηF.1
        · simpa [uLin, Category.assoc] using hηG.1
      · apply CategoryTheory.Limits.pullback.hom_ext
        · simpa [vLin, Category.assoc] using hηF.2
        · simpa [vLin, Category.assoc] using hηG.2
    · intro η hη
      apply CategoryTheory.Limits.pullback.hom_ext
      · calc
          η ≫ CategoryTheory.Limits.pullback.fst f g = ηF :=
            huniqF
              (η ≫ CategoryTheory.Limits.pullback.fst f g)
              (by
                constructor
                · simpa [uLin, Category.assoc] using
                    congrArg (fun z => z ≫ CategoryTheory.Limits.pullback.fst f g) hη.1
                · simpa [vLin, Category.assoc] using
                    congrArg (fun z => z ≫ CategoryTheory.Limits.pullback.fst f g) hη.2)
          _ = CategoryTheory.Limits.pullback.lift ηF ηG hcompat ≫
              CategoryTheory.Limits.pullback.fst f g := by
                symm
                exact CategoryTheory.Limits.pullback.lift_fst ηF ηG hcompat
      · calc
          η ≫ CategoryTheory.Limits.pullback.snd f g = ηG :=
            huniqG
              (η ≫ CategoryTheory.Limits.pullback.snd f g)
              (by
                constructor
                · simpa [uLin, Category.assoc] using
                    congrArg (fun z => z ≫ CategoryTheory.Limits.pullback.snd f g) hη.1
                · simpa [vLin, Category.assoc] using
                    congrArg (fun z => z ≫ CategoryTheory.Limits.pullback.snd f g) hη.2)
          _ = CategoryTheory.Limits.pullback.lift ηF ηG hcompat ≫
              CategoryTheory.Limits.pullback.snd f g := by
                symm
                exact CategoryTheory.Limits.pullback.lift_snd ηF ηG hcompat

/-- The bundled category of A1/Nis-local linear presheaves has pullbacks,
constructed as ambient pullbacks in `LinearPST` with locality supplied by
`isLinearA1NisLocal_pullback`. -/
noncomputable instance hasPullback
    {category : SmCorQ (k := k)}
    [CategoryTheory.Limits.HasPullbacks (LinearPST category)]
    {X Y Z : LinearA1NisLocalPST category}
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    CategoryTheory.Limits.HasPullback f g := by
  let f' : X.toLinearPST ⟶ Z.toLinearPST :=
    (inclusion category).map f
  let g' : Y.toLinearPST ⟶ Z.toLinearPST :=
    (inclusion category).map g
  let P₀ : LinearPST category := CategoryTheory.Limits.pullback f' g'
  have hP₀ : IsLinearA1NisLocal P₀ :=
    isLinearA1NisLocal_pullback
      (F := X.toLinearPST) (G := Y.toLinearPST) (H := Z.toLinearPST)
      (f := f') (g := g') X.2 Y.2 Z.2
  let P : LinearA1NisLocalPST category := ⟨P₀, hP₀⟩
  refine ⟨⟨CategoryTheory.Limits.PullbackCone.mk
    (show P ⟶ X from CategoryTheory.Limits.pullback.fst f' g')
    (show P ⟶ Y from CategoryTheory.Limits.pullback.snd f' g')
    ?_, ?_⟩⟩
  · change
      CategoryTheory.Limits.pullback.fst f' g' ≫ f' =
        CategoryTheory.Limits.pullback.snd f' g' ≫ g'
    exact CategoryTheory.Limits.pullback.condition
  · refine CategoryTheory.Limits.PullbackCone.IsLimit.mk _ ?lift ?fac_fst ?fac_snd ?uniq
    · intro s
      refine CategoryTheory.Limits.pullback.lift
        ((inclusion category).map s.fst)
        ((inclusion category).map s.snd) ?_
      change
        (inclusion category).map s.fst ≫ f' =
          (inclusion category).map s.snd ≫ g'
      simpa [f', g'] using congrArg ((inclusion category).map) s.condition
    · intro s
      change
        CategoryTheory.Limits.pullback.lift
            ((inclusion category).map s.fst)
            ((inclusion category).map s.snd) _ ≫
          CategoryTheory.Limits.pullback.fst f' g' =
            (inclusion category).map s.fst
      simp
    · intro s
      change
        CategoryTheory.Limits.pullback.lift
            ((inclusion category).map s.fst)
            ((inclusion category).map s.snd) _ ≫
          CategoryTheory.Limits.pullback.snd f' g' =
            (inclusion category).map s.snd
      simp
    · intro s m hfst hsnd
      change
        (inclusion category).map m =
          CategoryTheory.Limits.pullback.lift
            ((inclusion category).map s.fst)
            ((inclusion category).map s.snd) _
      apply CategoryTheory.Limits.pullback.hom_ext
      · calc
          (inclusion category).map m ≫ CategoryTheory.Limits.pullback.fst f' g' =
              (inclusion category).map s.fst := by
                exact congrArg ((inclusion category).map) hfst
          _ = CategoryTheory.Limits.pullback.lift
                ((inclusion category).map s.fst)
                ((inclusion category).map s.snd) _ ≫
              CategoryTheory.Limits.pullback.fst f' g' := by
                symm
                exact CategoryTheory.Limits.pullback.lift_fst
                  ((inclusion category).map s.fst)
                  ((inclusion category).map s.snd) _
      · calc
          (inclusion category).map m ≫ CategoryTheory.Limits.pullback.snd f' g' =
              (inclusion category).map s.snd := by
                exact congrArg ((inclusion category).map) hsnd
          _ = CategoryTheory.Limits.pullback.lift
                ((inclusion category).map s.fst)
                ((inclusion category).map s.snd) _ ≫
              CategoryTheory.Limits.pullback.snd f' g' := by
                symm
                exact CategoryTheory.Limits.pullback.lift_snd
                  ((inclusion category).map s.fst)
                  ((inclusion category).map s.snd) _

/-- A1/Nis-local linear presheaves have all pullbacks. -/
noncomputable instance hasPullbacks
    {category : SmCorQ (k := k)}
    [CategoryTheory.Limits.HasPullbacks (LinearPST category)] :
    CategoryTheory.Limits.HasPullbacks (LinearA1NisLocalPST category) := by
  apply CategoryTheory.Limits.hasPullbacks_of_hasLimit_cospan

/-- The ambient pullback of a cospan of local objects is again local. -/
theorem pullback_obj_isLocal
    {category : SmCorQ (k := k)}
    [CategoryTheory.Limits.HasPullbacks (LinearPST category)]
    {X Y Z : LinearA1NisLocalPST category}
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsLinearA1NisLocal
      (CategoryTheory.Limits.pullback
        ((inclusion category).map f)
        ((inclusion category).map g)) := by
  exact
    isLinearA1NisLocal_pullback
      (F := X.toLinearPST) (G := Y.toLinearPST) (H := Z.toLinearPST)
      (f := (inclusion category).map f)
      (g := (inclusion category).map g)
      X.2 Y.2 Z.2

/-- The local pullback constructed by `LinearA1NisLocalPST.hasPullback` is the
ambient pullback equipped with its induced locality proof. -/
noncomputable def pullback_isLimit_of_ambient
    {category : SmCorQ (k := k)}
    [CategoryTheory.Limits.HasPullbacks (LinearPST category)]
    {X Y Z : LinearA1NisLocalPST category}
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    CategoryTheory.Limits.IsLimit
      (CategoryTheory.Limits.PullbackCone.mk
        (CategoryTheory.Limits.pullback.fst f g)
        (CategoryTheory.Limits.pullback.snd f g)
        (CategoryTheory.Limits.pullback.condition)) := by
  exact CategoryTheory.Limits.pullbackIsPullback f g

end LinearA1NisLocalPST

/-- A morphism of linear presheaves into the actual zero presheaf is unique. -/
theorem LinearPST.hom_to_zero_subsingleton
    {category : SmCorQ (k := k)}
    (F : LinearPST category) :
    Subsingleton (F.toPST ⟶ (LinearPST.zero (category := category)).toPST) := by
  letI := SmCorQCat category
  constructor
  intro η₁ η₂
  apply NatTrans.ext
  apply _root_.funext
  intro X
  apply LinearMap.ext
  intro x
  cases η₁.app X x
  cases η₂.app X x
  rfl

/-- Maps from representable transfer presheaves into the actual zero presheaf
are unique. -/
theorem Qtr_hom_to_linearPST_zero_subsingleton
    {category : SmCorQ (k := k)}
    (X : Geometry.SmSchemeOver k) :
    Subsingleton (Qtr (category := category) X ⟶
      (LinearPST.zero (category := category)).toPST) := by
  change Subsingleton
    ((QtrLinear (category := category) X).toPST ⟶
      (LinearPST.zero (category := category)).toPST)
  exact LinearPST.hom_to_zero_subsingleton
    (QtrLinear (category := category) X)

theorem isLinearA1NisLocal_zero
    {category : SmCorQ (k := k)} :
    IsLinearA1NisLocal (LinearPST.zero (category := category)) := by
  change IsA1NisLocal (LinearPST.zero (category := category)).toPST
  refine (IsA1NisLocal_iff_QtrLinear_local _).2 ?_
  constructor
  · intro X D
    constructor
    · intro η₁ η₂
      intro _hη
      exact (LinearPST.hom_to_zero_subsingleton
        (QtrLinear (category := category) X)).elim η₁ η₂
    · intro η
      refine ⟨0, ?_⟩
      exact (LinearPST.hom_to_zero_subsingleton
        (QtrLinear (category := category) (productWithA1 X))).elim _ _
  · intro square ηopen ηpatch hoverlap
    refine ⟨0, ?_, ?_⟩
    · constructor
      · exact (LinearPST.hom_to_zero_subsingleton
          (QtrLinear (category := category) square.openPiece)).elim _ _
      · exact (LinearPST.hom_to_zero_subsingleton
          (QtrLinear (category := category) square.patchPiece)).elim _ _
    · intro η hη
      exact (LinearPST.hom_to_zero_subsingleton
        (QtrLinear (category := category) square.base)).elim η 0

/-- The bundled local category has a zero object, obtained by equipping the
ambient zero object with its locality proof. -/
noncomputable instance linearA1NisLocalPST_hasZeroObject
    {category : SmCorQ (k := k)} :
    CategoryTheory.Limits.HasZeroObject (LinearA1NisLocalPST category) := by
  letI := SmCorQCat category
  letI : Preadditive (LinearA1NisLocalPST category) :=
    LinearA1NisLocalPST.preadditive (category := category)
  let Z : LinearA1NisLocalPST category :=
    ⟨LinearPST.zero (category := category), isLinearA1NisLocal_zero⟩
  refine (show CategoryTheory.Limits.IsZero Z from ?_).hasZeroObject
  refine ⟨?_, ?_⟩
  · intro Y
    exact
      ⟨{ default := 0,
          uniq := fun f => by
            apply NatTrans.ext
            apply _root_.funext
            intro X
            apply LinearMap.ext
            intro x
            cases x
            change (f.app X) 0 = 0
            exact (f.app X).map_zero }⟩
  · intro Y
    exact
      ⟨{ default := 0,
          uniq := fun f => by
            apply NatTrans.ext
            apply _root_.funext
            intro X
            apply LinearMap.ext
            intro x
            cases f.app X x
            rfl }⟩


def A1NisLocalPST (category : SmCorQ (k := k)) :=
  { F : PST category // IsA1NisLocal F }

namespace A1NisLocalPST

/-- Forget the locality proofs and view a bundled object as a presheaf with
transfers. -/
abbrev toPST {category : SmCorQ (k := k)}
    (F : A1NisLocalPST category) : PST category :=
  F.1

instance {category : SmCorQ (k := k)} : Coe (A1NisLocalPST category) (PST category) where
  coe F := F.toPST

instance {category : SmCorQ (k := k)} : Category (A1NisLocalPST category) := by
  letI := SmCorQCat category
  exact InducedCategory.category A1NisLocalPST.toPST

/-- Morphisms in `A1NisLocalPST` are exactly ordinary `PST` morphisms between
the underlying presheaves. -/
@[simp] theorem Hom_def {category : SmCorQ (k := k)}
    (F G : A1NisLocalPST category) :
    (F ⟶ G) = (F.toPST ⟶ G.toPST) :=
  rfl

/-- The forgetful functor from bundled `A1`+Nisnevich-local presheaves with
transfers to ordinary presheaves with transfers. -/
def forgetToPST {category : SmCorQ (k := k)} : A1NisLocalPST category ⥤ PST category := by
  letI := SmCorQCat category
  exact inducedFunctor A1NisLocalPST.toPST

@[simp] theorem forgetToPST_obj {category : SmCorQ (k := k)}
    (F : A1NisLocalPST category) :
    (forgetToPST (category := category)).obj F = F.toPST :=
  rfl

@[simp] theorem forgetToPST_map {category : SmCorQ (k := k)}
    {F G : A1NisLocalPST category} (f : F ⟶ G) :
    (forgetToPST (category := category)).map f = f :=
  rfl

instance forgetToPST_full {category : SmCorQ (k := k)} :
    (forgetToPST (category := category)).Full := by
  letI := SmCorQCat category
  change (inducedFunctor A1NisLocalPST.toPST).Full
  infer_instance

instance forgetToPST_faithful {category : SmCorQ (k := k)} :
    (forgetToPST (category := category)).Faithful := by
  letI := SmCorQCat category
  change (inducedFunctor A1NisLocalPST.toPST).Faithful
  infer_instance

/-- An ordinary presheaf with transfers is `A1`+Nisnevich-local exactly when it
lies in the image of the forgetful functor from bundled local objects. -/
theorem exists_obj_forgetToPST_iff {category : SmCorQ (k := k)}
    (F : PST category) :
    (∃ G : A1NisLocalPST category, (forgetToPST (category := category)).obj G = F) ↔
      IsA1NisLocal F := by
  constructor
  · rintro ⟨G, hG⟩
    simpa [forgetToPST] using hG ▸ G.2
  · intro hF
    exact ⟨⟨F, hF⟩, rfl⟩

/-- An ordinary presheaf with transfers underlies a bundled object of
`A1NisLocalPST` exactly when it is both `A1`-local and Nisnevich-local. -/
theorem exists_obj_forgetToPST_iff_localities {category : SmCorQ (k := k)}
    (F : PST category) :
    (∃ G : A1NisLocalPST category, (forgetToPST (category := category)).obj G = F) ↔
      IsA1Local F ∧ IsNisnevichLocal F := by
  rw [exists_obj_forgetToPST_iff, IsA1NisLocal.iff_localities]

/-- A bundled `A1`+Nisnevich-local presheaf carries its `A1`-locality proof. -/
theorem isA1Local {category : SmCorQ (k := k)}
    (F : A1NisLocalPST category) : IsA1Local F.toPST :=
  F.2.1

/-- A bundled `A1`+Nisnevich-local presheaf carries its Nisnevich-locality
proof. -/
theorem isNisnevichLocal {category : SmCorQ (k := k)}
    (F : A1NisLocalPST category) : IsNisnevichLocal F.toPST :=
  F.2.2

end A1NisLocalPST

end

end Boundary
