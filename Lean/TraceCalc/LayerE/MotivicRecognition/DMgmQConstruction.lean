import TraceCalc.ClassicalPeriods.VoevodskyFiniteCorrespondences
import TraceCalc.ClassicalPeriods.VoevodskyFiniteCorrespondencesConcreteBridge
import TraceCalc.LayerE.MotivicRecognition.ManuscriptSpineTargets
import TraceCalc.LayerE.MotivicRecognition.RecognitionTarget

noncomputable section

/-!
# Classical construction spine for `DM_gm(Q)_Q`

This module starts the actual construction route for the classical category of
geometric motives over `Q` with rational coefficients. It deliberately does not
fill the final `DM_gm(Q)_Q` interface by arbitrary named fields. Instead it
records the standard ladder:

* smooth schemes over `Q`,
* finite correspondences over `Q`,
* the additive correspondence category with rational coefficients,
* bounded complexes,
* localization by Nisnevich descent and `A1`-homotopy,
* Karoubi/idempotent completion,
* the resulting `DM_gm(Q)_Q` category data.

Where the current project/mathlib surface does not yet provide the required
scheme-theoretic or categorical primitive, the missing step is named at that
exact construction point as a construction obligation.
-/

universe u v w x y

namespace TraceCalc
namespace MotivicRecognition
namespace DMgmQConstruction

open ClassicalPeriods.VoevodskyFiniteCorrespondences
open ClassicalPeriods

/-- Construction obligation for the base category `Sm/Q`.

This is the place where a future implementation should import or build smooth schemes over `Q`,
not a final-target placeholder for `DM_gm(Q)_Q`. -/
structure SmoothQSchemeConstruction where
  SmoothQScheme : Type u
  distinguished : SmoothQScheme
  product : SmoothQScheme → SmoothQScheme → SmoothQScheme
  tripleProduct : SmoothQScheme → SmoothQScheme → SmoothQScheme → SmoothQScheme
  terminalObject : Option SmoothQScheme
  affineLineObject : Option SmoothQScheme
  baseFieldIsQ : FieldIsQData Rat

namespace SmoothQSchemeConstruction

/-- The geometric base induced by the smooth `Q`-scheme construction. -/
def geometricBase (construction : SmoothQSchemeConstruction.{u}) : GeometricBase.{u} where
  Scheme := construction.SmoothQScheme
  product := construction.product
  tripleProduct := construction.tripleProduct

end SmoothQSchemeConstruction

/-- Smooth-scheme construction induced by the existing Wall 10A `SchemeOverQ` base.

The AG content of smoothness/separatedness/finite type is represented in the Wall 10A scheme layer;
this projection supplies the base objects and products needed by the finite-correspondence rung. -/
def smoothQSchemeFromWall10A : SmoothQSchemeConstruction.{1} where
  SmoothQScheme := ClassicalPeriods.Wall10A.SchemeOverQ
  distinguished :=
    { X := ClassicalPeriods.Wall10A.SpecQ
      structureMap := CategoryTheory.CategoryStruct.id ClassicalPeriods.Wall10A.SpecQ }
  product := ClassicalPeriods.Wall10A.SchemeOverQ.prod
  tripleProduct := ClassicalPeriods.Wall10A.SchemeOverQ.tripleProduct
  terminalObject := none
  affineLineObject := none
  baseFieldIsQ := FieldIsQData.id

abbrev SmoothQScheme (construction : SmoothQSchemeConstruction.{u}) : Type u :=
  construction.SmoothQScheme

/-- Construction obligation for finite-correspondence composition over `Q`.

The fields are exactly the cycle-operation, diagonal, projection, relation-respect, and composition
law data needed by `VoevodskyFiniteCorrespondences`. -/
structure FiniteCorrespondenceCompositionConstruction
    (smooth : SmoothQSchemeConstruction.{u}) where
  operations : CycleOperations smooth.geometricBase
  diagonal : (X : smooth.SmoothQScheme) → DiagonalData smooth.geometricBase X
  projection :
    (X Y Z : smooth.SmoothQScheme) →
      CorrespondenceProjectionData smooth.geometricBase operations X Y Z
  respect :
    (X Y Z : smooth.SmoothQScheme) →
      ComposeRespectsRelData operations (projection X Y Z)
  laws :
    FiniteCorrespondenceCompositionLaws smooth.geometricBase operations diagonal projection respect

namespace FiniteCorrespondenceCompositionConstruction

/-- The Wall 10A bridge already exports a concrete Voevodsky geometric base; a provider over that
base gives the finite-correspondence composition construction for the `Sm/Q` construction above. -/
structure Wall10AProvider where
  operations : CycleOperations ClassicalPeriods.Wall10A.SchemeOverQ.geometricBase
  diagonal :
    (X : ClassicalPeriods.Wall10A.SchemeOverQ) →
      DiagonalData ClassicalPeriods.Wall10A.SchemeOverQ.geometricBase X
  projection :
    (X Y Z : ClassicalPeriods.Wall10A.SchemeOverQ) →
      CorrespondenceProjectionData ClassicalPeriods.Wall10A.SchemeOverQ.geometricBase operations X Y Z
  respect :
    (X Y Z : ClassicalPeriods.Wall10A.SchemeOverQ) →
      ComposeRespectsRelData operations (projection X Y Z)
  laws :
    FiniteCorrespondenceCompositionLaws
      ClassicalPeriods.Wall10A.SchemeOverQ.geometricBase operations diagonal projection respect

def ofWall10AProvider
    (provider : Wall10AProvider.{v, w, x}) :
    FiniteCorrespondenceCompositionConstruction smoothQSchemeFromWall10A where
  operations := provider.operations
  diagonal := provider.diagonal
  projection := provider.projection
  respect := provider.respect
  laws := provider.laws

/-- Exact blocker for using a non-definitional concrete provider: it must be transported to the
Wall 10A geometric base before the operations and law package can populate this rung. -/
structure Wall10AProviderTransportObligation
    (provider : ConcreteVoevodskyCorrespondenceProvider.{1, v, w, x}) where
  base_eq : provider.base = ClassicalPeriods.Wall10A.SchemeOverQ.geometricBase
  transportedProvider : Wall10AProvider.{v, w, x}

end FiniteCorrespondenceCompositionConstruction

abbrev FiniteCorrespondenceQ
    {smooth : SmoothQSchemeConstruction.{u}}
  (X Y : SmoothQScheme smooth) :=
  FiniteCorrespondence smooth.geometricBase X Y

/-- The category of finite correspondences over `Q`, with its composition data projected from the
finite-correspondence construction obligation. -/
structure FiniteCorrespondenceCategoryQ
    (smooth : SmoothQSchemeConstruction.{u}) where
  composition : FiniteCorrespondenceCompositionConstruction smooth
namespace FiniteCorrespondenceCategoryQ

/-- Construct the finite-correspondence category rung directly from the concrete Voevodsky provider
already present in `ClassicalPeriods`. -/
def ofWall10AProvider
  (provider : FiniteCorrespondenceCompositionConstruction.Wall10AProvider.{v, w, x}) :
    FiniteCorrespondenceCategoryQ smoothQSchemeFromWall10A where
  composition := FiniteCorrespondenceCompositionConstruction.ofWall10AProvider provider

end FiniteCorrespondenceCategoryQ

namespace FiniteCorrespondenceCategoryQ

def Obj {smooth : SmoothQSchemeConstruction.{u}}
    (_category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth) : Type u :=
  smooth.SmoothQScheme

def distinguishedObject {smooth : SmoothQSchemeConstruction.{u}}
    (_category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth) : smooth.SmoothQScheme :=
  smooth.distinguished

def Hom {smooth : SmoothQSchemeConstruction.{u}}
    (category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth)
  (X Y : category.Obj) :=
  FiniteCorrespondence smooth.geometricBase X Y

def id {smooth : SmoothQSchemeConstruction.{u}}
    (category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth)
    (X : category.Obj) : category.Hom X X :=
  identity (category.composition.diagonal X)

def comp {smooth : SmoothQSchemeConstruction.{u}}
    (category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth)
    {X Y Z : category.Obj} (f : category.Hom X Y) (g : category.Hom Y Z) :
    category.Hom X Z :=
  compose category.composition.operations
    (category.composition.projection X Y Z)
    (category.composition.respect X Y Z) f g

theorem id_comp {smooth : SmoothQSchemeConstruction.{u}}
    (category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth)
    {X Y : category.Obj} (f : category.Hom X Y) :
    category.comp (category.id X) f = f :=
  category.composition.laws.id_left f

theorem comp_id {smooth : SmoothQSchemeConstruction.{u}}
    (category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth)
    {X Y : category.Obj} (f : category.Hom X Y) :
    category.comp f (category.id Y) = f :=
  category.composition.laws.id_right f

theorem assoc {smooth : SmoothQSchemeConstruction.{u}}
    (category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth)
    {W X Y Z : category.Obj}
    (f : category.Hom W X) (g : category.Hom X Y) (h : category.Hom Y Z) :
    category.comp (category.comp f g) h = category.comp f (category.comp g h) :=
  category.composition.laws.assoc f g h

def ofWall10AGraph
    (category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A)
    {X Y : category.Obj}
    (f : ClassicalPeriods.Wall10A.SchemeOverQ.Hom X Y)
    (graphData : ClassicalPeriods.Wall10A.SchemeOverQ.GraphFiniteCorrespondenceData f) :
    category.Hom X Y :=
  ClassicalPeriods.Wall10A.SchemeOverQ.toWall10BFiniteCorrespondence
    (ClassicalPeriods.Wall10A.SchemeOverQ.graphCorrespondence graphData)

/-- Source/target compatibility of the finite-correspondence category projection: its objects are
definitionally the smooth `Q`-schemes carried by the chosen base construction. -/
theorem obj_eq_smoothQScheme {smooth : SmoothQSchemeConstruction.{u}}
    (category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth) :
    category.Obj = smooth.SmoothQScheme :=
  rfl

end FiniteCorrespondenceCategoryQ

/-- Construction obligation for the additive rational-coefficient correspondence category. -/
structure RationalCorrespondenceLinearization
  {smooth : SmoothQSchemeConstruction.{u}}
  (category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth) where
  Obj : Type u
  Hom : Obj → Obj → Type y
  id : ∀ X, Hom X X
  comp : ∀ {X Y Z : Obj}, Hom X Y → Hom Y Z → Hom X Z
  fromIntegralObject : category.Obj → Obj
  fromIntegralCorrespondence :
    ∀ {X Y : category.Obj}, category.Hom X Y → Hom (fromIntegralObject X) (fromIntegralObject Y)
  qScalarAction : Rat → ∀ {X Y : Obj}, Hom X Y → Hom X Y
  addHom : ∀ {X Y : Obj}, Hom X Y → Hom X Y → Hom X Y
  zeroHom : ∀ {X Y : Obj}, Hom X Y
  fromIntegral_id : ∀ X, fromIntegralCorrespondence (category.id X) = id (fromIntegralObject X)
  fromIntegral_comp : ∀ {X Y Z : category.Obj}
    (f : category.Hom X Y) (g : category.Hom Y Z),
      comp (fromIntegralCorrespondence f) (fromIntegralCorrespondence g) =
        fromIntegralCorrespondence (category.comp f g)

/-- Category-law package for the formal `Rat`-linearization of finite correspondences. -/
structure RationalCorrespondenceLawPackage
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  (linearization : RationalCorrespondenceLinearization category) : Type (max u (max v (max w (max x y)))) where
  id_comp :
    ∀ {X Y : linearization.Obj} (f : linearization.Hom X Y),
      linearization.comp (linearization.id X) f = f
  comp_id :
    ∀ {X Y : linearization.Obj} (f : linearization.Hom X Y),
      linearization.comp f (linearization.id Y) = f
  zero_comp :
    ∀ {X Y Z : linearization.Obj} (f : linearization.Hom Y Z),
      linearization.comp (@linearization.zeroHom X Y) f = @linearization.zeroHom X Z
  comp_zero :
    ∀ {X Y Z : linearization.Obj} (f : linearization.Hom X Y),
      linearization.comp f (@linearization.zeroHom Y Z) = @linearization.zeroHom X Z
  add_comp :
    ∀ {X Y Z : linearization.Obj}
      (f g : linearization.Hom X Y) (h : linearization.Hom Y Z),
      linearization.comp (linearization.addHom f g) h =
        linearization.addHom (linearization.comp f h) (linearization.comp g h)
  comp_add :
    ∀ {X Y Z : linearization.Obj}
      (f : linearization.Hom X Y) (g h : linearization.Hom Y Z),
      linearization.comp f (linearization.addHom g h) =
        linearization.addHom (linearization.comp f g) (linearization.comp f h)
  smul_comp :
    ∀ (q : Rat) {X Y Z : linearization.Obj}
      (f : linearization.Hom X Y) (g : linearization.Hom Y Z),
      linearization.comp (linearization.qScalarAction q f) g =
        linearization.qScalarAction q (linearization.comp f g)
  comp_smul :
    ∀ (q : Rat) {X Y Z : linearization.Obj}
      (f : linearization.Hom X Y) (g : linearization.Hom Y Z),
      linearization.comp f (linearization.qScalarAction q g) =
        linearization.qScalarAction q (linearization.comp f g)
  assoc :
    ∀ {W X Y Z : linearization.Obj}
      (f : linearization.Hom W X) (g : linearization.Hom X Y) (h : linearization.Hom Y Z),
      linearization.comp (linearization.comp f g) h =
        linearization.comp f (linearization.comp g h)

/-- Genuine `Q`-linear finite-correspondence category obtained by adjoining the law package to the
formal `Rat`-linearization. -/
structure RationalFiniteCorrespondenceCategoryQ
  {smooth : SmoothQSchemeConstruction.{u}}
  (category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth) where
  linearization : RationalCorrespondenceLinearization category
  laws : RationalCorrespondenceLawPackage linearization

namespace FormalRatLinearization

/-- Formal `Rat`-linear combinations of integral finite correspondences. This is the first honest
rational-coefficient rung available from the existing integral provider/law package. -/
private def termsSetoid
    {smooth : SmoothQSchemeConstruction.{u}}
    (category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth)
    (X Y : smooth.SmoothQScheme) : Setoid (List (Rat × category.Hom X Y)) where
  r := List.Perm
  iseqv := ⟨List.Perm.refl, List.Perm.symm, List.Perm.trans⟩

structure FormalRatHom
    {smooth : SmoothQSchemeConstruction.{u}}
    (category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth)
    (X Y : smooth.SmoothQScheme) where
  terms : Quotient (termsSetoid category X Y)

namespace FormalRatHom

@[ext] theorem ext
    {smooth : SmoothQSchemeConstruction.{u}}
    {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
    {X Y : smooth.SmoothQScheme}
    {f g : FormalRatHom category X Y}
    (h : f.terms = g.terms) : f = g := by
  cases f
  cases g
  cases h
  rfl

private def ofList
    {smooth : SmoothQSchemeConstruction.{u}}
    {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
    {X Y : smooth.SmoothQScheme}
    (terms : List (Rat × category.Hom X Y)) : FormalRatHom category X Y where
  terms := Quotient.mk _ terms

private def compTermsRaw
    {smooth : SmoothQSchemeConstruction.{u}}
    {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
    {X Y Z : smooth.SmoothQScheme}
    (fterms : List (Rat × category.Hom X Y))
    (gterms : List (Rat × category.Hom Y Z)) :
    List (Rat × category.Hom X Z) :=
  fterms.flatMap fun left =>
    gterms.map fun right => (left.1 * right.1, category.comp left.2 right.2)

private theorem compTermsRaw_left_perm
    {smooth : SmoothQSchemeConstruction.{u}}
    {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
    {X Y Z : smooth.SmoothQScheme}
    {fterms₁ fterms₂ : List (Rat × category.Hom X Y)}
    (h : List.Perm fterms₁ fterms₂)
    (gterms : List (Rat × category.Hom Y Z)) :
    List.Perm (compTermsRaw (category := category) fterms₁ gterms)
      (compTermsRaw (category := category) fterms₂ gterms) :=
  h.flatMap_right _

private theorem compTermsRaw_right_perm
    {smooth : SmoothQSchemeConstruction.{u}}
    {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
    {X Y Z : smooth.SmoothQScheme}
    (fterms : List (Rat × category.Hom X Y))
    {gterms₁ gterms₂ : List (Rat × category.Hom Y Z)}
    (h : List.Perm gterms₁ gterms₂) :
    List.Perm (compTermsRaw (category := category) fterms gterms₁)
      (compTermsRaw (category := category) fterms gterms₂) := by
  exact (List.Perm.flatMap_left fterms) fun _ _ => h.map _

def zero
    {smooth : SmoothQSchemeConstruction.{u}}
    {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
    (X Y : smooth.SmoothQScheme) : FormalRatHom category X Y :=
  ofList []

def add
    {smooth : SmoothQSchemeConstruction.{u}}
    {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
    {X Y : smooth.SmoothQScheme}
    (f g : FormalRatHom category X Y) : FormalRatHom category X Y where
  terms := Quotient.liftOn₂ f.terms g.terms
    (fun fterms gterms => Quotient.mk _ (fterms ++ gterms))
    (by
      intro fterms₁ gterms₁ fterms₂ gterms₂ hfterms hgterms
      exact Quotient.sound <|
        (hfterms.append_right _).trans (hgterms.append_left _))

def smul
    {smooth : SmoothQSchemeConstruction.{u}}
    {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
    (q : Rat) {X Y : smooth.SmoothQScheme}
    (f : FormalRatHom category X Y) : FormalRatHom category X Y where
  terms := Quotient.liftOn f.terms
    (fun fterms => Quotient.mk _ (fterms.map fun term => (q * term.1, term.2)))
    (by
      intro fterms₁ fterms₂ hfterms
      exact Quotient.sound (hfterms.map _))

def ofIntegral
    {smooth : SmoothQSchemeConstruction.{u}}
    {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
    {X Y : smooth.SmoothQScheme}
    (f : category.Hom X Y) : FormalRatHom category X Y :=
  ofList [(1, f)]

def id
    {smooth : SmoothQSchemeConstruction.{u}}
    {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
    (X : smooth.SmoothQScheme) : FormalRatHom category X X :=
  ofIntegral (category.id X)

def comp
    {smooth : SmoothQSchemeConstruction.{u}}
    {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
    {X Y Z : smooth.SmoothQScheme}
    (f : FormalRatHom category X Y)
    (g : FormalRatHom category Y Z) : FormalRatHom category X Z where
  terms := Quotient.liftOn₂ f.terms g.terms
    (fun fterms gterms => Quotient.mk _ (compTermsRaw (category := category) fterms gterms))
    (by
      intro fterms₁ gterms₁ fterms₂ gterms₂ hfterms hgterms
      exact Quotient.sound <|
        (compTermsRaw_left_perm (category := category) hfterms gterms₁).trans
          (compTermsRaw_right_perm (category := category) fterms₂ hgterms))
private theorem id_comp_raw_perm
    {smooth : SmoothQSchemeConstruction.{u}}
    {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
    {X Y : smooth.SmoothQScheme}
    (terms : List (Rat × category.Hom X Y)) :
    List.Perm (compTermsRaw (category := category) [(1, category.id X)] terms) terms := by
  induction terms with
  | nil => exact List.Perm.nil
  | cons head tail ih =>
      rcases head with ⟨q, f⟩
      have htail :
          List.Perm
            (List.map (fun right => (right.1, category.comp (category.id X) right.2)) tail)
            tail := by
        simpa [compTermsRaw, category.id_comp] using ih
      have hhead : category.comp (category.id X) f = f := category.id_comp f
      simpa [compTermsRaw, hhead] using
        (List.Perm.cons (q, category.comp (category.id X) f) htail)

private theorem comp_id_raw_perm
    {smooth : SmoothQSchemeConstruction.{u}}
    {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
    {X Y : smooth.SmoothQScheme}
    (terms : List (Rat × category.Hom X Y)) :
    List.Perm (compTermsRaw (category := category) terms [(1, category.id Y)]) terms := by
  induction terms with
  | nil => exact List.Perm.nil
  | cons head tail ih =>
      rcases head with ⟨q, f⟩
      have htail :
          List.Perm
            (tail.flatMap fun left => [(left.1, category.comp left.2 (category.id Y))])
            tail := by
        simpa [compTermsRaw, category.comp_id] using ih
      have hhead : category.comp f (category.id Y) = f := category.comp_id f
      simpa [compTermsRaw, hhead] using
        (List.Perm.cons (q, category.comp f (category.id Y)) htail)

private theorem comp_zero_raw_perm
    {smooth : SmoothQSchemeConstruction.{u}}
    {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
    {X Y Z : smooth.SmoothQScheme}
    (terms : List (Rat × category.Hom X Y)) :
    List.Perm (compTermsRaw (category := category) terms ([] : List (Rat × category.Hom Y Z))) [] := by
  induction terms with
  | nil => exact List.Perm.nil
  | cons _ tail ih =>
      simpa [compTermsRaw] using ih

private theorem smul_head_map
    {smooth : SmoothQSchemeConstruction.{u}}
    {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
    {X Y Z : smooth.SmoothQScheme}
    (q : Rat)
    (head : Rat × category.Hom X Y)
    (gterms : List (Rat × category.Hom Y Z)) :
    List.map (fun right => ((q * head.1) * right.1, category.comp head.2 right.2)) gterms =
      List.map ((fun term => (q * term.1, term.2)) ∘
        fun right => (head.1 * right.1, category.comp head.2 right.2)) gterms := by
  induction gterms with
  | nil => rfl
  | cons right tail ih =>
      cases head
      cases right
      simp [ih, mul_assoc]

private theorem smul_comp_raw
    {smooth : SmoothQSchemeConstruction.{u}}
    {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
    (q : Rat) {X Y Z : smooth.SmoothQScheme}
    (fterms : List (Rat × category.Hom X Y))
    (gterms : List (Rat × category.Hom Y Z)) :
    compTermsRaw (category := category)
      (fterms.map fun term => (q * term.1, term.2)) gterms =
    (compTermsRaw (category := category) fterms gterms).map
      (fun term => (q * term.1, term.2)) := by
  induction fterms with
  | nil => rfl
  | cons head tail ih =>
      simpa [compTermsRaw, List.map_append, smul_head_map] using ih

private theorem comp_smul_head
    {smooth : SmoothQSchemeConstruction.{u}}
    {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
    {X Y Z : smooth.SmoothQScheme}
    (q : Rat)
    (head : Rat × category.Hom X Y)
    (gterms : List (Rat × category.Hom Y Z)) :
    List.map ((fun right => (head.1 * right.1, category.comp head.2 right.2)) ∘
        fun term => (q * term.1, term.2)) gterms =
      List.map ((fun term => (q * term.1, term.2)) ∘
        fun right => (head.1 * right.1, category.comp head.2 right.2)) gterms := by
  induction gterms with
  | nil => rfl
  | cons right tail ih =>
      cases head
      cases right
      simp [ih, mul_assoc, mul_left_comm, mul_comm]

private theorem comp_smul_raw
    {smooth : SmoothQSchemeConstruction.{u}}
    {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
    (q : Rat) {X Y Z : smooth.SmoothQScheme}
    (fterms : List (Rat × category.Hom X Y))
    (gterms : List (Rat × category.Hom Y Z)) :
    compTermsRaw (category := category) fterms
      (gterms.map fun term => (q * term.1, term.2)) =
    (compTermsRaw (category := category) fterms gterms).map
      (fun term => (q * term.1, term.2)) := by
  induction fterms with
  | nil => rfl
  | cons head tail ih =>
      simpa [compTermsRaw, List.map_append, comp_smul_head] using ih

private theorem assoc_pair_map
    {smooth : SmoothQSchemeConstruction.{u}}
    {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
    {W X Y Z : smooth.SmoothQScheme}
    (head : Rat × category.Hom W X)
    (mid : Rat × category.Hom X Y)
    (hterms : List (Rat × category.Hom Y Z)) :
    List.map (fun right =>
      (((head.1 * mid.1) * right.1), category.comp (category.comp head.2 mid.2) right.2)) hterms =
    List.map (fun right =>
      (head.1 * (mid.1 * right.1), category.comp head.2 (category.comp mid.2 right.2))) hterms := by
  induction hterms with
  | nil => rfl
  | cons right tail ih =>
      rw [List.map_cons, List.map_cons]
      refine congrArg₂ List.cons ?_ ih
      rcases head with ⟨q1, f1⟩
      rcases mid with ⟨q2, f2⟩
      rcases right with ⟨q3, f3⟩
      simpa [Prod.mk.injEq, mul_assoc] using category.assoc f1 f2 f3

private theorem assoc_head
    {smooth : SmoothQSchemeConstruction.{u}}
    {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
    {W X Y Z : smooth.SmoothQScheme}
    (head : Rat × category.Hom W X)
    (gterms : List (Rat × category.Hom X Y))
    (hterms : List (Rat × category.Hom Y Z)) :
    compTermsRaw (category := category)
      (gterms.map fun mid => (head.1 * mid.1, category.comp head.2 mid.2)) hterms =
    gterms.flatMap fun mid =>
      hterms.map fun right =>
        (head.1 * (mid.1 * right.1), category.comp head.2 (category.comp mid.2 right.2)) := by
  induction gterms with
  | nil => rfl
  | cons mid tail ih =>
      rw [compTermsRaw, List.map_cons, List.flatMap_cons, assoc_pair_map]
      simpa [compTermsRaw] using ih

private theorem map_bind_head
    {smooth : SmoothQSchemeConstruction.{u}}
    {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
    {W X Y Z : smooth.SmoothQScheme}
    (head : Rat × category.Hom W X)
    (gterms : List (Rat × category.Hom X Y))
    (hterms : List (Rat × category.Hom Y Z)) :
    (gterms.flatMap fun mid =>
      hterms.map fun right =>
        (head.1 * (mid.1 * right.1), category.comp head.2 (category.comp mid.2 right.2))) =
    (compTermsRaw (category := category) gterms hterms).map
      (fun right => (head.1 * right.1, category.comp head.2 right.2)) := by
  induction gterms with
  | nil => rfl
  | cons mid tail ih =>
      simp [compTermsRaw, List.map_append, assoc_pair_map, ih]

private theorem comp_assoc_raw
    {smooth : SmoothQSchemeConstruction.{u}}
    {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
    {W X Y Z : smooth.SmoothQScheme}
    (fterms : List (Rat × category.Hom W X))
    (gterms : List (Rat × category.Hom X Y))
    (hterms : List (Rat × category.Hom Y Z)) :
    compTermsRaw (category := category)
      (compTermsRaw (category := category) fterms gterms) hterms =
    compTermsRaw (category := category) fterms
      (compTermsRaw (category := category) gterms hterms) := by
  induction fterms with
  | nil => rfl
  | cons head tail ih =>
      calc
        compTermsRaw (category := category)
            (compTermsRaw (category := category) (head :: tail) gterms) hterms
            = compTermsRaw (category := category)
                (List.map (fun right => (head.1 * right.1, category.comp head.2 right.2)) gterms ++
                  compTermsRaw (category := category) tail gterms) hterms := by
                  rfl
        _ = compTermsRaw (category := category)
              (List.map (fun right => (head.1 * right.1, category.comp head.2 right.2)) gterms) hterms ++
            compTermsRaw (category := category)
              (compTermsRaw (category := category) tail gterms) hterms := by
                simp [compTermsRaw]
        _ = (gterms.flatMap fun mid =>
              hterms.map fun right =>
                (head.1 * (mid.1 * right.1), category.comp head.2 (category.comp mid.2 right.2))) ++
            compTermsRaw (category := category)
              (compTermsRaw (category := category) tail gterms) hterms := by
                rw [assoc_head]
        _ = (compTermsRaw (category := category) gterms hterms).map
              (fun right => (head.1 * right.1, category.comp head.2 right.2)) ++
            compTermsRaw (category := category)
              (compTermsRaw (category := category) tail gterms) hterms := by
                rw [map_bind_head]
        _ = (compTermsRaw (category := category) gterms hterms).map
              (fun right => (head.1 * right.1, category.comp head.2 right.2)) ++
            compTermsRaw (category := category) tail
              (compTermsRaw (category := category) gterms hterms) := by
                rw [ih]
        _ = compTermsRaw (category := category) (head :: tail)
              (compTermsRaw (category := category) gterms hterms) := by
                rfl

@[simp] theorem id_comp
    {smooth : SmoothQSchemeConstruction.{u}}
    {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
    {X Y : smooth.SmoothQScheme}
    (f : FormalRatHom category X Y) :
    comp (id (category := category) X) f = f := by
  cases f with
  | mk terms =>
      apply ext
      refine Quotient.inductionOn terms ?_
      intro rawTerms
      exact Quotient.sound (id_comp_raw_perm (category := category) rawTerms)

@[simp] theorem comp_id
    {smooth : SmoothQSchemeConstruction.{u}}
    {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
    {X Y : smooth.SmoothQScheme}
    (f : FormalRatHom category X Y) :
    comp f (id (category := category) Y) = f := by
  cases f with
  | mk terms =>
      apply ext
      refine Quotient.inductionOn terms ?_
      intro rawTerms
      exact Quotient.sound (comp_id_raw_perm (category := category) rawTerms)

@[simp] theorem zero_comp
    {smooth : SmoothQSchemeConstruction.{u}}
    {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
    {X Y Z : smooth.SmoothQScheme}
    (f : FormalRatHom category Y Z) :
    comp (zero (category := category) X Y) f = zero (category := category) X Z := by
  cases f with
  | mk terms =>
      apply ext
      refine Quotient.inductionOn terms ?_
      intro rawTerms
      rfl

@[simp] theorem comp_zero
    {smooth : SmoothQSchemeConstruction.{u}}
    {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
    {X Y Z : smooth.SmoothQScheme}
    (f : FormalRatHom category X Y) :
    comp f (zero (category := category) Y Z) = zero (category := category) X Z := by
  cases f with
  | mk terms =>
      apply ext
      refine Quotient.inductionOn terms ?_
      intro rawTerms
      exact Quotient.sound (comp_zero_raw_perm (category := category) rawTerms)

@[simp] theorem add_comp
    {smooth : SmoothQSchemeConstruction.{u}}
    {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
    {X Y Z : smooth.SmoothQScheme}
    (f g : FormalRatHom category X Y)
    (h : FormalRatHom category Y Z) :
    comp (add f g) h = add (comp f h) (comp g h) := by
  cases f with
  | mk fterms =>
      cases g with
      | mk gterms =>
          cases h with
          | mk hterms =>
              apply ext
              refine Quotient.inductionOn₃ fterms gterms hterms ?_
              intro rawF rawG rawH
              refine Quotient.sound ?_
              change List.Perm
                (compTermsRaw (category := category) (rawF ++ rawG) rawH)
                (compTermsRaw (category := category) rawF rawH ++
                  compTermsRaw (category := category) rawG rawH)
              simpa [compTermsRaw]

@[simp] theorem comp_add
    {smooth : SmoothQSchemeConstruction.{u}}
    {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
    {X Y Z : smooth.SmoothQScheme}
    (f : FormalRatHom category X Y)
    (g h : FormalRatHom category Y Z) :
    comp f (add g h) = add (comp f g) (comp f h) := by
  cases f with
  | mk fterms =>
      cases g with
      | mk gterms =>
          cases h with
          | mk hterms =>
              apply ext
              refine Quotient.inductionOn₃ fterms gterms hterms ?_
              intro rawF rawG rawH
              refine Quotient.sound ?_
              simpa [compTermsRaw] using
                (List.flatMap_append_perm rawF
                  (fun left => rawG.map fun right => (left.1 * right.1, category.comp left.2 right.2))
                  (fun left => rawH.map fun right => (left.1 * right.1, category.comp left.2 right.2))).symm

@[simp] theorem smul_comp
    {smooth : SmoothQSchemeConstruction.{u}}
    {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
    (q : Rat) {X Y Z : smooth.SmoothQScheme}
    (f : FormalRatHom category X Y)
    (g : FormalRatHom category Y Z) :
    comp (smul q f) g = smul q (comp f g) := by
  cases f with
  | mk fterms =>
      cases g with
      | mk gterms =>
          apply ext
          refine Quotient.inductionOn₂ fterms gterms ?_
          intro rawF rawG
          exact Quotient.sound <| by
            rw [smul_comp_raw (category := category) q rawF rawG]
            exact List.Perm.refl _

@[simp] theorem comp_smul
    {smooth : SmoothQSchemeConstruction.{u}}
    {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
    (q : Rat) {X Y Z : smooth.SmoothQScheme}
    (f : FormalRatHom category X Y)
    (g : FormalRatHom category Y Z) :
    comp f (smul q g) = smul q (comp f g) := by
  cases f with
  | mk fterms =>
      cases g with
      | mk gterms =>
          apply ext
          refine Quotient.inductionOn₂ fterms gterms ?_
          intro rawF rawG
          exact Quotient.sound <| by
            rw [comp_smul_raw (category := category) q rawF rawG]
            exact List.Perm.refl _

@[simp] theorem fromIntegral_id
    {smooth : SmoothQSchemeConstruction.{u}}
    {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
    (X : smooth.SmoothQScheme) :
    ofIntegral (category := category) (category.id X) = id (category := category) X :=
  rfl

@[simp] theorem fromIntegral_comp
    {smooth : SmoothQSchemeConstruction.{u}}
    {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
    {X Y Z : smooth.SmoothQScheme}
    (f : category.Hom X Y)
    (g : category.Hom Y Z) :
    comp (ofIntegral (category := category) f) (ofIntegral (category := category) g) =
      ofIntegral (category := category) (category.comp f g) := by
  apply ext
  refine Quotient.sound ?_
  change List.Perm [(1 * 1, category.comp f g)] [(1, category.comp f g)]
  simp

@[simp] theorem assoc
    {smooth : SmoothQSchemeConstruction.{u}}
    {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
    {W X Y Z : smooth.SmoothQScheme}
    (f : FormalRatHom category W X)
    (g : FormalRatHom category X Y)
    (h : FormalRatHom category Y Z) :
    comp (comp f g) h = comp f (comp g h) := by
  cases f with
  | mk fterms =>
      cases g with
      | mk gterms =>
          cases h with
          | mk hterms =>
              apply ext
              refine Quotient.inductionOn₃ fterms gterms hterms ?_
              intro rawF rawG rawH
              exact Quotient.sound <| by
                rw [comp_assoc_raw (category := category) rawF rawG rawH]
                exact List.Perm.refl _

end FormalRatHom

/-- Honest rational-coefficient correspondence category obtained by formal `Rat`-linearization of
the integral finite-correspondence homs. -/
def ofFormalRatLinearization
    {smooth : SmoothQSchemeConstruction.{u}}
    (category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth) :
    _root_.TraceCalc.MotivicRecognition.DMgmQConstruction.RationalCorrespondenceLinearization
      category where
  Obj := smooth.SmoothQScheme
  Hom := FormalRatHom category
  id := FormalRatHom.id (category := category)
  comp := FormalRatHom.comp
  fromIntegralObject := fun X => X
  fromIntegralCorrespondence := fun f => FormalRatHom.ofIntegral (category := category) f
  qScalarAction := fun q => FormalRatHom.smul q
  addHom := FormalRatHom.add
  zeroHom := fun {X Y} => FormalRatHom.zero X Y
  fromIntegral_id := FormalRatHom.fromIntegral_id
  fromIntegral_comp := FormalRatHom.fromIntegral_comp

/-- Full law package for the formal `Rat`-linear finite-correspondence category. -/
def lawPackage
    {smooth : SmoothQSchemeConstruction.{u}}
    (category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth) :
    RationalCorrespondenceLawPackage (ofFormalRatLinearization category) where
  id_comp := FormalRatHom.id_comp
  comp_id := FormalRatHom.comp_id
  zero_comp := FormalRatHom.zero_comp
  comp_zero := FormalRatHom.comp_zero
  add_comp := FormalRatHom.add_comp
  comp_add := FormalRatHom.comp_add
  smul_comp := FormalRatHom.smul_comp
  comp_smul := FormalRatHom.comp_smul
  assoc := FormalRatHom.assoc

/-- The honest `Q`-linear finite-correspondence category obtained from formal `Rat`-linearization
and its discharged law package. -/
def rationalFiniteCorrespondenceCategory
    {smooth : SmoothQSchemeConstruction.{u}}
    (category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth) :
    RationalFiniteCorrespondenceCategoryQ category where
  linearization := ofFormalRatLinearization category
  laws := lawPackage category

end FormalRatLinearization

/-- Construction package for bounded chain complexes of rational finite correspondences.

This is the first honest complex-level rung: a complex carries degree-indexed rational
correspondence objects, differentials between adjacent degrees, a $d^2 = 0$ witness, boundedness
data, and chain maps with degreewise components compatible with the differentials. -/
structure BoundedComplexOfFiniteCorrespondencesQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  (rationalCategory : RationalFiniteCorrespondenceCategoryQ category) where
  Complex : Type u
  degreeActive : Complex → Int → Prop
  objectAt : Complex → Int → rationalCategory.linearization.Obj
  differential :
    (C : Complex) → {n : Int} →
      (hn : degreeActive C n) →
      (hnPred : degreeActive C (n - 1)) →
      rationalCategory.linearization.Hom
        (objectAt C n) (objectAt C (n - 1))
  hom : Complex → Complex → Type v
  id : ∀ X, hom X X
  comp : ∀ {X Y Z}, hom X Y → hom Y Z → hom X Z
  component :
    ∀ {C D : Complex} (f : hom C D) {n : Int}
      (hCn : degreeActive C n) (hDn : degreeActive D n),
      rationalCategory.linearization.Hom
        (objectAt C n) (objectAt D n)
  motiveOfSmoothScheme : category.Obj → Complex
  bounded : Complex → Prop
  directSum : Complex → Complex → Complex
  cone : ∀ {C D : Complex}, hom C D → Complex
  mapOfIntegralCorrespondence :
    ∀ {X Y : category.Obj},
      category.Hom X Y → hom (motiveOfSmoothScheme X) (motiveOfSmoothScheme Y)
  directSumDesc :
    ∀ {C D E : Complex}, hom C D → hom C E → hom C (directSum D E)
  motiveOfSmoothSchemeBounded :
    ∀ X : category.Obj, bounded (motiveOfSmoothScheme X)
  directSumBounded :
    ∀ {C D : Complex}, bounded C → bounded D → bounded (directSum C D)
  coneBounded :
    ∀ {C D : Complex} (f : hom C D), bounded C → bounded D → bounded (cone f)
  bounded_window :
    ∀ {C : Complex}, bounded C →
      ∃ lower upper : Int, ∀ {n : Int}, degreeActive C n → lower ≤ n ∧ n ≤ upper
  differentialSquaresZero :
    ∀ (C : Complex) {n : Int}
      (hnSucc : degreeActive C (n + 1))
      (hn : degreeActive C n)
      (hnPred : degreeActive C (n - 1)),
      rationalCategory.linearization.comp
        (differential C hnSucc (by simpa using hn))
        (differential (n := n + 1 - 1) C (by simpa using hn) (by simpa using hnPred)) =
        rationalCategory.linearization.zeroHom
  component_commutes :
    ∀ {C D : Complex} (f : hom C D) {n : Int}
      (hCSucc : degreeActive C (n + 1)) (hC : degreeActive C n)
      (hDSucc : degreeActive D (n + 1)) (hD : degreeActive D n),
      rationalCategory.linearization.comp
          (differential C hCSucc (by simpa using hC))
          (component (n := n + 1 - 1) f (by simpa using hC) (by simpa using hD)) =
        rationalCategory.linearization.comp
          (component f hCSucc hDSucc)
          (differential D hDSucc (by simpa using hD))
  id_comp : ∀ {X Y : Complex} (f : hom X Y), comp (id X) f = f
  comp_id : ∀ {X Y : Complex} (f : hom X Y), comp f (id Y) = f
  mapOfIntegralIdentityTarget : Prop
  mapOfIntegralCompositionTarget : Prop
  assoc :
    ∀ {W X Y Z : Complex} (f : hom W X) (g : hom X Y) (h : hom Y Z),
      comp (comp f g) h = comp f (comp g h)

/-- Minimal category interface used for localization-factorization data. -/
structure LocalizationTargetCategoryQ where
  Obj : Type u
  hom : Obj → Obj → Type v
  id : ∀ X, hom X X
  comp : ∀ {X Y Z}, hom X Y → hom Y Z → hom X Z
  id_comp : ∀ {X Y : Obj} (f : hom X Y), comp (id X) f = f
  comp_id : ∀ {X Y : Obj} (f : hom X Y), comp f (id Y) = f
  assoc :
    ∀ {W X Y Z : Obj} (f : hom W X) (g : hom X Y) (h : hom Y Z),
      comp (comp f g) h = comp f (comp g h)

namespace LocalizationTargetCategoryQ

def transportHom
    (target : LocalizationTargetCategoryQ.{u, v})
    {X X' Y Y' : target.Obj}
    (hX : X = X') (hY : Y = Y') :
    target.hom X Y → target.hom X' Y' := by
  intro f
  cases hX
  cases hY
  exact f

theorem inverse_eq_of_two_sided_inverse
    (target : LocalizationTargetCategoryQ.{u, v})
    {X Y : target.Obj}
    {f : target.hom X Y}
    {g h : target.hom Y X}
    (g_comp_f : target.comp g f = target.id Y)
    (f_comp_g : target.comp f g = target.id X)
    (h_comp_f : target.comp h f = target.id Y)
    (f_comp_h : target.comp f h = target.id X) :
    g = h := by
  have leftProof : g = h := by
    calc
      g = target.comp (target.id Y) g := by rw [target.id_comp]
      _ = target.comp (target.comp h f) g := by rw [h_comp_f]
      _ = target.comp h (target.comp f g) := by rw [target.assoc]
      _ = target.comp h (target.id X) := by rw [f_comp_g]
      _ = h := by rw [target.comp_id]
  have rightProof : g = h := by
    calc
      g = target.comp g (target.id X) := by rw [target.comp_id]
      _ = target.comp g (target.comp f h) := by rw [f_comp_h]
      _ = target.comp (target.comp g f) h := by rw [target.assoc]
      _ = target.comp (target.id Y) h := by rw [g_comp_f]
      _ = h := by rw [target.id_comp]
  exact leftProof

end LocalizationTargetCategoryQ

/-- Functor data out of bounded complexes into a target category. -/
structure BoundedComplexFunctorQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  (complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory)
  (target : LocalizationTargetCategoryQ) where
  obj : complexes.Complex → target.Obj
  map : ∀ {X Y : complexes.Complex}, complexes.hom X Y → target.hom (obj X) (obj Y)
  map_id : ∀ X : complexes.Complex, map (complexes.id X) = target.id (obj X)
  map_comp :
    ∀ {X Y Z : complexes.Complex} (f : complexes.hom X Y) (g : complexes.hom Y Z),
      map (complexes.comp f g) = target.comp (map f) (map g)

/-- Construction obligation for the localizing subcategory generated by Nisnevich descent and
`A1`-homotopy relations. -/
structure A1NisLocalizingSubcategoryQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  (complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory) where
  relation : complexes.Complex → complexes.Complex → Prop
  a1HomotopyRelation : complexes.Complex → complexes.Complex → Prop
  nisnevichDescentRelation : complexes.Complex → complexes.Complex → Prop
  A1Generator : Type u
  NisGenerator : Type u
  a1GeneratorSource : A1Generator → complexes.Complex
  a1GeneratorTarget : A1Generator → complexes.Complex
  nisGeneratorSource : NisGenerator → complexes.Complex
  nisGeneratorTarget : NisGenerator → complexes.Complex
  a1GeneratorRealizesHomotopy :
    ∀ g : A1Generator,
      a1HomotopyRelation (a1GeneratorSource g) (a1GeneratorTarget g)
  nisGeneratorRealizesDescent :
    ∀ g : NisGenerator,
      nisnevichDescentRelation (nisGeneratorSource g) (nisGeneratorTarget g)
  generatedByA1 : ∀ {X Y}, a1HomotopyRelation X Y → relation X Y
  generatedByNisnevich : ∀ {X Y}, nisnevichDescentRelation X Y → relation X Y
  stableUnderShift : Prop
  stableUnderCone : Prop
  localizingClosure : Prop

/-- Canonical A1 generator-complex realization from witness rows once the geometric objects are
realized as Wall 10A smooth schemes. -/
structure A1WitnessToBoundedComplexRealizationQ
  {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  (complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory)
  {ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v}}
  (witness : ClassicalPeriods.A1AdmissibleGeneratorWitness ctx) where
  smoothRealization :
    ClassicalPeriods.GeometricSmoothRealizationFunctorData witness.realization
  baseToCylinderCorrespondence :
    (gen : witness.row.GeneratorIndex) →
      category.Hom
        (smoothRealization.scheme (witness.row.baseIndex gen))
        (smoothRealization.scheme (witness.row.cylinderIndex gen))

namespace A1WitnessToBoundedComplexRealizationQ

def sourceComplex
    {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v}}
    {witness : ClassicalPeriods.A1AdmissibleGeneratorWitness ctx}
    (package : A1WitnessToBoundedComplexRealizationQ complexes witness)
    (gen : witness.row.GeneratorIndex) :
    complexes.Complex :=
  complexes.motiveOfSmoothScheme (package.smoothRealization.scheme (witness.row.baseIndex gen))

def targetComplex
    {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v}}
    {witness : ClassicalPeriods.A1AdmissibleGeneratorWitness ctx}
    (package : A1WitnessToBoundedComplexRealizationQ complexes witness)
    (gen : witness.row.GeneratorIndex) :
    complexes.Complex :=
  complexes.motiveOfSmoothScheme (package.smoothRealization.scheme (witness.row.cylinderIndex gen))

def generatorMap
    {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v}}
    {witness : ClassicalPeriods.A1AdmissibleGeneratorWitness ctx}
    (package : A1WitnessToBoundedComplexRealizationQ complexes witness)
    (gen : witness.row.GeneratorIndex) :
    complexes.hom (package.sourceComplex gen) (package.targetComplex gen) := by
  simpa [sourceComplex, targetComplex] using
    complexes.mapOfIntegralCorrespondence (package.baseToCylinderCorrespondence gen)

theorem sourceComplex_bounded
    {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v}}
    {witness : ClassicalPeriods.A1AdmissibleGeneratorWitness ctx}
    (package : A1WitnessToBoundedComplexRealizationQ complexes witness)
    (gen : witness.row.GeneratorIndex) :
    complexes.bounded (package.sourceComplex gen) :=
  complexes.motiveOfSmoothSchemeBounded _

theorem targetComplex_bounded
    {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v}}
    {witness : ClassicalPeriods.A1AdmissibleGeneratorWitness ctx}
    (package : A1WitnessToBoundedComplexRealizationQ complexes witness)
    (gen : witness.row.GeneratorIndex) :
    complexes.bounded (package.targetComplex gen) :=
  complexes.motiveOfSmoothSchemeBounded _

end A1WitnessToBoundedComplexRealizationQ

/-- Nis witness-row realization package.

The object-level seam is closed canonically by `smoothRealization`, so the base, patch, and
overlap motives are no longer arbitrary inputs. The Nis target complex is now derived canonically
as the cone of a supplied Mayer-Vietoris map

`M(overlap) → M(patch) ⊕ M(base)`.

What remains explicit is the typed distinguished-square morphism data. The Mayer-Vietoris map is
derived canonically from the overlap-to-patch and overlap-to-base graph correspondences. -/
structure NisWitnessToBoundedComplexRealizationQ
  {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  (complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory)
  {ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v}}
  (witness : ClassicalPeriods.NisAdmissibleGeneratorWitness ctx) where
  smoothRealization :
    ClassicalPeriods.GeometricSmoothRealizationFunctorData witness.realization
  distinguishedSquare :
    ClassicalPeriods.GeometricNisnevichDistinguishedSquareData
      smoothRealization
      witness.row.GeneratorIndex
      witness.row.baseIndex
      witness.row.patchIndex
      witness.row.overlapIndex

namespace NisWitnessToBoundedComplexRealizationQ

def baseComplex
    {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v}}
    {witness : ClassicalPeriods.NisAdmissibleGeneratorWitness ctx}
    (package : NisWitnessToBoundedComplexRealizationQ complexes witness)
    (gen : witness.row.GeneratorIndex) :
    complexes.Complex :=
  complexes.motiveOfSmoothScheme (package.smoothRealization.scheme (witness.row.baseIndex gen))

def patchComplex
    {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v}}
    {witness : ClassicalPeriods.NisAdmissibleGeneratorWitness ctx}
    (package : NisWitnessToBoundedComplexRealizationQ complexes witness)
    (gen : witness.row.GeneratorIndex) :
    complexes.Complex :=
  complexes.motiveOfSmoothScheme (package.smoothRealization.scheme (witness.row.patchIndex gen))

def overlapComplex
    {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v}}
    {witness : ClassicalPeriods.NisAdmissibleGeneratorWitness ctx}
    (package : NisWitnessToBoundedComplexRealizationQ complexes witness)
    (gen : witness.row.GeneratorIndex) :
    complexes.Complex :=
  complexes.motiveOfSmoothScheme (package.smoothRealization.scheme (witness.row.overlapIndex gen))

def sourceComplex
    {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v}}
    {witness : ClassicalPeriods.NisAdmissibleGeneratorWitness ctx}
    (package : NisWitnessToBoundedComplexRealizationQ complexes witness)
    (gen : witness.row.GeneratorIndex) :
    complexes.Complex :=
  package.baseComplex gen

def patchPlusBaseComplex
    {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v}}
    {witness : ClassicalPeriods.NisAdmissibleGeneratorWitness ctx}
    (package : NisWitnessToBoundedComplexRealizationQ complexes witness)
    (gen : witness.row.GeneratorIndex) :
    complexes.Complex :=
  complexes.directSum (package.patchComplex gen) (package.baseComplex gen)

def overlapToPatchCorrespondence
    {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v}}
    {witness : ClassicalPeriods.NisAdmissibleGeneratorWitness ctx}
    (package : NisWitnessToBoundedComplexRealizationQ complexes witness)
    (gen : witness.row.GeneratorIndex) :
    category.Hom
      (package.smoothRealization.scheme (witness.row.overlapIndex gen))
      (package.smoothRealization.scheme (witness.row.patchIndex gen)) :=
  FiniteCorrespondenceCategoryQ.ofWall10AGraph category
    (package.distinguishedSquare.overlapToPatch gen)
    (package.distinguishedSquare.overlapToPatchGraph gen)

def overlapToBaseCorrespondence
    {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v}}
    {witness : ClassicalPeriods.NisAdmissibleGeneratorWitness ctx}
    (package : NisWitnessToBoundedComplexRealizationQ complexes witness)
    (gen : witness.row.GeneratorIndex) :
    category.Hom
      (package.smoothRealization.scheme (witness.row.overlapIndex gen))
      (package.smoothRealization.scheme (witness.row.baseIndex gen)) :=
  FiniteCorrespondenceCategoryQ.ofWall10AGraph category
    (package.distinguishedSquare.overlapToBase gen)
    (package.distinguishedSquare.overlapToBaseGraph gen)

def overlapToPatchMap
    {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v}}
    {witness : ClassicalPeriods.NisAdmissibleGeneratorWitness ctx}
    (package : NisWitnessToBoundedComplexRealizationQ complexes witness)
    (gen : witness.row.GeneratorIndex) :
    complexes.hom (package.overlapComplex gen) (package.patchComplex gen) :=
  complexes.mapOfIntegralCorrespondence (package.overlapToPatchCorrespondence gen)

def overlapToBaseMap
    {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v}}
    {witness : ClassicalPeriods.NisAdmissibleGeneratorWitness ctx}
    (package : NisWitnessToBoundedComplexRealizationQ complexes witness)
    (gen : witness.row.GeneratorIndex) :
    complexes.hom (package.overlapComplex gen) (package.baseComplex gen) :=
  complexes.mapOfIntegralCorrespondence (package.overlapToBaseCorrespondence gen)

def descentMap
    {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v}}
    {witness : ClassicalPeriods.NisAdmissibleGeneratorWitness ctx}
    (package : NisWitnessToBoundedComplexRealizationQ complexes witness)
    (gen : witness.row.GeneratorIndex) :
    complexes.hom (package.overlapComplex gen) (package.patchPlusBaseComplex gen) :=
  complexes.directSumDesc
    (package.overlapToPatchMap gen)
    (package.overlapToBaseMap gen)

def targetComplex
    {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v}}
    {witness : ClassicalPeriods.NisAdmissibleGeneratorWitness ctx}
    (package : NisWitnessToBoundedComplexRealizationQ complexes witness)
    (gen : witness.row.GeneratorIndex) :
    complexes.Complex :=
  complexes.cone (package.descentMap gen)

theorem baseComplex_bounded
    {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v}}
    {witness : ClassicalPeriods.NisAdmissibleGeneratorWitness ctx}
    (package : NisWitnessToBoundedComplexRealizationQ complexes witness)
    (gen : witness.row.GeneratorIndex) :
    complexes.bounded (package.baseComplex gen) :=
  complexes.motiveOfSmoothSchemeBounded _

theorem patchComplex_bounded
    {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v}}
    {witness : ClassicalPeriods.NisAdmissibleGeneratorWitness ctx}
    (package : NisWitnessToBoundedComplexRealizationQ complexes witness)
    (gen : witness.row.GeneratorIndex) :
    complexes.bounded (package.patchComplex gen) :=
  complexes.motiveOfSmoothSchemeBounded _

theorem overlapComplex_bounded
    {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v}}
    {witness : ClassicalPeriods.NisAdmissibleGeneratorWitness ctx}
    (package : NisWitnessToBoundedComplexRealizationQ complexes witness)
    (gen : witness.row.GeneratorIndex) :
    complexes.bounded (package.overlapComplex gen) :=
  complexes.motiveOfSmoothSchemeBounded _

theorem patchPlusBaseComplex_bounded
    {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v}}
    {witness : ClassicalPeriods.NisAdmissibleGeneratorWitness ctx}
    (package : NisWitnessToBoundedComplexRealizationQ complexes witness)
    (gen : witness.row.GeneratorIndex) :
    complexes.bounded (package.patchPlusBaseComplex gen) :=
  complexes.directSumBounded
    (package.patchComplex_bounded gen)
    (package.baseComplex_bounded gen)

theorem targetComplex_bounded
    {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v}}
    {witness : ClassicalPeriods.NisAdmissibleGeneratorWitness ctx}
    (package : NisWitnessToBoundedComplexRealizationQ complexes witness)
    (gen : witness.row.GeneratorIndex) :
    complexes.bounded (package.targetComplex gen) :=
  complexes.coneBounded
    (package.descentMap gen)
    (package.overlapComplex_bounded gen)
    (package.patchPlusBaseComplex_bounded gen)

end NisWitnessToBoundedComplexRealizationQ

/-- Exact bridge still required to turn the sealed classical localization witnesses into
actual generators of the bounded-complex localizing subcategory.

The A1/Nis theorem packages already exist in the recognition lane. What remains is a transport
from those theorem targets to concrete generator families in the rational bounded-complex model. -/
structure A1NisGeneratorRealizationBridgeQ
  {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  (complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory)
  (localizing : A1NisLocalizingSubcategoryQ complexes)
  {trace : TracePresentation.{u, v, w, x, y}}
  (presentation : ClassicalMotivicPresentation trace) where
  closurePackage :
    ClassicalPeriods.PresentationAdmissibleClosureEquivalence presentation.classicalContext
  witnesses : TraceLocalizationAxiomWitnesses presentation
  a1GeneratorEquiv :
    localizing.A1Generator ≃ closurePackage.primitiveWitnesses.a1.row.GeneratorIndex
  nisGeneratorEquiv :
    localizing.NisGenerator ≃ closurePackage.primitiveWitnesses.nis.row.GeneratorIndex
  a1RowRealization :
    A1WitnessToBoundedComplexRealizationQ complexes closurePackage.primitiveWitnesses.a1
  nisRowRealization :
    NisWitnessToBoundedComplexRealizationQ complexes closurePackage.primitiveWitnesses.nis
  a1GeneratorSource_eq :
    ∀ g : localizing.A1Generator,
      localizing.a1GeneratorSource g =
        a1RowRealization.sourceComplex (a1GeneratorEquiv g)
  a1GeneratorTarget_eq :
    ∀ g : localizing.A1Generator,
      localizing.a1GeneratorTarget g =
        a1RowRealization.targetComplex (a1GeneratorEquiv g)
  nisGeneratorSource_eq :
    ∀ g : localizing.NisGenerator,
      localizing.nisGeneratorSource g =
        nisRowRealization.sourceComplex (nisGeneratorEquiv g)
  nisGeneratorTarget_eq :
    ∀ g : localizing.NisGenerator,
      localizing.nisGeneratorTarget g =
        nisRowRealization.targetComplex (nisGeneratorEquiv g)

/-- Positive package recording that the `A1`/Nis localizing generators in the bounded-complex
model are genuinely realized from the sealed classical witness rows. -/
structure A1NisGeneratorRealizationPackageQ
  {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  (complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory)
  {trace : TracePresentation.{u, v, w, x, y}}
  (presentation : ClassicalMotivicPresentation trace) where
  localizing : A1NisLocalizingSubcategoryQ complexes
  bridge : A1NisGeneratorRealizationBridgeQ complexes localizing presentation

namespace A1NisGeneratorRealizationPackageQ

def a1TheoremTarget
  {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (package : A1NisGeneratorRealizationPackageQ complexes presentation) :
    presentation.admissibleLocalizationAxioms.A1.theoremTarget :=
  package.bridge.witnesses.theoremPackage.a1_holds

def nisTheoremTarget
  {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (package : A1NisGeneratorRealizationPackageQ complexes presentation) :
    presentation.admissibleLocalizationAxioms.Nis.theoremTarget :=
  package.bridge.witnesses.theoremPackage.nis_holds

theorem theoremTargets_holds
  {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (package : A1NisGeneratorRealizationPackageQ complexes presentation) :
    presentation.admissibleLocalizationAxioms.A1.theoremTarget ∧
      presentation.admissibleLocalizationAxioms.Nis.theoremTarget := by
  exact ⟨package.a1TheoremTarget, package.nisTheoremTarget⟩

def a1SourceOfWitness
  {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (package : A1NisGeneratorRealizationPackageQ complexes presentation)
    (gen : package.bridge.closurePackage.primitiveWitnesses.a1.row.GeneratorIndex) :
    complexes.Complex :=
  package.bridge.a1RowRealization.sourceComplex gen

def a1TargetOfWitness
  {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (package : A1NisGeneratorRealizationPackageQ complexes presentation)
    (gen : package.bridge.closurePackage.primitiveWitnesses.a1.row.GeneratorIndex) :
    complexes.Complex :=
  package.bridge.a1RowRealization.targetComplex gen

def nisSourceOfWitness
  {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (package : A1NisGeneratorRealizationPackageQ complexes presentation)
    (gen : package.bridge.closurePackage.primitiveWitnesses.nis.row.GeneratorIndex) :
    complexes.Complex :=
  package.bridge.nisRowRealization.sourceComplex gen

def nisTargetOfWitness
  {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (package : A1NisGeneratorRealizationPackageQ complexes presentation)
    (gen : package.bridge.closurePackage.primitiveWitnesses.nis.row.GeneratorIndex) :
    complexes.Complex :=
  package.bridge.nisRowRealization.targetComplex gen

def nisMapSourceOfWitness
  {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (package : A1NisGeneratorRealizationPackageQ complexes presentation)
    (gen : package.bridge.closurePackage.primitiveWitnesses.nis.row.GeneratorIndex) :
    complexes.Complex :=
  package.bridge.nisRowRealization.overlapComplex gen

def nisMapTargetOfWitness
  {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (package : A1NisGeneratorRealizationPackageQ complexes presentation)
    (gen : package.bridge.closurePackage.primitiveWitnesses.nis.row.GeneratorIndex) :
    complexes.Complex :=
  package.bridge.nisRowRealization.patchPlusBaseComplex gen

def a1MapOfWitness
  {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (package : A1NisGeneratorRealizationPackageQ complexes presentation)
    (gen : package.bridge.closurePackage.primitiveWitnesses.a1.row.GeneratorIndex) :
    complexes.hom (package.a1SourceOfWitness gen) (package.a1TargetOfWitness gen) := by
  simpa [a1SourceOfWitness, a1TargetOfWitness] using
    package.bridge.a1RowRealization.generatorMap gen

def nisMapOfWitness
  {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (package : A1NisGeneratorRealizationPackageQ complexes presentation)
    (gen : package.bridge.closurePackage.primitiveWitnesses.nis.row.GeneratorIndex) :
    complexes.hom (package.nisMapSourceOfWitness gen) (package.nisMapTargetOfWitness gen) :=
  package.bridge.nisRowRealization.descentMap gen

def realizedA1Relation
  {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (package : A1NisGeneratorRealizationPackageQ complexes presentation) :
    complexes.Complex → complexes.Complex → Prop :=
  fun X Y =>
    ∃ gen : package.bridge.closurePackage.primitiveWitnesses.a1.row.GeneratorIndex,
      X = package.a1SourceOfWitness gen ∧
      Y = package.a1TargetOfWitness gen

def realizedNisRelation
  {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (package : A1NisGeneratorRealizationPackageQ complexes presentation) :
    complexes.Complex → complexes.Complex → Prop :=
  fun X Y =>
    ∃ gen : package.bridge.closurePackage.primitiveWitnesses.nis.row.GeneratorIndex,
      X = package.nisSourceOfWitness gen ∧
      Y = package.nisTargetOfWitness gen

def realizedLocalizingSubcategory
  {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (package : A1NisGeneratorRealizationPackageQ complexes presentation) :
    A1NisLocalizingSubcategoryQ complexes where
  relation := fun X Y => package.realizedA1Relation X Y ∨ package.realizedNisRelation X Y
  a1HomotopyRelation := package.realizedA1Relation
  nisnevichDescentRelation := package.realizedNisRelation
  A1Generator := package.bridge.closurePackage.primitiveWitnesses.a1.row.GeneratorIndex
  NisGenerator := package.bridge.closurePackage.primitiveWitnesses.nis.row.GeneratorIndex
  a1GeneratorSource := package.a1SourceOfWitness
  a1GeneratorTarget := package.a1TargetOfWitness
  nisGeneratorSource := package.nisSourceOfWitness
  nisGeneratorTarget := package.nisTargetOfWitness

theorem realizedLocalizing_a1GeneratorSource_eq
  {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (package : A1NisGeneratorRealizationPackageQ complexes presentation)
    (g : package.realizedLocalizingSubcategory.A1Generator) :
    package.realizedLocalizingSubcategory.a1GeneratorSource g =
      package.bridge.a1RowRealization.sourceComplex g := by
  rfl

theorem realizedLocalizing_a1GeneratorTarget_eq
  {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (package : A1NisGeneratorRealizationPackageQ complexes presentation)
    (g : package.realizedLocalizingSubcategory.A1Generator) :
    package.realizedLocalizingSubcategory.a1GeneratorTarget g =
      package.bridge.a1RowRealization.targetComplex g := by
  rfl

theorem realizedLocalizing_nisGeneratorSource_eq
  {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (package : A1NisGeneratorRealizationPackageQ complexes presentation)
    (g : package.realizedLocalizingSubcategory.NisGenerator) :
    package.realizedLocalizingSubcategory.nisGeneratorSource g =
      package.bridge.nisRowRealization.sourceComplex g := by
  rfl

theorem realizedLocalizing_nisGeneratorTarget_eq
  {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (package : A1NisGeneratorRealizationPackageQ complexes presentation)
    (g : package.realizedLocalizingSubcategory.NisGenerator) :
    package.realizedLocalizingSubcategory.nisGeneratorTarget g =
      package.bridge.nisRowRealization.targetComplex g := by
  rfl
  a1GeneratorRealizesHomotopy := by
    intro gen
    exact ⟨gen, rfl, rfl⟩
  nisGeneratorRealizesDescent := by
    intro gen
    exact ⟨gen, rfl, rfl⟩
  generatedByA1 := by
    intro X Y h
    exact Or.inl h
  generatedByNisnevich := by
    intro X Y h
    exact Or.inr h
  stableUnderShift := package.localizing.stableUnderShift
  stableUnderCone := package.localizing.stableUnderCone
  localizingClosure := package.localizing.localizingClosure

end A1NisGeneratorRealizationPackageQ

/-- Construction obligation for the quotient/localization by the `A1`/Nisnevich localizing
subcategory. -/
structure A1NisLocalizationConstruction
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  (complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory)
    (localizing : A1NisLocalizingSubcategoryQ complexes) where
  Localized : Type u
  hom : Localized → Localized → Type v
  id : ∀ X, hom X X
  comp : ∀ {X Y Z}, hom X Y → hom Y Z → hom X Z
  homRelation :
    ∀ {X Y : complexes.Complex}, complexes.hom X Y → complexes.hom X Y → Prop
  homRelation_refl :
    ∀ {X Y : complexes.Complex} (f : complexes.hom X Y), homRelation f f
  homRelation_symm :
    ∀ {X Y : complexes.Complex} {f g : complexes.hom X Y},
      homRelation f g → homRelation g f
  homRelation_trans :
    ∀ {X Y : complexes.Complex} {f g h : complexes.hom X Y},
      homRelation f g → homRelation g h → homRelation f h
  homRelation_comp_left :
    ∀ {X Y Z : complexes.Complex} {f g : complexes.hom X Y}
      (hfg : homRelation f g) (k : complexes.hom Y Z),
      homRelation (complexes.comp f k) (complexes.comp g k)
  homRelation_comp_right :
    ∀ {X Y Z : complexes.Complex} (k : complexes.hom X Y)
      {f g : complexes.hom Y Z},
      homRelation f g → homRelation (complexes.comp k f) (complexes.comp k g)
  quotient : complexes.Complex → Localized
  quotientMap :
    ∀ {X Y : complexes.Complex}, complexes.hom X Y → hom (quotient X) (quotient Y)
  quotientMap_respects :
    ∀ {X Y : complexes.Complex} {f g : complexes.hom X Y},
      homRelation f g → quotientMap f = quotientMap g
  killsLocalizingRelation : ∀ {X Y}, localizing.relation X Y → quotient X = quotient Y
  invertsA1Homotopies : ∀ {X Y}, localizing.a1HomotopyRelation X Y → quotient X = quotient Y
  enforcesNisnevichDescent :
    ∀ {X Y}, localizing.nisnevichDescentRelation X Y → quotient X = quotient Y
  quotientMap_id :
    ∀ X : complexes.Complex, quotientMap (complexes.id X) = id (quotient X)
  quotientMap_comp :
    ∀ {X Y Z : complexes.Complex} (f : complexes.hom X Y) (g : complexes.hom Y Z),
      quotientMap (complexes.comp f g) = comp (quotientMap f) (quotientMap g)
  id_comp : ∀ {X Y : Localized} (f : hom X Y), comp (id X) f = f
  comp_id : ∀ {X Y : Localized} (f : hom X Y), comp f (id Y) = f
  assoc :
    ∀ {W X Y Z : Localized} (f : hom W X) (g : hom X Y) (h : hom Y Z),
      comp (comp f g) h = comp f (comp g h)

abbrev DMgmQRaw
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {localizing : A1NisLocalizingSubcategoryQ complexes}
    (localization : A1NisLocalizationConstruction complexes localizing) : Type u :=
  localization.Localized

namespace A1NisLocalizationConstruction

def targetCategory
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  (localization : A1NisLocalizationConstruction complexes localizing) :
  LocalizationTargetCategoryQ where
  Obj := localization.Localized
  hom := localization.hom
  id := localization.id
  comp := localization.comp
  id_comp := localization.id_comp
  comp_id := localization.comp_id
  assoc := localization.assoc

def localizationFunctor
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  (localization : A1NisLocalizationConstruction complexes localizing) :
  BoundedComplexFunctorQ complexes localization.targetCategory where
  obj := localization.quotient
  map := fun f => localization.quotientMap f
  map_id := localization.quotientMap_id
  map_comp := localization.quotientMap_comp

end A1NisLocalizationConstruction

/-- Functor data out of the localized category. -/
structure LocalizedFunctorQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  (localization : A1NisLocalizationConstruction complexes localizing)
  (target : LocalizationTargetCategoryQ) where
  obj : localization.Localized → target.Obj
  map : ∀ {X Y : localization.Localized}, localization.hom X Y → target.hom (obj X) (obj Y)
  map_id : ∀ X : localization.Localized, map (localization.id X) = target.id (obj X)
  map_comp :
    ∀ {X Y Z : localization.Localized} (f : localization.hom X Y) (g : localization.hom Y Z),
      map (localization.comp f g) = target.comp (map f) (map g)

/-- Evidence that a functor out of bounded complexes identifies every chosen A1/Nis generator pair. -/
structure KillsLocalizingGeneratorsQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  (localizing : A1NisLocalizingSubcategoryQ complexes)
  {target : LocalizationTargetCategoryQ}
  (functor : BoundedComplexFunctorQ complexes target) where
  killsA1Generators :
    ∀ g : localizing.A1Generator,
      functor.obj (localizing.a1GeneratorSource g) =
        functor.obj (localizing.a1GeneratorTarget g)
  killsNisGenerators :
    ∀ g : localizing.NisGenerator,
      functor.obj (localizing.nisGeneratorSource g) =
        functor.obj (localizing.nisGeneratorTarget g)

/-- Proof-relevant factorization of a generator-killing functor through the localization functor. -/
structure LocalizationFactorizationQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  (localization : A1NisLocalizationConstruction complexes localizing)
  (target : LocalizationTargetCategoryQ)
  (sourceFunctor : BoundedComplexFunctorQ complexes target) where
  descendedFunctor : LocalizedFunctorQ localization target
  objFactorization :
    ∀ X : complexes.Complex,
      descendedFunctor.obj (localization.quotient X) = sourceFunctor.obj X
  mapFactorization :
    ∀ {X Y : complexes.Complex} (f : complexes.hom X Y),
      LocalizationTargetCategoryQ.transportHom target
        (objFactorization X) (objFactorization Y)
        (descendedFunctor.map (localization.quotientMap f)) =
          sourceFunctor.map f

/-- Proof-relevant agreement data between two factorizations of the same source functor. -/
structure LocalizationFactorizationAgreementQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localization : A1NisLocalizationConstruction complexes localizing}
  {target : LocalizationTargetCategoryQ}
  {sourceFunctor : BoundedComplexFunctorQ complexes target}
  (left right : LocalizationFactorizationQ localization target sourceFunctor) where
  objEq :
    ∀ X : localization.Localized,
      left.descendedFunctor.obj X = right.descendedFunctor.obj X
  mapEq :
    ∀ {X Y : localization.Localized} (f : localization.hom X Y),
      LocalizationTargetCategoryQ.transportHom target
        (objEq X) (objEq Y) (left.descendedFunctor.map f) =
          right.descendedFunctor.map f

namespace A1NisLocalizationConstruction

/-- Equivalence closure of the chosen localizing object relation.

The concrete localization would have to quotient objects by at least this closure before the A1/Nis
generator pairs become literally identified. -/
inductive ObjectRelationClosureQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  (localizing : A1NisLocalizingSubcategoryQ complexes) :
  complexes.Complex → complexes.Complex → Prop where
  | of_relation {X Y : complexes.Complex} :
      localizing.relation X Y → ObjectRelationClosureQ localizing X Y
  | refl (X : complexes.Complex) :
      ObjectRelationClosureQ localizing X X
  | symm {X Y : complexes.Complex} :
      ObjectRelationClosureQ localizing X Y → ObjectRelationClosureQ localizing Y X
  | trans {X Y Z : complexes.Complex} :
      ObjectRelationClosureQ localizing X Y →
      ObjectRelationClosureQ localizing Y Z →
      ObjectRelationClosureQ localizing X Z

/-- Exact missing lower package for turning the localized object quotient into a genuine category.

Quotienting homs by `homRelation` with fixed source and target objects is not enough. Once objects
are identified by the localization relation, one also needs a way to transport morphisms along that
object equivalence closure so homs between quotient objects are even well-typed. -/
structure HomTransportAlongObjectRelationQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  (localization : A1NisLocalizationConstruction complexes localizing) where
  transport :
    ∀ {X X' Y Y' : complexes.Complex},
      ObjectRelationClosureQ localizing X X' →
      ObjectRelationClosureQ localizing Y Y' →
      complexes.hom X Y → complexes.hom X' Y'
  transport_refl :
    ∀ {X Y : complexes.Complex} (f : complexes.hom X Y),
      transport (ObjectRelationClosureQ.refl X) (ObjectRelationClosureQ.refl Y) f = f
  transport_id :
    ∀ {X X' : complexes.Complex}
      (hXX' : ObjectRelationClosureQ localizing X X'),
      transport hXX' hXX' (complexes.id X) = complexes.id X'
  transport_comp :
    ∀ {X X' Y Y' Z Z' : complexes.Complex}
      (hXX' : ObjectRelationClosureQ localizing X X')
      (hYY' : ObjectRelationClosureQ localizing Y Y')
      (hZZ' : ObjectRelationClosureQ localizing Z Z')
      (f : complexes.hom X Y) (g : complexes.hom Y Z),
      transport hXX' hZZ' (complexes.comp f g) =
        complexes.comp (transport hXX' hYY' f) (transport hYY' hZZ' g)
  transport_respects_homRelation :
    ∀ {X X' Y Y' : complexes.Complex}
      (hXX' : ObjectRelationClosureQ localizing X X')
      (hYY' : ObjectRelationClosureQ localizing Y Y')
      {f g : complexes.hom X Y},
      localization.homRelation f g →
        localization.homRelation (transport hXX' hYY' f) (transport hXX' hYY' g)

/-- Additional compatibility needed before a bounded-complex functor can descend through the
concrete morphism quotient.

Generator-killing data controls object identifications coming from the localizing generators, but a
map out of the localized hom-quotient also needs the source functor to identify morphisms related
by `homRelation`. -/
def FunctorRespectsHomRelationQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  (localization : A1NisLocalizationConstruction complexes localizing)
  {target : LocalizationTargetCategoryQ}
  (sourceFunctor : BoundedComplexFunctorQ complexes target) : Prop :=
  ∀ {X Y : complexes.Complex} {f g : complexes.hom X Y},
    localization.homRelation f g → sourceFunctor.map f = sourceFunctor.map g

/-- The concrete quotient construction already factors its own localization functor through itself. -/
def selfFactorization
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  (localization : A1NisLocalizationConstruction complexes localizing) :
  LocalizationFactorizationQ
    localization localization.targetCategory localization.localizationFunctor where
  descendedFunctor :=
    { obj := fun X => X
      map := fun f => f
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl }
  objFactorization := fun _ => rfl
  mapFactorization := fun _ => rfl

/-- Exact missing quotient-elimination theorem at the quotient-on-morphisms layer.

This is the first theorem strong enough to instantiate the current proof-relevant universal
property interface once object-level morphism transport is also available. Without
`HomTransportAlongObjectRelationQ`, the localized object quotient has no well-typed homs between
its equivalence classes. -/
def quotientFunctorLiftType
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  (localization : A1NisLocalizationConstruction complexes localizing)
  (target : LocalizationTargetCategoryQ)
  (sourceFunctor : BoundedComplexFunctorQ complexes target) :=
  HomTransportAlongObjectRelationQ localization →
  (killsGenerators : KillsLocalizingGeneratorsQ localizing sourceFunctor) →
  FunctorRespectsHomRelationQ localization sourceFunctor →
    LocalizationFactorizationQ localization target sourceFunctor

/-- Exact missing uniqueness theorem corresponding to `quotientFunctorLiftType`. -/
def quotientFunctorLiftAgreementType
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  (localization : A1NisLocalizationConstruction complexes localizing)
  (target : LocalizationTargetCategoryQ)
  (sourceFunctor : BoundedComplexFunctorQ complexes target) :=
  (homTransport : HomTransportAlongObjectRelationQ localization) →
  (killsGenerators : KillsLocalizingGeneratorsQ localizing sourceFunctor) →
  (respectsHomRelation : FunctorRespectsHomRelationQ localization sourceFunctor) →
  (left right : LocalizationFactorizationQ localization target sourceFunctor) →
    LocalizationFactorizationAgreementQ left right

/-- Exact stronger datum needed for an honest localization category: actual morphisms to invert.

The current generator package only identifies source and target complexes propositionally. A roof or
zigzag localization needs explicit morphisms in the bounded-complex category whose formal inverses
generate the localization. -/
structure LocalizingMorphismPresentationQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  (localizing : A1NisLocalizingSubcategoryQ complexes) where
  a1Source : localizing.A1Generator → complexes.Complex
  a1Target : localizing.A1Generator → complexes.Complex
  a1Map : (g : localizing.A1Generator) → complexes.hom (a1Source g) (a1Target g)
  nisSource : localizing.NisGenerator → complexes.Complex
  nisTarget : localizing.NisGenerator → complexes.Complex
  nisMap : (g : localizing.NisGenerator) → complexes.hom (nisSource g) (nisTarget g)

namespace LocalizingMorphismPresentationQ

def a1Generator
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  (localizingMorphisms : LocalizingMorphismPresentationQ localizing)
  (g : localizing.A1Generator) :
  Sigma fun X => Sigma fun Y => complexes.hom X Y :=
  ⟨localizingMorphisms.a1Source g, localizingMorphisms.a1Target g, localizingMorphisms.a1Map g⟩

def nisGenerator
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  (localizingMorphisms : LocalizingMorphismPresentationQ localizing)
  (g : localizing.NisGenerator) :
  Sigma fun X => Sigma fun Y => complexes.hom X Y :=
  ⟨localizingMorphisms.nisSource g, localizingMorphisms.nisTarget g, localizingMorphisms.nisMap g⟩

end LocalizingMorphismPresentationQ

namespace A1NisGeneratorRealizationPackageQ

def localizingMorphismPresentation
  {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (package : A1NisGeneratorRealizationPackageQ complexes presentation) :
    LocalizingMorphismPresentationQ package.realizedLocalizingSubcategory where
  a1Source := package.a1SourceOfWitness
  a1Target := package.a1TargetOfWitness
  a1Map := package.a1MapOfWitness
  nisSource := package.nisMapSourceOfWitness
  nisTarget := package.nisMapTargetOfWitness
  nisMap := package.nisMapOfWitness

end A1NisGeneratorRealizationPackageQ

inductive A1NisWeakEquivalenceGeneratorFamilyQ where
  | a1
  | nis

/-- Proof-relevant generator maps whose closure is inverted by the A1/Nis localization. -/
inductive A1NisWeakEquivalenceGeneratorQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  (localizingMorphisms : LocalizingMorphismPresentationQ localizing) where
  | a1 (g : localizing.A1Generator)
  | nis (g : localizing.NisGenerator)

namespace A1NisWeakEquivalenceGeneratorQ

def family
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing} :
  A1NisWeakEquivalenceGeneratorQ localizingMorphisms →
    A1NisWeakEquivalenceGeneratorFamilyQ
  | .a1 _ => .a1
  | .nis _ => .nis

def source
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing} :
  A1NisWeakEquivalenceGeneratorQ localizingMorphisms → complexes.Complex
  | .a1 g => localizingMorphisms.a1Source g
  | .nis g => localizingMorphisms.nisSource g

def target
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing} :
  A1NisWeakEquivalenceGeneratorQ localizingMorphisms → complexes.Complex
  | .a1 g => localizingMorphisms.a1Target g
  | .nis g => localizingMorphisms.nisTarget g

def map
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  (localizingMorphisms : LocalizingMorphismPresentationQ localizing) :
  (generator : A1NisWeakEquivalenceGeneratorQ localizingMorphisms) →
    complexes.hom (source generator) (target generator)
  | .a1 g => localizingMorphisms.a1Map g
  | .nis g => localizingMorphisms.nisMap g

end A1NisWeakEquivalenceGeneratorQ

/-- Proof-relevant weak equivalences to invert in the `A1`/Nis localization.

This is the first honest closure layer above the generator maps. We close under identity and
composition only. Two-out-of-three is intentionally not assumed here; if needed later, it must be
added as a separate proved datum rather than smuggled in through a `Prop` field. -/
inductive A1NisWeakEquivalenceQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  (localizingMorphisms : LocalizingMorphismPresentationQ localizing) :
  {X Y : complexes.Complex} → complexes.hom X Y → Type (max u v) where
    | ofGenerator (generator : A1NisWeakEquivalenceGeneratorQ localizingMorphisms) :
      A1NisWeakEquivalenceQ localizingMorphisms
      (A1NisWeakEquivalenceGeneratorQ.map localizingMorphisms generator)
  | id (X : complexes.Complex) :
      A1NisWeakEquivalenceQ localizingMorphisms (complexes.id X)
  | comp
      {X Y Z : complexes.Complex}
      {f : complexes.hom X Y}
      {g : complexes.hom Y Z} :
      A1NisWeakEquivalenceQ localizingMorphisms f →
      A1NisWeakEquivalenceQ localizingMorphisms g →
      A1NisWeakEquivalenceQ localizingMorphisms (complexes.comp f g)

/-- Explicit later saturation obligation if the localization needs a saturated weak-equivalence
class. This is recorded, not assumed. -/
def A1NisWeakEquivalenceTwoOutOfThreeTargetQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  (localizingMorphisms : LocalizingMorphismPresentationQ localizing) : Type (max u v) :=
  ∀ {X Y Z : complexes.Complex}
    {f : complexes.hom X Y}
    {g : complexes.hom Y Z},
    A1NisWeakEquivalenceQ localizingMorphisms f →
    A1NisWeakEquivalenceQ localizingMorphisms (complexes.comp f g) →
    A1NisWeakEquivalenceQ localizingMorphisms g

/-- One step in the raw zigzag localization category.

Forward steps are ordinary bounded-complex morphisms. Backward steps are formal inverses of
proof-relevant A1/Nis weak equivalences. -/
inductive ZigzagStepQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  (localizingMorphisms : LocalizingMorphismPresentationQ localizing) :
  complexes.Complex → complexes.Complex → Type (max u v) where
  | forward {X Y : complexes.Complex} :
      complexes.hom X Y → ZigzagStepQ localizingMorphisms X Y
  | backward {X Y : complexes.Complex} (f : complexes.hom Y X) :
      A1NisWeakEquivalenceQ localizingMorphisms f →
      ZigzagStepQ localizingMorphisms X Y

/-- Raw A1/Nis zigzags generated by ordinary morphisms and formal inverses of chosen weak
equivalences.

This keeps the original objects and avoids the overly strong requirement that localization identify
objects by equality. -/
inductive A1NisZigzagQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  (localizingMorphisms : LocalizingMorphismPresentationQ localizing) :
  complexes.Complex → complexes.Complex → Type (max u v) where
  | nil (X : complexes.Complex) : A1NisZigzagQ localizingMorphisms X X
  | cons {X Y Z : complexes.Complex} :
      ZigzagStepQ localizingMorphisms X Y →
      A1NisZigzagQ localizingMorphisms Y Z →
      A1NisZigzagQ localizingMorphisms X Z

namespace A1NisZigzagQ

def id
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  (X : complexes.Complex) :
  A1NisZigzagQ localizingMorphisms X X :=
  .nil X

def comp
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {X Y Z : complexes.Complex} :
  A1NisZigzagQ localizingMorphisms X Y →
  A1NisZigzagQ localizingMorphisms Y Z →
  A1NisZigzagQ localizingMorphisms X Z
  | .nil _, g => g
  | .cons step tail, g => .cons step (comp tail g)

def ofForward
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {X Y : complexes.Complex}
  (f : complexes.hom X Y) :
  A1NisZigzagQ localizingMorphisms X Y :=
  .cons (.forward f) (.nil Y)

def ofBackward
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {X Y : complexes.Complex}
  (f : complexes.hom Y X)
  (hf : A1NisWeakEquivalenceQ localizingMorphisms f) :
  A1NisZigzagQ localizingMorphisms X Y :=
  .cons (.backward f hf) (.nil _)

@[simp] theorem id_comp
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {X Y : complexes.Complex}
  (f : A1NisZigzagQ localizingMorphisms X Y) :
  comp (id X) f = f := rfl

@[simp] theorem comp_id
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {X Y : complexes.Complex}
  (f : A1NisZigzagQ localizingMorphisms X Y) :
  comp f (id Y) = f := by
  induction f with
  | nil _ => rfl
  | cons _ tail ih => simp [comp, ih]

@[simp] theorem assoc
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {W X Y Z : complexes.Complex}
  (f : A1NisZigzagQ localizingMorphisms W X)
  (g : A1NisZigzagQ localizingMorphisms X Y)
  (h : A1NisZigzagQ localizingMorphisms Y Z) :
  comp (comp f g) h = comp f (comp g h) := by
  induction f with
  | nil _ => rfl
  | cons _ tail ih => simp [comp, ih]

end A1NisZigzagQ

/-- Generated equivalence relation on raw A1/Nis zigzags.

This is intentionally the strongest honest relation currently supported by the file: equivalence
closure, congruence under concatenation, ordinary forward-map category rewrites, and cancellation
of a weak equivalence against its formal inverse. No calculus-of-fractions or common-refinement law
is assumed here. -/
inductive A1NisZigzagEquivalentQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing} :
  {X Y : complexes.Complex} →
  A1NisZigzagQ localizingMorphisms X Y →
    A1NisZigzagQ localizingMorphisms X Y → Prop where
  | ofEq {X Y : complexes.Complex} {left right : A1NisZigzagQ localizingMorphisms X Y} :
      left = right → A1NisZigzagEquivalentQ left right
  | refl {X Y : complexes.Complex} (zigzag : A1NisZigzagQ localizingMorphisms X Y) :
      A1NisZigzagEquivalentQ zigzag zigzag
  | symm {X Y : complexes.Complex} {left right : A1NisZigzagQ localizingMorphisms X Y} :
      A1NisZigzagEquivalentQ left right → A1NisZigzagEquivalentQ right left
  | trans {X Y : complexes.Complex}
      {left middle right : A1NisZigzagQ localizingMorphisms X Y} :
      A1NisZigzagEquivalentQ left middle →
      A1NisZigzagEquivalentQ middle right →
      A1NisZigzagEquivalentQ left right
  | comp_left
      {X Y : complexes.Complex}
      {Z : complexes.Complex}
      {left left' : A1NisZigzagQ localizingMorphisms X Y}
      {right : A1NisZigzagQ localizingMorphisms Y Z} :
      A1NisZigzagEquivalentQ left left' →
      A1NisZigzagEquivalentQ
        (A1NisZigzagQ.comp left right)
        (A1NisZigzagQ.comp left' right)
  | comp_right
      {W : complexes.Complex}
      {X Y : complexes.Complex}
      {left : A1NisZigzagQ localizingMorphisms W X}
      {right right' : A1NisZigzagQ localizingMorphisms X Y} :
      A1NisZigzagEquivalentQ right right' →
      A1NisZigzagEquivalentQ
        (A1NisZigzagQ.comp left right)
        (A1NisZigzagQ.comp left right')
  | forward_id (X : complexes.Complex) :
      A1NisZigzagEquivalentQ
        (A1NisZigzagQ.ofForward (localizingMorphisms := localizingMorphisms) (complexes.id X))
        (A1NisZigzagQ.id X)
  | forward_comp
      {X Y Z : complexes.Complex}
      (f : complexes.hom X Y)
      (g : complexes.hom Y Z) :
      A1NisZigzagEquivalentQ
        (A1NisZigzagQ.comp
          (A1NisZigzagQ.ofForward (localizingMorphisms := localizingMorphisms) f)
          (A1NisZigzagQ.ofForward (localizingMorphisms := localizingMorphisms) g))
        (A1NisZigzagQ.ofForward (localizingMorphisms := localizingMorphisms) (complexes.comp f g))
  | backward_forward_cancel
      {X Y : complexes.Complex}
      (f : complexes.hom Y X)
      (hf : A1NisWeakEquivalenceQ localizingMorphisms f) :
      A1NisZigzagEquivalentQ
        (A1NisZigzagQ.comp
          (A1NisZigzagQ.ofBackward (localizingMorphisms := localizingMorphisms) f hf)
          (A1NisZigzagQ.ofForward (localizingMorphisms := localizingMorphisms) f))
        (A1NisZigzagQ.id X)
  | forward_backward_cancel
      {X Y : complexes.Complex}
      (f : complexes.hom Y X)
      (hf : A1NisWeakEquivalenceQ localizingMorphisms f) :
      A1NisZigzagEquivalentQ
        (A1NisZigzagQ.comp
          (A1NisZigzagQ.ofForward (localizingMorphisms := localizingMorphisms) f)
          (A1NisZigzagQ.ofBackward (localizingMorphisms := localizingMorphisms) f hf))
        (A1NisZigzagQ.id Y)

namespace A1NisZigzagEquivalentQ

theorem comp_congr
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {W X Y : complexes.Complex}
  {left left' : A1NisZigzagQ localizingMorphisms W X}
  {right right' : A1NisZigzagQ localizingMorphisms X Y} :
  A1NisZigzagEquivalentQ left left' →
  A1NisZigzagEquivalentQ right right' →
  A1NisZigzagEquivalentQ
    (A1NisZigzagQ.comp left right)
    (A1NisZigzagQ.comp left' right') := by
  intro hLeft hRight
  exact
    A1NisZigzagEquivalentQ.trans
    (A1NisZigzagEquivalentQ.comp_left hLeft)
    (A1NisZigzagEquivalentQ.comp_right hRight)

def setoid
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  (localizingMorphisms : LocalizingMorphismPresentationQ localizing)
  (X Y : complexes.Complex) :
  Setoid (A1NisZigzagQ localizingMorphisms X Y) where
  r := fun left right => A1NisZigzagEquivalentQ left right
  iseqv :=
    { refl := fun left => A1NisZigzagEquivalentQ.refl left
      symm := fun h => A1NisZigzagEquivalentQ.symm h
      trans := fun h1 h2 => A1NisZigzagEquivalentQ.trans h1 h2 }

end A1NisZigzagEquivalentQ

def A1NisLocalizedHomQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  (localizingMorphisms : LocalizingMorphismPresentationQ localizing)
  (X Y : complexes.Complex) : Type (max u v) :=
  Quotient (A1NisZigzagEquivalentQ.setoid localizingMorphisms X Y)

namespace A1NisLocalizedHomQ

def id
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  (localizingMorphisms : LocalizingMorphismPresentationQ localizing)
  (X : complexes.Complex) :
  A1NisLocalizedHomQ localizingMorphisms X X :=
  Quotient.mk _ (A1NisZigzagQ.id X)

def comp
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  (localizingMorphisms : LocalizingMorphismPresentationQ localizing)
  {X Y Z : complexes.Complex} :
  A1NisLocalizedHomQ localizingMorphisms X Y →
  A1NisLocalizedHomQ localizingMorphisms Y Z →
  A1NisLocalizedHomQ localizingMorphisms X Z := by
  intro left right
  refine Quotient.liftOn₂ left right
    (fun rawLeft rawRight => Quotient.mk _ (A1NisZigzagQ.comp rawLeft rawRight)) ?_
  intro rawLeft rawRight rawLeft' rawRight' hLeft hRight
  apply Quotient.sound
  exact
    A1NisZigzagEquivalentQ.trans
      (A1NisZigzagEquivalentQ.comp_left hLeft)
      (A1NisZigzagEquivalentQ.comp_right hRight)

def ofForward
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  (localizingMorphisms : LocalizingMorphismPresentationQ localizing)
  {X Y : complexes.Complex}
  (f : complexes.hom X Y) :
  A1NisLocalizedHomQ localizingMorphisms X Y :=
  Quotient.mk _ (A1NisZigzagQ.ofForward (localizingMorphisms := localizingMorphisms) f)

def ofBackward
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  (localizingMorphisms : LocalizingMorphismPresentationQ localizing)
  {X Y : complexes.Complex}
  (f : complexes.hom Y X)
  (hf : A1NisWeakEquivalenceQ localizingMorphisms f) :
  A1NisLocalizedHomQ localizingMorphisms X Y :=
  Quotient.mk _ (A1NisZigzagQ.ofBackward (localizingMorphisms := localizingMorphisms) f hf)

@[simp] theorem id_comp
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  (localizingMorphisms : LocalizingMorphismPresentationQ localizing)
  {X Y : complexes.Complex}
  (f : A1NisLocalizedHomQ localizingMorphisms X Y) :
  comp localizingMorphisms (id localizingMorphisms X) f = f := by
  refine Quotient.inductionOn f ?_
  intro raw
  simp [A1NisLocalizedHomQ.comp, A1NisLocalizedHomQ.id]

@[simp] theorem comp_id
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  (localizingMorphisms : LocalizingMorphismPresentationQ localizing)
  {X Y : complexes.Complex}
  (f : A1NisLocalizedHomQ localizingMorphisms X Y) :
  comp localizingMorphisms f (id localizingMorphisms Y) = f := by
  refine Quotient.inductionOn f ?_
  intro raw
  simp [A1NisLocalizedHomQ.comp, A1NisLocalizedHomQ.id]

@[simp] theorem assoc
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  (localizingMorphisms : LocalizingMorphismPresentationQ localizing)
  {W X Y Z : complexes.Complex}
  (f : A1NisLocalizedHomQ localizingMorphisms W X)
  (g : A1NisLocalizedHomQ localizingMorphisms X Y)
  (h : A1NisLocalizedHomQ localizingMorphisms Y Z) :
  comp localizingMorphisms (comp localizingMorphisms f g) h =
    comp localizingMorphisms f (comp localizingMorphisms g h) := by
  refine Quotient.inductionOn₃ f g h ?_
  intro rawF rawG rawH
  simp [A1NisLocalizedHomQ.comp]

@[simp] theorem ofForward_id
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  (localizingMorphisms : LocalizingMorphismPresentationQ localizing)
  (X : complexes.Complex) :
  ofForward localizingMorphisms (complexes.id X) = id localizingMorphisms X := by
  change
    Quotient.mk (A1NisZigzagEquivalentQ.setoid localizingMorphisms X X)
        (A1NisZigzagQ.ofForward (localizingMorphisms := localizingMorphisms) (complexes.id X)) =
      Quotient.mk (A1NisZigzagEquivalentQ.setoid localizingMorphisms X X)
        (A1NisZigzagQ.id X)
  exact Quotient.sound (A1NisZigzagEquivalentQ.forward_id X)

@[simp] theorem ofForward_comp
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  (localizingMorphisms : LocalizingMorphismPresentationQ localizing)
  {X Y Z : complexes.Complex}
  (f : complexes.hom X Y)
  (g : complexes.hom Y Z) :
  ofForward localizingMorphisms (complexes.comp f g) =
    comp localizingMorphisms (ofForward localizingMorphisms f) (ofForward localizingMorphisms g) := by
  simp [A1NisLocalizedHomQ.comp, A1NisLocalizedHomQ.ofForward]
  apply Quotient.sound
  change
    A1NisZigzagEquivalentQ
      (A1NisZigzagQ.ofForward (localizingMorphisms := localizingMorphisms) (complexes.comp f g))
      (A1NisZigzagQ.comp
        (A1NisZigzagQ.ofForward (localizingMorphisms := localizingMorphisms) f)
        (A1NisZigzagQ.ofForward (localizingMorphisms := localizingMorphisms) g))
  exact A1NisZigzagEquivalentQ.symm (A1NisZigzagEquivalentQ.forward_comp f g)

@[simp] theorem backward_comp_forward
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  (localizingMorphisms : LocalizingMorphismPresentationQ localizing)
  {X Y : complexes.Complex}
  (f : complexes.hom Y X)
  (hf : A1NisWeakEquivalenceQ localizingMorphisms f) :
  comp localizingMorphisms
      (ofBackward localizingMorphisms f hf)
      (ofForward localizingMorphisms f) =
    id localizingMorphisms X := by
  change
    Quotient.mk (A1NisZigzagEquivalentQ.setoid localizingMorphisms X X)
      (A1NisZigzagQ.comp
        (A1NisZigzagQ.ofBackward (localizingMorphisms := localizingMorphisms) f hf)
        (A1NisZigzagQ.ofForward (localizingMorphisms := localizingMorphisms) f)) =
    Quotient.mk (A1NisZigzagEquivalentQ.setoid localizingMorphisms X X)
      (A1NisZigzagQ.id X)
  exact Quotient.sound (A1NisZigzagEquivalentQ.backward_forward_cancel f hf)

@[simp] theorem forward_comp_backward
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  (localizingMorphisms : LocalizingMorphismPresentationQ localizing)
  {X Y : complexes.Complex}
  (f : complexes.hom Y X)
  (hf : A1NisWeakEquivalenceQ localizingMorphisms f) :
  comp localizingMorphisms
      (ofForward localizingMorphisms f)
      (ofBackward localizingMorphisms f hf) =
    id localizingMorphisms Y := by
  change
    Quotient.mk (A1NisZigzagEquivalentQ.setoid localizingMorphisms Y Y)
      (A1NisZigzagQ.comp
        (A1NisZigzagQ.ofForward (localizingMorphisms := localizingMorphisms) f)
        (A1NisZigzagQ.ofBackward (localizingMorphisms := localizingMorphisms) f hf)) =
    Quotient.mk (A1NisZigzagEquivalentQ.setoid localizingMorphisms Y Y)
      (A1NisZigzagQ.id Y)
  exact Quotient.sound (A1NisZigzagEquivalentQ.forward_backward_cancel f hf)

end A1NisLocalizedHomQ

abbrev ZigzagHomQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  (localizingMorphisms : LocalizingMorphismPresentationQ localizing) :=
  A1NisZigzagQ localizingMorphisms

/-- Honest fallback localization shape if object transport is too strong: keep the original objects
and localize by zigzag-equivalence classes.

This is the correct categorical direction once A1/Nis localization is understood as inverting a
class of morphisms rather than quotienting objects by equality. -/
structure ZigzagLocalizationConstructionQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  (complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory)
  (localizing : A1NisLocalizingSubcategoryQ complexes)
  (localizingMorphisms : LocalizingMorphismPresentationQ localizing) where
  hom : complexes.Complex → complexes.Complex → Type (max u v)
  id : ∀ X : complexes.Complex, hom X X
  comp : ∀ {X Y Z : complexes.Complex}, hom X Y → hom Y Z → hom X Z
  quotientObj : complexes.Complex → complexes.Complex
  quotientMap : ∀ {X Y : complexes.Complex}, complexes.hom X Y → hom X Y
  id_comp : ∀ {X Y : complexes.Complex} (f : hom X Y), comp (id X) f = f
  comp_id : ∀ {X Y : complexes.Complex} (f : hom X Y), comp f (id Y) = f
  assoc :
    ∀ {W X Y Z : complexes.Complex} (f : hom W X) (g : hom X Y) (h : hom Y Z),
      comp (comp f g) h = comp f (comp g h)

namespace ZigzagLocalizationConstructionQ

def targetCategory
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  (localizingMorphisms : LocalizingMorphismPresentationQ localizing) :
  LocalizationTargetCategoryQ where
  Obj := complexes.Complex
  hom := A1NisLocalizedHomQ localizingMorphisms
  id := A1NisLocalizedHomQ.id localizingMorphisms
  comp := A1NisLocalizedHomQ.comp localizingMorphisms
  id_comp := A1NisLocalizedHomQ.id_comp localizingMorphisms
  comp_id := A1NisLocalizedHomQ.comp_id localizingMorphisms
  assoc := A1NisLocalizedHomQ.assoc localizingMorphisms

def localizationFunctor
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  (localizingMorphisms : LocalizingMorphismPresentationQ localizing) :
  BoundedComplexFunctorQ complexes (targetCategory localizingMorphisms) where
  obj := fun X => X
  map := fun f => A1NisLocalizedHomQ.ofForward localizingMorphisms f
  map_id := A1NisLocalizedHomQ.ofForward_id localizingMorphisms
  map_comp := A1NisLocalizedHomQ.ofForward_comp localizingMorphisms

structure A1NisWeakEquivalencesInvertInLocalizationQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  (localizingMorphisms : LocalizingMorphismPresentationQ localizing) where
  inverse :
    ∀ {X Y : complexes.Complex} {f : complexes.hom Y X},
      A1NisWeakEquivalenceQ localizingMorphisms f →
        A1NisLocalizedHomQ localizingMorphisms X Y
  inverse_comp_forward :
    ∀ {X Y : complexes.Complex} {f : complexes.hom Y X}
      (hf : A1NisWeakEquivalenceQ localizingMorphisms f),
      A1NisLocalizedHomQ.comp localizingMorphisms (inverse hf)
        (A1NisLocalizedHomQ.ofForward localizingMorphisms f) =
          A1NisLocalizedHomQ.id localizingMorphisms X
  forward_comp_inverse :
    ∀ {X Y : complexes.Complex} {f : complexes.hom Y X}
      (hf : A1NisWeakEquivalenceQ localizingMorphisms f),
      A1NisLocalizedHomQ.comp localizingMorphisms
        (A1NisLocalizedHomQ.ofForward localizingMorphisms f) (inverse hf) =
          A1NisLocalizedHomQ.id localizingMorphisms Y

def weakEquivalencesInvert
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  (localizingMorphisms : LocalizingMorphismPresentationQ localizing) :
  A1NisWeakEquivalencesInvertInLocalizationQ localizingMorphisms where
  inverse := fun hf => A1NisLocalizedHomQ.ofBackward localizingMorphisms _ hf
  inverse_comp_forward := by
    intro X Y f hf
    exact A1NisLocalizedHomQ.backward_comp_forward localizingMorphisms f hf
  forward_comp_inverse := by
    intro X Y f hf
    exact A1NisLocalizedHomQ.forward_comp_backward localizingMorphisms f hf

structure FunctorInvertsA1NisWeakEquivalencesQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  (localizingMorphisms : LocalizingMorphismPresentationQ localizing)
  {target : LocalizationTargetCategoryQ}
  (sourceFunctor : BoundedComplexFunctorQ complexes target) where
  inverse :
    ∀ {X Y : complexes.Complex} {f : complexes.hom Y X},
      A1NisWeakEquivalenceQ localizingMorphisms f →
        target.hom (sourceFunctor.obj X) (sourceFunctor.obj Y)
  inverse_comp_forward :
    ∀ {X Y : complexes.Complex} {f : complexes.hom Y X}
      (hf : A1NisWeakEquivalenceQ localizingMorphisms f),
      target.comp (inverse hf) (sourceFunctor.map f) = target.id (sourceFunctor.obj X)
  forward_comp_inverse :
    ∀ {X Y : complexes.Complex} {f : complexes.hom Y X}
      (hf : A1NisWeakEquivalenceQ localizingMorphisms f),
      target.comp (sourceFunctor.map f) (inverse hf) = target.id (sourceFunctor.obj Y)

def interpretStep
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {target : LocalizationTargetCategoryQ}
  {sourceFunctor : BoundedComplexFunctorQ complexes target}
  {X Y : complexes.Complex}
  (inverts : FunctorInvertsA1NisWeakEquivalencesQ localizingMorphisms sourceFunctor) :
  ZigzagStepQ localizingMorphisms X Y → target.hom (sourceFunctor.obj X) (sourceFunctor.obj Y)
  | .forward f => sourceFunctor.map f
  | .backward f hf => inverts.inverse hf

def interpretZigzag
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {target : LocalizationTargetCategoryQ}
  {sourceFunctor : BoundedComplexFunctorQ complexes target}
  {X Y : complexes.Complex}
  (inverts : FunctorInvertsA1NisWeakEquivalencesQ localizingMorphisms sourceFunctor) :
  A1NisZigzagQ localizingMorphisms X Y → target.hom (sourceFunctor.obj X) (sourceFunctor.obj Y)
  | .nil X => target.id (sourceFunctor.obj X)
  | .cons step tail =>
      target.comp (interpretStep (localizingMorphisms := localizingMorphisms) inverts step)
        (interpretZigzag (localizingMorphisms := localizingMorphisms) inverts tail)

@[simp] theorem interpret_comp
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {target : LocalizationTargetCategoryQ}
  {sourceFunctor : BoundedComplexFunctorQ complexes target}
  {X Y Z : complexes.Complex}
  (inverts : FunctorInvertsA1NisWeakEquivalencesQ localizingMorphisms sourceFunctor)
  (left : A1NisZigzagQ localizingMorphisms X Y)
  (right : A1NisZigzagQ localizingMorphisms Y Z) :
  interpretZigzag (localizingMorphisms := localizingMorphisms) inverts (A1NisZigzagQ.comp left right) =
    target.comp
      (interpretZigzag (localizingMorphisms := localizingMorphisms) inverts left)
      (interpretZigzag (localizingMorphisms := localizingMorphisms) inverts right) := by
  induction left with
  | nil _ =>
      simp [A1NisZigzagQ.comp, interpretZigzag]
      exact (target.id_comp _).symm
  | cons step tail ih =>
      simp [A1NisZigzagQ.comp, interpretZigzag, ih]
      exact (target.assoc _ _ _).symm

theorem interpret_equivalent
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {target : LocalizationTargetCategoryQ}
  {sourceFunctor : BoundedComplexFunctorQ complexes target}
  {X Y : complexes.Complex}
  (inverts : FunctorInvertsA1NisWeakEquivalencesQ localizingMorphisms sourceFunctor)
  {left right : A1NisZigzagQ localizingMorphisms X Y} :
  A1NisZigzagEquivalentQ left right →
    interpretZigzag (localizingMorphisms := localizingMorphisms) inverts left =
      interpretZigzag (localizingMorphisms := localizingMorphisms) inverts right := by
  intro h
  induction h with
  | ofEq hEq => cases hEq; rfl
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | comp_left h ih =>
      simp [interpret_comp]
      exact congrArg (fun morphism => target.comp morphism _) ih
  | comp_right h ih =>
      simp [interpret_comp]
      exact congrArg (fun morphism => target.comp _ morphism) ih
  | forward_id X =>
      simp [A1NisZigzagQ.ofForward, interpretZigzag, interpretStep]
      rw [target.comp_id]
      exact sourceFunctor.map_id X
  | forward_comp f g =>
      simp [A1NisZigzagQ.ofForward, interpretZigzag, interpretStep]
      rw [target.comp_id, target.comp_id]
      exact (sourceFunctor.map_comp f g).symm
  | backward_forward_cancel f hf =>
      rw [interpret_comp]
      simp [A1NisZigzagQ.ofBackward, A1NisZigzagQ.ofForward, interpretZigzag, interpretStep]
      rw [target.comp_id, target.comp_id]
      exact inverts.inverse_comp_forward hf
  | forward_backward_cancel f hf =>
      rw [interpret_comp]
      simp [A1NisZigzagQ.ofBackward, A1NisZigzagQ.ofForward, interpretZigzag, interpretStep]
      rw [target.comp_id, target.comp_id]
      exact inverts.forward_comp_inverse hf

structure ZigzagLocalizationFactorizationQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  (localizingMorphisms : LocalizingMorphismPresentationQ localizing)
  (target : LocalizationTargetCategoryQ)
  (sourceFunctor : BoundedComplexFunctorQ complexes target) where
  map : ∀ {X Y : complexes.Complex}, A1NisLocalizedHomQ localizingMorphisms X Y →
    target.hom (sourceFunctor.obj X) (sourceFunctor.obj Y)
  map_id :
    ∀ X : complexes.Complex,
      map (A1NisLocalizedHomQ.id localizingMorphisms X) = target.id (sourceFunctor.obj X)
  map_comp :
    ∀ {X Y Z : complexes.Complex}
      (f : A1NisLocalizedHomQ localizingMorphisms X Y)
      (g : A1NisLocalizedHomQ localizingMorphisms Y Z),
      map (A1NisLocalizedHomQ.comp localizingMorphisms f g) =
        target.comp (map f) (map g)
  map_ofForward :
    ∀ {X Y : complexes.Complex} (f : complexes.hom X Y),
      map (A1NisLocalizedHomQ.ofForward localizingMorphisms f) = sourceFunctor.map f

/-- Agreement between two quotient-zigzag factorizations of the same source functor. -/
structure ZigzagLocalizationFactorizationAgreementQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  (localizingMorphisms : LocalizingMorphismPresentationQ localizing)
  {target : LocalizationTargetCategoryQ}
  {sourceFunctor : BoundedComplexFunctorQ complexes target}
  (left right : ZigzagLocalizationFactorizationQ localizingMorphisms target sourceFunctor) where
  mapEq :
    ∀ {X Y : complexes.Complex} (f : A1NisLocalizedHomQ localizingMorphisms X Y),
      left.map f = right.map f

def descendInvertingFunctor
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  (localizingMorphisms : LocalizingMorphismPresentationQ localizing)
  (target : LocalizationTargetCategoryQ)
  (sourceFunctor : BoundedComplexFunctorQ complexes target)
  (inverts : FunctorInvertsA1NisWeakEquivalencesQ localizingMorphisms sourceFunctor) :
  ZigzagLocalizationFactorizationQ localizingMorphisms target sourceFunctor where
  map := by
    intro X Y
    refine Quotient.lift ?_ ?_
    · intro raw
      exact interpretZigzag (localizingMorphisms := localizingMorphisms) inverts raw
    · intro left right h
      exact interpret_equivalent (localizingMorphisms := localizingMorphisms) inverts h
  map_id := by
    intro X
    rfl
  map_comp := by
    intro X Y Z f g
    refine Quotient.inductionOn₂ f g ?_
    intro rawF rawG
    exact interpret_comp (localizingMorphisms := localizingMorphisms) inverts rawF rawG
  map_ofForward := by
    intro X Y f
    simp [A1NisLocalizedHomQ.ofForward, interpretZigzag, interpretStep, target.comp_id]

/-- The inverse-choice independence needed for quotient-zigzag descent holds in every target
category, because two-sided inverses are unique by associativity and unit laws alone. -/
theorem inverseChoiceIndependenceTargetQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {_localizing : A1NisLocalizingSubcategoryQ complexes}
  (target : LocalizationTargetCategoryQ)
  (sourceFunctor : BoundedComplexFunctorQ complexes target) :
  ∀ {X Y : complexes.Complex} {f : complexes.hom Y X}
    (left right : target.hom (sourceFunctor.obj X) (sourceFunctor.obj Y)),
    target.comp left (sourceFunctor.map f) = target.id (sourceFunctor.obj X) →
    target.comp (sourceFunctor.map f) left = target.id (sourceFunctor.obj Y) →
    target.comp right (sourceFunctor.map f) = target.id (sourceFunctor.obj X) →
    target.comp (sourceFunctor.map f) right = target.id (sourceFunctor.obj Y) →
      left = right := by
  intro X Y f left right left_comp_forward forward_comp_left right_comp_forward forward_comp_right
  exact LocalizationTargetCategoryQ.inverse_eq_of_two_sided_inverse target
    left_comp_forward forward_comp_left right_comp_forward forward_comp_right

/-- Any two inversion packages interpret each backward weak-equivalence step in the same way. -/
theorem interpretStep_inverseChoiceIndependent
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {target : LocalizationTargetCategoryQ}
  {sourceFunctor : BoundedComplexFunctorQ complexes target}
  (leftInverts rightInverts : FunctorInvertsA1NisWeakEquivalencesQ localizingMorphisms sourceFunctor)
  {X Y : complexes.Complex}
  (step : ZigzagStepQ localizingMorphisms X Y) :
  interpretStep (localizingMorphisms := localizingMorphisms) leftInverts step =
    interpretStep (localizingMorphisms := localizingMorphisms) rightInverts step := by
  cases step with
  | forward f => rfl
  | backward f hf =>
      exact inverseChoiceIndependenceTargetQ
        (_localizing := localizing) target sourceFunctor
        (leftInverts.inverse hf) (rightInverts.inverse hf)
        (leftInverts.inverse_comp_forward hf)
        (leftInverts.forward_comp_inverse hf)
        (rightInverts.inverse_comp_forward hf)
        (rightInverts.forward_comp_inverse hf)

/-- The interpretation of a quotient-zigzag class is independent of the chosen inverse package
whenever the target category has unique two-sided inverses. -/
theorem interpretZigzag_inverseChoiceIndependent
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {target : LocalizationTargetCategoryQ}
  {sourceFunctor : BoundedComplexFunctorQ complexes target}
  (leftInverts rightInverts : FunctorInvertsA1NisWeakEquivalencesQ localizingMorphisms sourceFunctor)
  {X Y : complexes.Complex}
  (zigzag : A1NisZigzagQ localizingMorphisms X Y) :
  interpretZigzag (localizingMorphisms := localizingMorphisms) leftInverts zigzag =
    interpretZigzag (localizingMorphisms := localizingMorphisms) rightInverts zigzag := by
  induction zigzag with
  | nil _ => rfl
  | cons step tail ih =>
      rw [interpretZigzag, interpretZigzag]
      rw [interpretStep_inverseChoiceIndependent
        (localizingMorphisms := localizingMorphisms)
        (sourceFunctor := sourceFunctor)
        leftInverts rightInverts step]
      rw [ih]

/-- Quotient-zigzag descent is independent of the chosen inverse package as soon as the target
category has unique two-sided inverses. Since the localization keeps the original objects, map-level
agreement is the full uniqueness content of this concrete factorization surface. -/
theorem descendInvertingFunctor_map_eq
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {target : LocalizationTargetCategoryQ}
  {sourceFunctor : BoundedComplexFunctorQ complexes target}
  (leftInverts rightInverts : FunctorInvertsA1NisWeakEquivalencesQ localizingMorphisms sourceFunctor)
  {X Y : complexes.Complex}
  (f : A1NisLocalizedHomQ localizingMorphisms X Y) :
  (descendInvertingFunctor localizingMorphisms target sourceFunctor leftInverts).map f =
    (descendInvertingFunctor localizingMorphisms target sourceFunctor rightInverts).map f := by
  refine Quotient.inductionOn f ?_
  intro raw
  exact interpretZigzag_inverseChoiceIndependent
    (localizingMorphisms := localizingMorphisms)
    (sourceFunctor := sourceFunctor)
    leftInverts rightInverts raw

def descendInvertingFunctor_agreement
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  (localizingMorphisms : LocalizingMorphismPresentationQ localizing)
  (target : LocalizationTargetCategoryQ)
  (sourceFunctor : BoundedComplexFunctorQ complexes target)
  (leftInverts rightInverts : FunctorInvertsA1NisWeakEquivalencesQ localizingMorphisms sourceFunctor) :
  ZigzagLocalizationFactorizationAgreementQ localizingMorphisms
    (descendInvertingFunctor localizingMorphisms target sourceFunctor leftInverts)
    (descendInvertingFunctor localizingMorphisms target sourceFunctor rightInverts) where
  mapEq := by
    intro X Y f
    exact descendInvertingFunctor_map_eq
      (localizingMorphisms := localizingMorphisms)
      (target := target)
      (sourceFunctor := sourceFunctor)
      leftInverts rightInverts f

def ofLocalizingMorphisms
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  (localizingMorphisms : LocalizingMorphismPresentationQ localizing) :
  ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms where
  hom := A1NisLocalizedHomQ localizingMorphisms
  id := fun X => A1NisLocalizedHomQ.id localizingMorphisms X
  comp := fun {X Y Z} f g => A1NisLocalizedHomQ.comp localizingMorphisms f g
  quotientObj := fun X => X
  quotientMap := fun f => A1NisLocalizedHomQ.ofForward localizingMorphisms f
  id_comp := by
    intro X Y f
    exact A1NisLocalizedHomQ.id_comp localizingMorphisms f
  comp_id := by
    intro X Y f
    exact A1NisLocalizedHomQ.comp_id localizingMorphisms f
  assoc := by
    intro W X Y Z f g h
    exact A1NisLocalizedHomQ.assoc localizingMorphisms f g h

end ZigzagLocalizationConstructionQ

end A1NisLocalizationConstruction

open A1NisLocalizationConstruction

/-- Universal-property interface for the A1/Nis localization over the realized generator package. -/
structure A1NisLocalizationUniversalPropertyQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  (localizing : A1NisLocalizingSubcategoryQ complexes)
  (localizingMorphisms : LocalizingMorphismPresentationQ localizing) where
  localizationFunctor :
    BoundedComplexFunctorQ complexes
      (ZigzagLocalizationConstructionQ.targetCategory localizingMorphisms)
  weakEquivalencesInvert :
    ZigzagLocalizationConstructionQ.A1NisWeakEquivalencesInvertInLocalizationQ localizingMorphisms
  factorization :
    ∀ (target : LocalizationTargetCategoryQ)
      (sourceFunctor : BoundedComplexFunctorQ complexes target),
      ZigzagLocalizationConstructionQ.FunctorInvertsA1NisWeakEquivalencesQ
        localizingMorphisms sourceFunctor →
        ZigzagLocalizationConstructionQ.ZigzagLocalizationFactorizationQ
          localizingMorphisms target sourceFunctor
  uniqueness :
    ∀ (target : LocalizationTargetCategoryQ)
      (sourceFunctor : BoundedComplexFunctorQ complexes target)
      (left right : ZigzagLocalizationConstructionQ.FunctorInvertsA1NisWeakEquivalencesQ
        localizingMorphisms sourceFunctor),
      ZigzagLocalizationConstructionQ.ZigzagLocalizationFactorizationAgreementQ
        localizingMorphisms
        (factorization target sourceFunctor left)
        (factorization target sourceFunctor right)

def zigzagUniversalPropertyOfLocalizingMorphisms
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  (localizingMorphisms : LocalizingMorphismPresentationQ localizing) :
  A1NisLocalizationUniversalPropertyQ localizing localizingMorphisms where
  localizationFunctor := ZigzagLocalizationConstructionQ.localizationFunctor localizingMorphisms
  weakEquivalencesInvert :=
    ZigzagLocalizationConstructionQ.weakEquivalencesInvert localizingMorphisms
  factorization := by
    intro target sourceFunctor inverts
    exact ZigzagLocalizationConstructionQ.descendInvertingFunctor
      localizingMorphisms target sourceFunctor inverts
  uniqueness := by
    intro target sourceFunctor left right
    exact ZigzagLocalizationConstructionQ.descendInvertingFunctor_agreement
      localizingMorphisms target sourceFunctor left right

/-- Construction obligation for the Karoubi/idempotent completion of the localized category.

This carries concrete Karoubi objects, morphisms, embedding, proof-relevant splitting data, and
the proof-relevant universal property for idempotent-complete targets over the quotient-zigzag
localization. -/
structure KaroubiEnvelopeConstruction
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
    (localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms) where
  Karoubi : Type (max u v)
  hom : Karoubi → Karoubi → Type (max u v)
  id : ∀ X, hom X X
  comp : ∀ {X Y Z}, hom X Y → hom Y Z → hom X Z
  embed : complexes.Complex → Karoubi
  embedHom : ∀ {X Y : complexes.Complex}, localization.hom X Y → hom (embed X) (embed Y)
  embed_id : ∀ X : complexes.Complex, embedHom (localization.id X) = id (embed X)
  embed_comp :
    ∀ {X Y Z : complexes.Complex} (f : localization.hom X Y) (g : localization.hom Y Z),
      embedHom (localization.comp f g) = comp (embedHom f) (embedHom g)
  splitIdempotent :
    ∀ {X : complexes.Complex} (e : localization.hom X X),
      localization.comp e e = e →
        Σ' (Y : Karoubi) (projection : hom (embed X) Y) (inclusion : hom Y (embed X)),
          comp inclusion projection = id Y ∧
            comp projection inclusion = embedHom e
  id_comp : ∀ {X Y : Karoubi} (f : hom X Y), comp (id X) f = f
  comp_id : ∀ {X Y : Karoubi} (f : hom X Y), comp f (id Y) = f
  assoc :
    ∀ {W X Y Z : Karoubi} (f : hom W X) (g : hom X Y) (h : hom Y Z),
      comp (comp f g) h = comp f (comp g h)

structure ConcreteKaroubiObjectQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  (localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms) where
  obj : complexes.Complex
  idem : localization.hom obj obj
  idem_comp : localization.comp idem idem = idem

structure ConcreteKaroubiHomQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  (localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms)
  (X Y : ConcreteKaroubiObjectQ localization) where
  morphism : localization.hom X.obj Y.obj
  left_idem : localization.comp X.idem morphism = morphism
  right_idem : localization.comp morphism Y.idem = morphism

namespace ConcreteKaroubiHomQ

@[ext] theorem ext
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms}
  {X Y : ConcreteKaroubiObjectQ localization}
  (f g : ConcreteKaroubiHomQ localization X Y)
  (h : f.morphism = g.morphism) : f = g := by
  cases f
  cases g
  cases h
  rfl

def id
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms}
  (X : ConcreteKaroubiObjectQ localization) :
  ConcreteKaroubiHomQ localization X X where
  morphism := X.idem
  left_idem := X.idem_comp
  right_idem := X.idem_comp

def comp
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms}
  {X Y Z : ConcreteKaroubiObjectQ localization}
  (f : ConcreteKaroubiHomQ localization X Y)
  (g : ConcreteKaroubiHomQ localization Y Z) :
  ConcreteKaroubiHomQ localization X Z where
  morphism := localization.comp f.morphism g.morphism
  left_idem := by
    rw [← localization.assoc, f.left_idem]
  right_idem := by
    rw [localization.assoc, g.right_idem]

theorem id_comp
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms}
  {X Y : ConcreteKaroubiObjectQ localization}
  (f : ConcreteKaroubiHomQ localization X Y) :
  ConcreteKaroubiHomQ.comp (ConcreteKaroubiHomQ.id X) f = f := by
  ext
  exact f.left_idem

theorem comp_id
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms}
  {X Y : ConcreteKaroubiObjectQ localization}
  (f : ConcreteKaroubiHomQ localization X Y) :
  ConcreteKaroubiHomQ.comp f (ConcreteKaroubiHomQ.id Y) = f := by
  ext
  exact f.right_idem

theorem assoc
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms}
  {W X Y Z : ConcreteKaroubiObjectQ localization}
  (f : ConcreteKaroubiHomQ localization W X)
  (g : ConcreteKaroubiHomQ localization X Y)
  (h : ConcreteKaroubiHomQ localization Y Z) :
  ConcreteKaroubiHomQ.comp (ConcreteKaroubiHomQ.comp f g) h =
    ConcreteKaroubiHomQ.comp f (ConcreteKaroubiHomQ.comp g h) := by
  ext
  exact localization.assoc _ _ _

end ConcreteKaroubiHomQ

namespace KaroubiEnvelopeConstruction

def embedObject
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  (localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms)
  (X : complexes.Complex) : ConcreteKaroubiObjectQ localization where
  obj := X
  idem := localization.id X
  idem_comp := by rw [localization.id_comp]

def embedMorphism
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  (localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms)
  {X Y : complexes.Complex} (f : localization.hom X Y) :
  ConcreteKaroubiHomQ localization (embedObject localization X) (embedObject localization Y) where
  morphism := f
  left_idem := localization.id_comp f
  right_idem := localization.comp_id f

def concreteSplitIdempotent
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  (localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms)
  {X : complexes.Complex} (e : localization.hom X X)
  (he : localization.comp e e = e) :
  Σ' (Y : ConcreteKaroubiObjectQ localization)
      (projection : ConcreteKaroubiHomQ localization (embedObject localization X) Y)
      (inclusion : ConcreteKaroubiHomQ localization Y (embedObject localization X)),
        ConcreteKaroubiHomQ.comp inclusion projection = ConcreteKaroubiHomQ.id Y ∧
          ConcreteKaroubiHomQ.comp projection inclusion = embedMorphism localization e := by
  refine ⟨
    { obj := X, idem := e, idem_comp := he },
    { morphism := e
      left_idem := localization.id_comp e
      right_idem := he },
    { morphism := e
      left_idem := he
      right_idem := localization.comp_id e },
    ?_, ?_⟩
  · ext
    exact he
  · ext
    exact he

structure IdempotentCompleteTargetCategoryQ.{cu, cv} where
  toTargetCategory : LocalizationTargetCategoryQ.{cu, cv}
  splitIdempotent :
    ∀ {X : toTargetCategory.Obj} (e : toTargetCategory.hom X X),
      toTargetCategory.comp e e = e →
        Σ' (Y : toTargetCategory.Obj)
            (projection : toTargetCategory.hom X Y)
            (inclusion : toTargetCategory.hom Y X),
          toTargetCategory.comp inclusion projection = toTargetCategory.id Y ∧
            toTargetCategory.comp projection inclusion = e

structure CategoryFunctorQ.{su, sv, tu, tv}
  (source : LocalizationTargetCategoryQ.{su, sv})
  (target : LocalizationTargetCategoryQ.{tu, tv}) where
  obj : source.Obj → target.Obj
  map : ∀ {X Y : source.Obj}, source.hom X Y → target.hom (obj X) (obj Y)
  map_id : ∀ X : source.Obj, map (source.id X) = target.id (obj X)
  map_comp :
    ∀ {X Y Z : source.Obj} (f : source.hom X Y) (g : source.hom Y Z),
      map (source.comp f g) = target.comp (map f) (map g)

def sourceCategory
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  (localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms) :
  LocalizationTargetCategoryQ where
  Obj := complexes.Complex
  hom := localization.hom
  id := localization.id
  comp := fun f g => localization.comp f g
  id_comp := by
    intro X Y f
    exact localization.id_comp f
  comp_id := by
    intro X Y f
    exact localization.comp_id f
  assoc := by
    intro W X Y Z f g h
    exact localization.assoc f g h

def concreteTargetCategory
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  (localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms) :
  LocalizationTargetCategoryQ where
  Obj := ConcreteKaroubiObjectQ localization
  hom := ConcreteKaroubiHomQ localization
  id := ConcreteKaroubiHomQ.id
  comp := fun f g => ConcreteKaroubiHomQ.comp f g
  id_comp := by
    intro X Y f
    exact ConcreteKaroubiHomQ.id_comp f
  comp_id := by
    intro X Y f
    exact ConcreteKaroubiHomQ.comp_id f
  assoc := by
    intro W X Y Z f g h
    exact ConcreteKaroubiHomQ.assoc f g h

def karoubiProjection
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  (localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms)
  (X : ConcreteKaroubiObjectQ localization) :
  ConcreteKaroubiHomQ localization (embedObject localization X.obj) X where
  morphism := X.idem
  left_idem := by
    exact localization.id_comp X.idem
  right_idem := by
    exact X.idem_comp

def karoubiInclusion
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  (localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms)
  (X : ConcreteKaroubiObjectQ localization) :
  ConcreteKaroubiHomQ localization X (embedObject localization X.obj) where
  morphism := X.idem
  left_idem := by
    exact X.idem_comp
  right_idem := by
    exact localization.comp_id X.idem

theorem karoubiInclusion_comp_projection
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms}
  (X : ConcreteKaroubiObjectQ localization) :
  ConcreteKaroubiHomQ.comp (karoubiInclusion localization X)
      (karoubiProjection localization X) =
    ConcreteKaroubiHomQ.id X := by
  apply ConcreteKaroubiHomQ.ext
  exact X.idem_comp

theorem karoubiProjection_comp_inclusion
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms}
  (X : ConcreteKaroubiObjectQ localization) :
  ConcreteKaroubiHomQ.comp (karoubiProjection localization X)
      (karoubiInclusion localization X) =
    embedMorphism localization X.idem := by
  apply ConcreteKaroubiHomQ.ext
  exact X.idem_comp

theorem karoubiProjection_naturality
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms}
  {X Y : ConcreteKaroubiObjectQ localization}
  (f : ConcreteKaroubiHomQ localization X Y) :
  ConcreteKaroubiHomQ.comp (karoubiProjection localization X) f =
    ConcreteKaroubiHomQ.comp (embedMorphism localization f.morphism)
      (karoubiProjection localization Y) := by
  apply ConcreteKaroubiHomQ.ext
  calc
    localization.comp X.idem f.morphism = f.morphism := f.left_idem
    _ = localization.comp f.morphism Y.idem := by
      rw [f.right_idem]

theorem karoubiInclusion_naturality
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms}
  {X Y : ConcreteKaroubiObjectQ localization}
  (f : ConcreteKaroubiHomQ localization X Y) :
  ConcreteKaroubiHomQ.comp f (karoubiInclusion localization Y) =
    ConcreteKaroubiHomQ.comp (karoubiInclusion localization X)
      (embedMorphism localization f.morphism) := by
  apply ConcreteKaroubiHomQ.ext
  calc
    localization.comp f.morphism Y.idem = f.morphism := f.right_idem
    _ = localization.comp X.idem f.morphism := by
      rw [f.left_idem]

structure KaroubiExtensionDataQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  (localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms)
  (target : IdempotentCompleteTargetCategoryQ.{max u v, max u v})
  (sourceFunctor : CategoryFunctorQ (sourceCategory localization) target.toTargetCategory) where
  descendedFunctor :
    CategoryFunctorQ (concreteTargetCategory localization) target.toTargetCategory
  embedProjection :
    ∀ X : complexes.Complex,
      target.toTargetCategory.hom (sourceFunctor.obj X)
        (descendedFunctor.obj (embedObject localization X))
  embedInclusion :
    ∀ X : complexes.Complex,
      target.toTargetCategory.hom (descendedFunctor.obj (embedObject localization X))
        (sourceFunctor.obj X)
  embedSection :
    ∀ X : complexes.Complex,
      target.toTargetCategory.comp (embedInclusion X) (embedProjection X) =
        target.toTargetCategory.id (descendedFunctor.obj (embedObject localization X))
  embedRetraction :
    ∀ X : complexes.Complex,
      target.toTargetCategory.comp (embedProjection X) (embedInclusion X) =
        sourceFunctor.map (localization.id X)
  mapCompatibility :
    ∀ {X Y : complexes.Complex} (f : localization.hom X Y),
      target.toTargetCategory.comp (embedInclusion X) (sourceFunctor.map f) =
        target.toTargetCategory.comp
          (descendedFunctor.map (embedMorphism localization f)) (embedInclusion Y)

namespace KaroubiExtensionDataQ

theorem projectionCompatibility
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms}
  {target : IdempotentCompleteTargetCategoryQ.{max u v, max u v}}
  {sourceFunctor : CategoryFunctorQ (sourceCategory localization) target.toTargetCategory}
  (extension : KaroubiExtensionDataQ localization target sourceFunctor)
  {X Y : complexes.Complex} (f : localization.hom X Y) :
  target.toTargetCategory.comp (sourceFunctor.map f) (extension.embedProjection Y) =
    target.toTargetCategory.comp (extension.embedProjection X)
      (extension.descendedFunctor.map (embedMorphism localization f)) := by
  let T := target.toTargetCategory
  calc
    T.comp (sourceFunctor.map f) (extension.embedProjection Y)
      = T.comp (T.id (sourceFunctor.obj X))
          (T.comp (sourceFunctor.map f) (extension.embedProjection Y)) := by
            rw [T.id_comp]
    _ = T.comp (sourceFunctor.map ((sourceCategory localization).id X))
          (T.comp (sourceFunctor.map f) (extension.embedProjection Y)) := by
            rw [← sourceFunctor.map_id X]
    _ = T.comp (sourceFunctor.map (localization.id X))
          (T.comp (sourceFunctor.map f) (extension.embedProjection Y)) := by
            rfl
    _ = T.comp (T.comp (extension.embedProjection X) (extension.embedInclusion X))
          (T.comp (sourceFunctor.map f) (extension.embedProjection Y)) := by
            rw [← extension.embedRetraction X]
    _ = T.comp (extension.embedProjection X)
          (T.comp (extension.embedInclusion X)
            (T.comp (sourceFunctor.map f) (extension.embedProjection Y))) := by
            exact T.assoc
              (extension.embedProjection X)
              (extension.embedInclusion X)
              (T.comp (sourceFunctor.map f) (extension.embedProjection Y))
    _ = T.comp (extension.embedProjection X)
          (T.comp (T.comp (extension.embedInclusion X) (sourceFunctor.map f))
            (extension.embedProjection Y)) := by
            apply congrArg (T.comp (extension.embedProjection X))
            rw [← T.assoc]
    _ = T.comp (extension.embedProjection X)
          (T.comp
            (T.comp (extension.descendedFunctor.map (embedMorphism localization f))
              (extension.embedInclusion Y))
            (extension.embedProjection Y)) := by
            rw [extension.mapCompatibility f]
    _ = T.comp (extension.embedProjection X)
          (T.comp (extension.descendedFunctor.map (embedMorphism localization f))
            (T.comp (extension.embedInclusion Y) (extension.embedProjection Y))) := by
            rw [T.assoc]
    _ = T.comp (extension.embedProjection X)
          (T.comp (extension.descendedFunctor.map (embedMorphism localization f))
            (T.id (extension.descendedFunctor.obj (embedObject localization Y)))) := by
            rw [extension.embedSection Y]
    _ = T.comp (extension.embedProjection X)
          (extension.descendedFunctor.map (embedMorphism localization f)) := by
            rw [T.comp_id]

end KaroubiExtensionDataQ

structure KaroubiExtensionAgreementQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms}
  {target : IdempotentCompleteTargetCategoryQ.{max u v, max u v}}
  {sourceFunctor : CategoryFunctorQ (sourceCategory localization) target.toTargetCategory}
  (left right : KaroubiExtensionDataQ localization target sourceFunctor) where
  objectForward :
    ∀ X : ConcreteKaroubiObjectQ localization,
      target.toTargetCategory.hom (left.descendedFunctor.obj X)
        (right.descendedFunctor.obj X)
  objectBackward :
    ∀ X : ConcreteKaroubiObjectQ localization,
      target.toTargetCategory.hom (right.descendedFunctor.obj X)
        (left.descendedFunctor.obj X)
  forward_backward :
    ∀ X : ConcreteKaroubiObjectQ localization,
      target.toTargetCategory.comp (objectForward X) (objectBackward X) =
        target.toTargetCategory.id (left.descendedFunctor.obj X)
  backward_forward :
    ∀ X : ConcreteKaroubiObjectQ localization,
      target.toTargetCategory.comp (objectBackward X) (objectForward X) =
        target.toTargetCategory.id (right.descendedFunctor.obj X)
  mapEq :
    ∀ {X Y : ConcreteKaroubiObjectQ localization}
      (f : ConcreteKaroubiHomQ localization X Y),
      target.toTargetCategory.comp (objectForward X) (right.descendedFunctor.map f) =
        target.toTargetCategory.comp (left.descendedFunctor.map f) (objectForward Y)

structure UniversalForIdempotentCompleteTargetsDataQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  (localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms) where
  extend :
    ∀ (target : IdempotentCompleteTargetCategoryQ.{max u v, max u v})
      (sourceFunctor : CategoryFunctorQ (sourceCategory localization) target.toTargetCategory),
      KaroubiExtensionDataQ localization target sourceFunctor
  unique :
    ∀ (target : IdempotentCompleteTargetCategoryQ.{max u v, max u v})
      (sourceFunctor : CategoryFunctorQ (sourceCategory localization) target.toTargetCategory)
      (extension : KaroubiExtensionDataQ localization target sourceFunctor),
      KaroubiExtensionAgreementQ (extend target sourceFunctor) extension

def UniversalForIdempotentCompleteTargetsDataQ.statement
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms}
  (data : UniversalForIdempotentCompleteTargetsDataQ localization) : Type (max (u + 1) (v + 1)) :=
  ∀ (target : IdempotentCompleteTargetCategoryQ.{max u v, max u v})
    (sourceFunctor : CategoryFunctorQ (sourceCategory localization) target.toTargetCategory),
      Σ' (extension : KaroubiExtensionDataQ localization target sourceFunctor),
        ∀ extension' : KaroubiExtensionDataQ localization target sourceFunctor,
          KaroubiExtensionAgreementQ extension extension'

def UniversalForIdempotentCompleteTargetsDataQ.holds
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms}
  (data : UniversalForIdempotentCompleteTargetsDataQ localization) :
  data.statement := by
  intro target sourceFunctor
  exact ⟨data.extend target sourceFunctor,
    fun extension' => data.unique target sourceFunctor extension'⟩

private def canonicalSplitDataQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms}
  (target : IdempotentCompleteTargetCategoryQ.{max u v, max u v})
  (sourceFunctor : CategoryFunctorQ (sourceCategory localization) target.toTargetCategory)
  (X : ConcreteKaroubiObjectQ localization) :=
  target.splitIdempotent (sourceFunctor.map X.idem) (by
    rw [← sourceFunctor.map_comp X.idem X.idem]
    change sourceFunctor.map (localization.comp X.idem X.idem) = sourceFunctor.map X.idem
    rw [X.idem_comp])

private def canonicalSplitObjectQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms}
  (target : IdempotentCompleteTargetCategoryQ.{max u v, max u v})
  (sourceFunctor : CategoryFunctorQ (sourceCategory localization) target.toTargetCategory)
  (X : ConcreteKaroubiObjectQ localization) :=
  (canonicalSplitDataQ target sourceFunctor X).1

private def canonicalSplitProjectionQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms}
  (target : IdempotentCompleteTargetCategoryQ.{max u v, max u v})
  (sourceFunctor : CategoryFunctorQ (sourceCategory localization) target.toTargetCategory)
  (X : ConcreteKaroubiObjectQ localization) :
  target.toTargetCategory.hom (sourceFunctor.obj X.obj)
    (canonicalSplitObjectQ target sourceFunctor X) :=
  (canonicalSplitDataQ target sourceFunctor X).2.1

private def canonicalSplitInclusionQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms}
  (target : IdempotentCompleteTargetCategoryQ.{max u v, max u v})
  (sourceFunctor : CategoryFunctorQ (sourceCategory localization) target.toTargetCategory)
  (X : ConcreteKaroubiObjectQ localization) :
  target.toTargetCategory.hom (canonicalSplitObjectQ target sourceFunctor X)
    (sourceFunctor.obj X.obj) :=
  (canonicalSplitDataQ target sourceFunctor X).2.2.1

private theorem canonicalSplitSectionQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms}
  (target : IdempotentCompleteTargetCategoryQ.{max u v, max u v})
  (sourceFunctor : CategoryFunctorQ (sourceCategory localization) target.toTargetCategory)
  (X : ConcreteKaroubiObjectQ localization) :
  target.toTargetCategory.comp
      (canonicalSplitInclusionQ target sourceFunctor X)
      (canonicalSplitProjectionQ target sourceFunctor X) =
    target.toTargetCategory.id (canonicalSplitObjectQ target sourceFunctor X) :=
  (canonicalSplitDataQ target sourceFunctor X).2.2.2.1

private theorem canonicalSplitRetractionQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms}
  (target : IdempotentCompleteTargetCategoryQ.{max u v, max u v})
  (sourceFunctor : CategoryFunctorQ (sourceCategory localization) target.toTargetCategory)
  (X : ConcreteKaroubiObjectQ localization) :
  target.toTargetCategory.comp
      (canonicalSplitProjectionQ target sourceFunctor X)
      (canonicalSplitInclusionQ target sourceFunctor X) =
    sourceFunctor.map X.idem :=
  (canonicalSplitDataQ target sourceFunctor X).2.2.2.2

private theorem mappedLeftIdemQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms}
  {target : IdempotentCompleteTargetCategoryQ.{max u v, max u v}}
  {sourceFunctor : CategoryFunctorQ (sourceCategory localization) target.toTargetCategory}
  {X Y : ConcreteKaroubiObjectQ localization}
  (f : ConcreteKaroubiHomQ localization X Y) :
  target.toTargetCategory.comp (sourceFunctor.map X.idem)
      (sourceFunctor.map f.morphism) =
    sourceFunctor.map f.morphism := by
  rw [← sourceFunctor.map_comp X.idem f.morphism]
  change sourceFunctor.map (localization.comp X.idem f.morphism) = sourceFunctor.map f.morphism
  rw [f.left_idem]

private theorem mappedRightIdemQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms}
  {target : IdempotentCompleteTargetCategoryQ.{max u v, max u v}}
  {sourceFunctor : CategoryFunctorQ (sourceCategory localization) target.toTargetCategory}
  {X Y : ConcreteKaroubiObjectQ localization}
  (f : ConcreteKaroubiHomQ localization X Y) :
  target.toTargetCategory.comp (sourceFunctor.map f.morphism)
      (sourceFunctor.map Y.idem) =
    sourceFunctor.map f.morphism := by
  rw [← sourceFunctor.map_comp f.morphism Y.idem]
  change sourceFunctor.map (localization.comp f.morphism Y.idem) = sourceFunctor.map f.morphism
  rw [f.right_idem]

private theorem canonicalSplitProjection_idemQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms}
  (target : IdempotentCompleteTargetCategoryQ.{max u v, max u v})
  (sourceFunctor : CategoryFunctorQ (sourceCategory localization) target.toTargetCategory)
  (X : ConcreteKaroubiObjectQ localization) :
  target.toTargetCategory.comp (sourceFunctor.map X.idem)
      (canonicalSplitProjectionQ target sourceFunctor X) =
    canonicalSplitProjectionQ target sourceFunctor X := by
  let T := target.toTargetCategory
  calc
    T.comp (sourceFunctor.map X.idem)
        (canonicalSplitProjectionQ target sourceFunctor X)
      = T.comp
          (T.comp (canonicalSplitProjectionQ target sourceFunctor X)
            (canonicalSplitInclusionQ target sourceFunctor X))
          (canonicalSplitProjectionQ target sourceFunctor X) := by
            rw [canonicalSplitRetractionQ target sourceFunctor X]
    _ = T.comp (canonicalSplitProjectionQ target sourceFunctor X)
          (T.comp (canonicalSplitInclusionQ target sourceFunctor X)
            (canonicalSplitProjectionQ target sourceFunctor X)) := by
            rw [T.assoc]
    _ = T.comp (canonicalSplitProjectionQ target sourceFunctor X)
          (T.id (canonicalSplitObjectQ target sourceFunctor X)) := by
            rw [canonicalSplitSectionQ target sourceFunctor X]
    _ = canonicalSplitProjectionQ target sourceFunctor X := by
            rw [T.comp_id]

private theorem canonicalSplitInclusion_idemQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms}
  (target : IdempotentCompleteTargetCategoryQ.{max u v, max u v})
  (sourceFunctor : CategoryFunctorQ (sourceCategory localization) target.toTargetCategory)
  (X : ConcreteKaroubiObjectQ localization) :
  target.toTargetCategory.comp (canonicalSplitInclusionQ target sourceFunctor X)
      (sourceFunctor.map X.idem) =
    canonicalSplitInclusionQ target sourceFunctor X := by
  let T := target.toTargetCategory
  calc
    T.comp (canonicalSplitInclusionQ target sourceFunctor X)
        (sourceFunctor.map X.idem)
      = T.comp (canonicalSplitInclusionQ target sourceFunctor X)
          (T.comp (canonicalSplitProjectionQ target sourceFunctor X)
            (canonicalSplitInclusionQ target sourceFunctor X)) := by
              rw [canonicalSplitRetractionQ target sourceFunctor X]
    _ = T.comp
          (T.comp (canonicalSplitInclusionQ target sourceFunctor X)
            (canonicalSplitProjectionQ target sourceFunctor X))
          (canonicalSplitInclusionQ target sourceFunctor X) := by
              rw [← T.assoc]
    _ = T.comp (T.id (canonicalSplitObjectQ target sourceFunctor X))
          (canonicalSplitInclusionQ target sourceFunctor X) := by
              rw [canonicalSplitSectionQ target sourceFunctor X]
    _ = canonicalSplitInclusionQ target sourceFunctor X := by
              rw [T.id_comp]

private theorem target_comp_four_assocQ
  {T : LocalizationTargetCategoryQ}
  {A B C D E : T.Obj}
  (f : T.hom A B) (g : T.hom B C) (h : T.hom C D) (i : T.hom D E) :
  T.comp (T.comp (T.comp f g) h) i =
    T.comp (T.comp f g) (T.comp h i) := by
  rw [T.assoc]

private theorem target_comp_four_assoc_middleQ
  {T : LocalizationTargetCategoryQ}
  {A B C D E : T.Obj}
  (f : T.hom A B) (g : T.hom B C) (h : T.hom C D) (i : T.hom D E) :
  T.comp (T.comp (T.comp f g) h) i =
    T.comp (T.comp f (T.comp g h)) i := by
  calc
    T.comp (T.comp (T.comp f g) h) i
      = T.comp (T.comp f g) (T.comp h i) := by
          rw [T.assoc]
    _ = T.comp f (T.comp g (T.comp h i)) := by
          rw [T.assoc]
    _ = T.comp f (T.comp (T.comp g h) i) := by
          congr 1
          rw [← T.assoc]
    _ = T.comp (T.comp f (T.comp g h)) i := by
          rw [← T.assoc]

private theorem target_comp_four_split_assocQ
  {T : LocalizationTargetCategoryQ}
  {A B C D E : T.Obj}
  (f : T.hom A B) (g : T.hom B C) (h : T.hom C D) (i : T.hom D E) :
  T.comp (T.comp f g) (T.comp h i) =
    T.comp f (T.comp (T.comp g h) i) := by
  calc
    T.comp (T.comp f g) (T.comp h i)
      = T.comp (T.comp (T.comp f g) h) i := by
          rw [← T.assoc]
    _ = T.comp (T.comp f (T.comp g h)) i := by
          exact target_comp_four_assoc_middleQ (T := T) f g h i
    _ = T.comp f (T.comp (T.comp g h) i) := by
          rw [T.assoc]

private theorem target_comp_four_right_assocQ
  {T : LocalizationTargetCategoryQ}
  {A B C D E : T.Obj}
  (f : T.hom A B) (g : T.hom B C) (h : T.hom C D) (i : T.hom D E) :
  T.comp (T.comp f g) (T.comp h i) =
    T.comp f (T.comp g (T.comp h i)) := by
  calc
    T.comp (T.comp f g) (T.comp h i)
      = T.comp (T.comp (T.comp f g) h) i := by
          exact (target_comp_four_assocQ (T := T) f g h i).symm
    _ = T.comp f (T.comp g (T.comp h i)) := by
          rw [T.assoc, T.assoc]

private theorem target_comp_five_assocQ
  {T : LocalizationTargetCategoryQ}
  {A B C D E F : T.Obj}
  (f : T.hom A B) (g : T.hom B C) (h : T.hom C D) (i : T.hom D E) (j : T.hom E F) :
  T.comp (T.comp (T.comp (T.comp f g) h) i) j =
    T.comp (T.comp (T.comp f g) h) (T.comp i j) := by
  rw [T.assoc]

private theorem target_comp_five_right_assocQ
  {T : LocalizationTargetCategoryQ}
  {A B C D E F : T.Obj}
  (f : T.hom A B) (g : T.hom B C) (h : T.hom C D) (i : T.hom D E) (j : T.hom E F) :
  T.comp (T.comp (T.comp (T.comp f g) h) i) j =
    T.comp f (T.comp g (T.comp h (T.comp i j))) := by
  rw [T.assoc, T.assoc, T.assoc]

private theorem target_comp_six_right_assocQ
  {T : LocalizationTargetCategoryQ}
  {A B C D E F G : T.Obj}
  (f : T.hom A B) (g : T.hom B C) (h : T.hom C D)
  (i : T.hom D E) (j : T.hom E F) (k : T.hom F G) :
  T.comp (T.comp (T.comp (T.comp (T.comp f g) h) i) j) k =
    T.comp f (T.comp g (T.comp h (T.comp i (T.comp j k)))) := by
  rw [T.assoc, T.assoc, T.assoc, T.assoc]

  private theorem target_comp_six_split_tail_assocQ
    {T : LocalizationTargetCategoryQ}
    {A B C D E F G : T.Obj}
    (f : T.hom A B) (g : T.hom B C) (h : T.hom C D)
    (i : T.hom D E) (j : T.hom E F) (k : T.hom F G) :
    T.comp (T.comp (T.comp (T.comp f g) (T.comp h i)) j) k =
      T.comp (T.comp (T.comp (T.comp (T.comp f g) h) i) j) k := by
    apply Eq.symm
    calc
      T.comp (T.comp (T.comp (T.comp (T.comp f g) h) i) j) k
        = T.comp (T.comp (T.comp (T.comp f g) h) (T.comp i j)) k := by
            congr 1
            rw [T.assoc]
      _ = T.comp (T.comp (T.comp f g) (T.comp h (T.comp i j))) k := by
            congr 1
            rw [T.assoc]
      _ = T.comp (T.comp (T.comp f g) (T.comp (T.comp h i) j)) k := by
            congr 1
            congr 1
            rw [← T.assoc]
      _ = T.comp (T.comp (T.comp (T.comp f g) (T.comp h i)) j) k := by
            congr 1
            rw [← T.assoc]

private theorem split_middle_right_idem_cancellationQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms}
  {target : IdempotentCompleteTargetCategoryQ.{max u v, max u v}}
  {sourceFunctor : CategoryFunctorQ (sourceCategory localization) target.toTargetCategory}
  {X Y Z : ConcreteKaroubiObjectQ localization}
  (f : ConcreteKaroubiHomQ localization X Y)
  (g : ConcreteKaroubiHomQ localization Y Z) :
  target.toTargetCategory.comp
      (target.toTargetCategory.comp
        (target.toTargetCategory.comp
          (target.toTargetCategory.comp (canonicalSplitInclusionQ target sourceFunctor X)
            (sourceFunctor.map f.morphism))
          (sourceFunctor.map Y.idem))
        (sourceFunctor.map g.morphism))
      (canonicalSplitProjectionQ target sourceFunctor Z) =
    target.toTargetCategory.comp
      (target.toTargetCategory.comp
        (target.toTargetCategory.comp (canonicalSplitInclusionQ target sourceFunctor X)
          (sourceFunctor.map f.morphism))
        (sourceFunctor.map g.morphism))
      (canonicalSplitProjectionQ target sourceFunctor Z) := by
  let T := target.toTargetCategory
  calc
    T.comp
        (T.comp
          (T.comp
            (T.comp (canonicalSplitInclusionQ target sourceFunctor X)
              (sourceFunctor.map f.morphism))
            (sourceFunctor.map Y.idem))
          (sourceFunctor.map g.morphism))
        (canonicalSplitProjectionQ target sourceFunctor Z)
      = T.comp
          (T.comp
            (T.comp (canonicalSplitInclusionQ target sourceFunctor X)
              (T.comp (sourceFunctor.map f.morphism) (sourceFunctor.map Y.idem)))
            (sourceFunctor.map g.morphism))
          (canonicalSplitProjectionQ target sourceFunctor Z) := by
            exact congrArg
              (fun h => T.comp h (canonicalSplitProjectionQ target sourceFunctor Z))
              (target_comp_four_assoc_middleQ
                (T := T)
                (canonicalSplitInclusionQ target sourceFunctor X)
                (sourceFunctor.map f.morphism)
                (sourceFunctor.map Y.idem)
                (sourceFunctor.map g.morphism))
    _ = T.comp
          (T.comp
            (T.comp (canonicalSplitInclusionQ target sourceFunctor X)
              (sourceFunctor.map f.morphism))
            (sourceFunctor.map g.morphism))
          (canonicalSplitProjectionQ target sourceFunctor Z) := by
            rw [mappedRightIdemQ f]

private def canonicalDescendedKaroubiMapQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms}
  (target : IdempotentCompleteTargetCategoryQ.{max u v, max u v})
  (sourceFunctor : CategoryFunctorQ (sourceCategory localization) target.toTargetCategory)
  {X Y : ConcreteKaroubiObjectQ localization}
  (f : ConcreteKaroubiHomQ localization X Y) :
  target.toTargetCategory.hom
    (canonicalSplitObjectQ target sourceFunctor X)
    (canonicalSplitObjectQ target sourceFunctor Y) :=
  let T := target.toTargetCategory
  -- `comp` is left-to-right here, so the descended map is `incl_X ; F(f) ; proj_Y`.
  T.comp
    (T.comp (canonicalSplitInclusionQ target sourceFunctor X)
      (sourceFunctor.map f.morphism))
    (canonicalSplitProjectionQ target sourceFunctor Y)

def canonicalDescendedKaroubiFunctorQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms}
  (target : IdempotentCompleteTargetCategoryQ.{max u v, max u v})
  (sourceFunctor : CategoryFunctorQ (sourceCategory localization) target.toTargetCategory) :
  CategoryFunctorQ (concreteTargetCategory localization) target.toTargetCategory where
  obj := canonicalSplitObjectQ target sourceFunctor
  map := fun f => canonicalDescendedKaroubiMapQ target sourceFunctor f
  map_id := by
    intro X
    let T := target.toTargetCategory
    calc
      canonicalDescendedKaroubiMapQ target sourceFunctor (ConcreteKaroubiHomQ.id X)
        = T.comp
            (T.comp (canonicalSplitInclusionQ target sourceFunctor X)
              (sourceFunctor.map X.idem))
            (canonicalSplitProjectionQ target sourceFunctor X) := rfl
      _ = T.comp (canonicalSplitInclusionQ target sourceFunctor X)
            (T.comp (sourceFunctor.map X.idem)
              (canonicalSplitProjectionQ target sourceFunctor X)) := by
                rw [← T.assoc]
      _ = T.comp (canonicalSplitInclusionQ target sourceFunctor X)
            (canonicalSplitProjectionQ target sourceFunctor X) := by
                rw [canonicalSplitProjection_idemQ target sourceFunctor X]
      _ = T.id (canonicalSplitObjectQ target sourceFunctor X) := by
                rw [canonicalSplitSectionQ target sourceFunctor X]
  map_comp := by
    intro X Y Z f g
    let T := target.toTargetCategory
    calc
      canonicalDescendedKaroubiMapQ target sourceFunctor (ConcreteKaroubiHomQ.comp f g)
        = T.comp
            (T.comp
              (T.comp (canonicalSplitInclusionQ target sourceFunctor X)
                (sourceFunctor.map f.morphism))
              (sourceFunctor.map g.morphism))
            (canonicalSplitProjectionQ target sourceFunctor Z) := by
                change T.comp
                  (T.comp (canonicalSplitInclusionQ target sourceFunctor X)
                    (sourceFunctor.map ((sourceCategory localization).comp f.morphism g.morphism)))
                  (canonicalSplitProjectionQ target sourceFunctor Z) = _
                rw [sourceFunctor.map_comp]
                rw [← T.assoc]
      _ = T.comp
            (T.comp
              (T.comp
                (T.comp (canonicalSplitInclusionQ target sourceFunctor X)
                  (sourceFunctor.map f.morphism))
                (sourceFunctor.map Y.idem))
              (sourceFunctor.map g.morphism))
            (canonicalSplitProjectionQ target sourceFunctor Z) := by
                exact (split_middle_right_idem_cancellationQ f g).symm
      _ = T.comp
            (T.comp
              (T.comp
                (T.comp (canonicalSplitInclusionQ target sourceFunctor X)
                  (sourceFunctor.map f.morphism))
                (T.comp
                  (canonicalSplitProjectionQ target sourceFunctor Y)
                  (canonicalSplitInclusionQ target sourceFunctor Y)))
              (sourceFunctor.map g.morphism))
            (canonicalSplitProjectionQ target sourceFunctor Z) := by
                congr 1
                congr 1
                rw [← canonicalSplitRetractionQ target sourceFunctor Y]
      _ = T.comp
            (T.comp
              (T.comp
                (T.comp
                  (T.comp (canonicalSplitInclusionQ target sourceFunctor X)
                    (sourceFunctor.map f.morphism))
                  (canonicalSplitProjectionQ target sourceFunctor Y))
                (canonicalSplitInclusionQ target sourceFunctor Y))
              (sourceFunctor.map g.morphism))
            (canonicalSplitProjectionQ target sourceFunctor Z) := by
                exact target_comp_six_split_tail_assocQ
                  (T := T)
                  (canonicalSplitInclusionQ target sourceFunctor X)
                  (sourceFunctor.map f.morphism)
                  (canonicalSplitProjectionQ target sourceFunctor Y)
                  (canonicalSplitInclusionQ target sourceFunctor Y)
                  (sourceFunctor.map g.morphism)
                  (canonicalSplitProjectionQ target sourceFunctor Z)
      _ = T.comp
            (T.comp
              (T.comp
                (T.comp (canonicalSplitInclusionQ target sourceFunctor X)
                  (sourceFunctor.map f.morphism))
                (canonicalSplitProjectionQ target sourceFunctor Y))
              (canonicalSplitInclusionQ target sourceFunctor Y))
            (T.comp (sourceFunctor.map g.morphism)
              (canonicalSplitProjectionQ target sourceFunctor Z)) := by
                exact target_comp_five_assocQ
                  (T := T)
                  (T.comp
                    (canonicalSplitInclusionQ target sourceFunctor X)
                    (sourceFunctor.map f.morphism))
                  (canonicalSplitProjectionQ target sourceFunctor Y)
                  (canonicalSplitInclusionQ target sourceFunctor Y)
                  (sourceFunctor.map g.morphism)
                  (canonicalSplitProjectionQ target sourceFunctor Z)
      _ = T.comp
            (T.comp
              (T.comp (canonicalSplitInclusionQ target sourceFunctor X)
                (sourceFunctor.map f.morphism))
              (canonicalSplitProjectionQ target sourceFunctor Y))
            (T.comp
              (canonicalSplitInclusionQ target sourceFunctor Y)
              (T.comp (sourceFunctor.map g.morphism)
                (canonicalSplitProjectionQ target sourceFunctor Z))) := by
                exact target_comp_four_assocQ
                  (T := T)
                  (T.comp
                    (canonicalSplitInclusionQ target sourceFunctor X)
                    (sourceFunctor.map f.morphism))
                  (canonicalSplitProjectionQ target sourceFunctor Y)
                  (canonicalSplitInclusionQ target sourceFunctor Y)
                  (T.comp (sourceFunctor.map g.morphism)
                    (canonicalSplitProjectionQ target sourceFunctor Z))
      _ = T.comp
            (canonicalDescendedKaroubiMapQ target sourceFunctor f)
            (T.comp
              (canonicalSplitInclusionQ target sourceFunctor Y)
              (T.comp (sourceFunctor.map g.morphism)
                (canonicalSplitProjectionQ target sourceFunctor Z))) := by
                rfl
      _ = T.comp
            (canonicalDescendedKaroubiMapQ target sourceFunctor f)
            (canonicalDescendedKaroubiMapQ target sourceFunctor g) := by
                rw [canonicalDescendedKaroubiMapQ]
                congr 1
                exact (T.assoc
                  (canonicalSplitInclusionQ target sourceFunctor Y)
                  (sourceFunctor.map g.morphism)
                  (canonicalSplitProjectionQ target sourceFunctor Z)).symm

def canonicalDescendedKaroubiExtensionDataQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  (localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms)
  (target : IdempotentCompleteTargetCategoryQ.{max u v, max u v})
  (sourceFunctor : CategoryFunctorQ (sourceCategory localization) target.toTargetCategory) :
  KaroubiExtensionDataQ localization target sourceFunctor where
  descendedFunctor := canonicalDescendedKaroubiFunctorQ target sourceFunctor
  embedProjection := fun X =>
    canonicalSplitProjectionQ target sourceFunctor (embedObject localization X)
  embedInclusion := fun X =>
    canonicalSplitInclusionQ target sourceFunctor (embedObject localization X)
  embedSection := by
    intro X
    exact canonicalSplitSectionQ target sourceFunctor (embedObject localization X)
  embedRetraction := by
    intro X
    exact canonicalSplitRetractionQ target sourceFunctor (embedObject localization X)
  mapCompatibility := by
    intro X Y f
    let T := target.toTargetCategory
    calc
      T.comp
          (canonicalSplitInclusionQ target sourceFunctor (embedObject localization X))
          (sourceFunctor.map f)
        = T.comp
            (T.comp
              (canonicalSplitInclusionQ target sourceFunctor (embedObject localization X))
              (sourceFunctor.map f))
            (T.id (sourceFunctor.obj Y)) := by
              rw [T.comp_id]
      _ = T.comp
            (T.comp
              (canonicalSplitInclusionQ target sourceFunctor (embedObject localization X))
              (sourceFunctor.map f))
            (sourceFunctor.map ((sourceCategory localization).id Y)) := by
              rw [← sourceFunctor.map_id Y]
      _ = T.comp
            (T.comp
              (canonicalSplitInclusionQ target sourceFunctor (embedObject localization X))
              (sourceFunctor.map f))
            (sourceFunctor.map (localization.id Y)) := by
              rfl
      _ = T.comp
            (T.comp
              (canonicalSplitInclusionQ target sourceFunctor (embedObject localization X))
              (sourceFunctor.map f))
            (T.comp
              (canonicalSplitProjectionQ target sourceFunctor (embedObject localization Y))
              (canonicalSplitInclusionQ target sourceFunctor (embedObject localization Y))) := by
              change T.comp
                (T.comp
                  (canonicalSplitInclusionQ target sourceFunctor (embedObject localization X))
                  (sourceFunctor.map f))
                (sourceFunctor.map (embedObject localization Y).idem) = _
              rw [← canonicalSplitRetractionQ target sourceFunctor (embedObject localization Y)]
      _ = T.comp
            (T.comp
              (T.comp
                (canonicalSplitInclusionQ target sourceFunctor (embedObject localization X))
                (sourceFunctor.map f))
              (canonicalSplitProjectionQ target sourceFunctor (embedObject localization Y)))
            (canonicalSplitInclusionQ target sourceFunctor (embedObject localization Y)) := by
              exact (target_comp_four_assocQ
                (T := T)
                (canonicalSplitInclusionQ target sourceFunctor (embedObject localization X))
                (sourceFunctor.map f)
                (canonicalSplitProjectionQ target sourceFunctor (embedObject localization Y))
                (canonicalSplitInclusionQ target sourceFunctor (embedObject localization Y))).symm
      _ = T.comp
            ((canonicalDescendedKaroubiFunctorQ target sourceFunctor).map
              (embedMorphism localization f))
            (canonicalSplitInclusionQ target sourceFunctor (embedObject localization Y)) := by
              rfl

private theorem karoubiProjection_absorb_idemQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms}
  (X : ConcreteKaroubiObjectQ localization) :
  ConcreteKaroubiHomQ.comp (embedMorphism localization X.idem)
      (karoubiProjection localization X) =
    karoubiProjection localization X := by
  apply ConcreteKaroubiHomQ.ext
  exact X.idem_comp

private theorem karoubiInclusion_absorb_idemQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms}
  (X : ConcreteKaroubiObjectQ localization) :
  ConcreteKaroubiHomQ.comp (karoubiInclusion localization X)
      (embedMorphism localization X.idem) =
    karoubiInclusion localization X := by
  apply ConcreteKaroubiHomQ.ext
  exact X.idem_comp

private theorem descendedFunctor_map_compQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms}
  {target : IdempotentCompleteTargetCategoryQ.{max u v, max u v}}
  {sourceFunctor : CategoryFunctorQ (sourceCategory localization) target.toTargetCategory}
  (extension : KaroubiExtensionDataQ localization target sourceFunctor)
  {X Y Z : ConcreteKaroubiObjectQ localization}
  (f : ConcreteKaroubiHomQ localization X Y)
  (g : ConcreteKaroubiHomQ localization Y Z) :
  extension.descendedFunctor.map (ConcreteKaroubiHomQ.comp f g) =
    target.toTargetCategory.comp (extension.descendedFunctor.map f)
      (extension.descendedFunctor.map g) := by
  simpa [concreteTargetCategory] using extension.descendedFunctor.map_comp f g

private theorem descendedFunctor_map_idQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms}
  {target : IdempotentCompleteTargetCategoryQ.{max u v, max u v}}
  {sourceFunctor : CategoryFunctorQ (sourceCategory localization) target.toTargetCategory}
  (extension : KaroubiExtensionDataQ localization target sourceFunctor)
  (X : ConcreteKaroubiObjectQ localization) :
  extension.descendedFunctor.map (ConcreteKaroubiHomQ.id X) =
    target.toTargetCategory.id (extension.descendedFunctor.obj X) := by
  simpa [concreteTargetCategory] using extension.descendedFunctor.map_id X

private def inducedProjectionQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms}
  {target : IdempotentCompleteTargetCategoryQ.{max u v, max u v}}
  {sourceFunctor : CategoryFunctorQ (sourceCategory localization) target.toTargetCategory}
  (extension : KaroubiExtensionDataQ localization target sourceFunctor)
  (X : ConcreteKaroubiObjectQ localization) :
  target.toTargetCategory.hom (sourceFunctor.obj X.obj)
    (extension.descendedFunctor.obj X) :=
  target.toTargetCategory.comp (extension.embedProjection X.obj)
    (extension.descendedFunctor.map (karoubiProjection localization X))

private def inducedInclusionQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms}
  {target : IdempotentCompleteTargetCategoryQ.{max u v, max u v}}
  {sourceFunctor : CategoryFunctorQ (sourceCategory localization) target.toTargetCategory}
  (extension : KaroubiExtensionDataQ localization target sourceFunctor)
  (X : ConcreteKaroubiObjectQ localization) :
  target.toTargetCategory.hom (extension.descendedFunctor.obj X)
    (sourceFunctor.obj X.obj) :=
  target.toTargetCategory.comp
    (extension.descendedFunctor.map (karoubiInclusion localization X))
    (extension.embedInclusion X.obj)

private theorem inducedSectionQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms}
  {target : IdempotentCompleteTargetCategoryQ.{max u v, max u v}}
  {sourceFunctor : CategoryFunctorQ (sourceCategory localization) target.toTargetCategory}
  (extension : KaroubiExtensionDataQ localization target sourceFunctor)
  (X : ConcreteKaroubiObjectQ localization) :
  target.toTargetCategory.comp (inducedInclusionQ extension X)
      (inducedProjectionQ extension X) =
    target.toTargetCategory.id (extension.descendedFunctor.obj X) := by
  let T := target.toTargetCategory
  calc
    T.comp (inducedInclusionQ extension X) (inducedProjectionQ extension X)
      = T.comp
          (extension.descendedFunctor.map (karoubiInclusion localization X))
          (T.comp (extension.embedInclusion X.obj) (inducedProjectionQ extension X)) := by
            rw [inducedInclusionQ, T.assoc]
    _ = T.comp
          (extension.descendedFunctor.map (karoubiInclusion localization X))
          (T.comp
            (T.comp (extension.embedInclusion X.obj) (extension.embedProjection X.obj))
            (extension.descendedFunctor.map (karoubiProjection localization X))) := by
            rw [inducedProjectionQ]
            congr 1
            exact (T.assoc
              (extension.embedInclusion X.obj)
              (extension.embedProjection X.obj)
              (extension.descendedFunctor.map (karoubiProjection localization X))).symm
    _ = T.comp
          (extension.descendedFunctor.map (karoubiInclusion localization X))
          (T.comp
            (T.id (extension.descendedFunctor.obj (embedObject localization X.obj)))
            (extension.descendedFunctor.map (karoubiProjection localization X))) := by
            rw [extension.embedSection X.obj]
    _ = T.comp
          (extension.descendedFunctor.map (karoubiInclusion localization X))
          (extension.descendedFunctor.map (karoubiProjection localization X)) := by
            rw [T.id_comp]
    _ = extension.descendedFunctor.map
          (ConcreteKaroubiHomQ.comp (karoubiInclusion localization X)
            (karoubiProjection localization X)) := by
            rw [← descendedFunctor_map_compQ extension]
    _ = extension.descendedFunctor.map (ConcreteKaroubiHomQ.id X) := by
            rw [karoubiInclusion_comp_projection X]
    _ = T.id (extension.descendedFunctor.obj X) := by
            rw [descendedFunctor_map_idQ extension X]

private theorem inducedRetractionQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms}
  {target : IdempotentCompleteTargetCategoryQ.{max u v, max u v}}
  {sourceFunctor : CategoryFunctorQ (sourceCategory localization) target.toTargetCategory}
  (extension : KaroubiExtensionDataQ localization target sourceFunctor)
  (X : ConcreteKaroubiObjectQ localization) :
  target.toTargetCategory.comp (inducedProjectionQ extension X)
      (inducedInclusionQ extension X) =
    sourceFunctor.map X.idem := by
  let T := target.toTargetCategory
  calc
    T.comp (inducedProjectionQ extension X) (inducedInclusionQ extension X)
      = T.comp
          (extension.embedProjection X.obj)
          (T.comp (extension.descendedFunctor.map (karoubiProjection localization X))
            (inducedInclusionQ extension X)) := by
            rw [inducedProjectionQ, T.assoc]
    _ = T.comp
          (extension.embedProjection X.obj)
          (T.comp (extension.descendedFunctor.map (karoubiProjection localization X))
            (T.comp (extension.descendedFunctor.map (karoubiInclusion localization X))
              (extension.embedInclusion X.obj))) := by
            rw [inducedInclusionQ]
    _ = T.comp
          (extension.embedProjection X.obj)
          (T.comp
            (extension.descendedFunctor.map
              (ConcreteKaroubiHomQ.comp (karoubiProjection localization X)
                (karoubiInclusion localization X)))
            (extension.embedInclusion X.obj)) := by
            calc
              T.comp
                (extension.embedProjection X.obj)
                (T.comp (extension.descendedFunctor.map (karoubiProjection localization X))
                  (T.comp (extension.descendedFunctor.map (karoubiInclusion localization X))
                    (extension.embedInclusion X.obj)))
                = T.comp
                    (extension.embedProjection X.obj)
                    (T.comp
                      (T.comp (extension.descendedFunctor.map (karoubiProjection localization X))
                        (extension.descendedFunctor.map (karoubiInclusion localization X)))
                      (extension.embedInclusion X.obj)) := by
                        congr 1
                        exact (T.assoc
                          (extension.descendedFunctor.map (karoubiProjection localization X))
                          (extension.descendedFunctor.map (karoubiInclusion localization X))
                          (extension.embedInclusion X.obj)).symm
              _ = T.comp
                    (extension.embedProjection X.obj)
                    (T.comp
                      (extension.descendedFunctor.map
                        (ConcreteKaroubiHomQ.comp (karoubiProjection localization X)
                          (karoubiInclusion localization X)))
                      (extension.embedInclusion X.obj)) := by
                        congr 1
                        rw [← descendedFunctor_map_compQ extension]
    _ = T.comp
          (extension.embedProjection X.obj)
          (T.comp (extension.descendedFunctor.map (embedMorphism localization X.idem))
            (extension.embedInclusion X.obj)) := by
            rw [karoubiProjection_comp_inclusion X]
    _ = T.comp
          (T.comp (extension.embedProjection X.obj)
            (extension.descendedFunctor.map (embedMorphism localization X.idem)))
          (extension.embedInclusion X.obj) := by
            exact (T.assoc
              (extension.embedProjection X.obj)
              (extension.descendedFunctor.map (embedMorphism localization X.idem))
              (extension.embedInclusion X.obj)).symm
    _ = T.comp (T.comp (sourceFunctor.map X.idem) (extension.embedProjection X.obj))
          (extension.embedInclusion X.obj) := by
            rw [← KaroubiExtensionDataQ.projectionCompatibility extension X.idem]
    _ = T.comp (sourceFunctor.map X.idem)
          (T.comp (extension.embedProjection X.obj) (extension.embedInclusion X.obj)) := by
            exact T.assoc
              (sourceFunctor.map X.idem)
              (extension.embedProjection X.obj)
              (extension.embedInclusion X.obj)
    _ = T.comp (sourceFunctor.map X.idem)
          (sourceFunctor.map (localization.id X.obj)) := by
            rw [extension.embedRetraction X.obj]
    _ = sourceFunctor.map ((sourceCategory localization).comp X.idem (localization.id X.obj)) := by
            rw [← sourceFunctor.map_comp X.idem (localization.id X.obj)]
    _ = sourceFunctor.map (localization.comp X.idem (localization.id X.obj)) := by
            rfl
    _ = sourceFunctor.map X.idem := by
            rw [localization.comp_id]

private theorem inducedProjectionCompatibilityQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms}
  {target : IdempotentCompleteTargetCategoryQ.{max u v, max u v}}
  {sourceFunctor : CategoryFunctorQ (sourceCategory localization) target.toTargetCategory}
  (extension : KaroubiExtensionDataQ localization target sourceFunctor)
  {X Y : ConcreteKaroubiObjectQ localization}
  (f : ConcreteKaroubiHomQ localization X Y) :
  target.toTargetCategory.comp (sourceFunctor.map f.morphism)
      (inducedProjectionQ extension Y) =
    target.toTargetCategory.comp (inducedProjectionQ extension X)
      (extension.descendedFunctor.map f) := by
  let T := target.toTargetCategory
  calc
    T.comp (sourceFunctor.map f.morphism) (inducedProjectionQ extension Y)
      = T.comp (T.comp (sourceFunctor.map f.morphism) (extension.embedProjection Y.obj))
          (extension.descendedFunctor.map (karoubiProjection localization Y)) := by
            rw [inducedProjectionQ, T.assoc]
    _ = T.comp
          (T.comp (extension.embedProjection X.obj)
            (extension.descendedFunctor.map (embedMorphism localization f.morphism)))
          (extension.descendedFunctor.map (karoubiProjection localization Y)) := by
            rw [KaroubiExtensionDataQ.projectionCompatibility extension f.morphism]
    _ = T.comp (extension.embedProjection X.obj)
          (T.comp (extension.descendedFunctor.map (embedMorphism localization f.morphism))
            (extension.descendedFunctor.map (karoubiProjection localization Y))) := by
            rw [T.assoc]
    _ = T.comp (extension.embedProjection X.obj)
          (extension.descendedFunctor.map
            (ConcreteKaroubiHomQ.comp (embedMorphism localization f.morphism)
              (karoubiProjection localization Y))) := by
            rw [← descendedFunctor_map_compQ extension]
    _ = T.comp (extension.embedProjection X.obj)
          (extension.descendedFunctor.map
            (ConcreteKaroubiHomQ.comp (karoubiProjection localization X) f)) := by
            rw [← karoubiProjection_naturality f]
    _ = T.comp (extension.embedProjection X.obj)
          (T.comp (extension.descendedFunctor.map (karoubiProjection localization X))
            (extension.descendedFunctor.map f)) := by
            rw [descendedFunctor_map_compQ extension]
    _ = T.comp (inducedProjectionQ extension X)
          (extension.descendedFunctor.map f) := by
            rw [inducedProjectionQ, ← T.assoc]

private theorem inducedProjection_idemQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms}
  {target : IdempotentCompleteTargetCategoryQ.{max u v, max u v}}
  {sourceFunctor : CategoryFunctorQ (sourceCategory localization) target.toTargetCategory}
  (extension : KaroubiExtensionDataQ localization target sourceFunctor)
  (X : ConcreteKaroubiObjectQ localization) :
  target.toTargetCategory.comp (sourceFunctor.map X.idem)
      (inducedProjectionQ extension X) =
    inducedProjectionQ extension X := by
  let T := target.toTargetCategory
  calc
    T.comp (sourceFunctor.map X.idem) (inducedProjectionQ extension X)
      = T.comp (T.comp (sourceFunctor.map X.idem) (extension.embedProjection X.obj))
          (extension.descendedFunctor.map (karoubiProjection localization X)) := by
            rw [inducedProjectionQ, T.assoc]
    _ = T.comp
          (T.comp (extension.embedProjection X.obj)
            (extension.descendedFunctor.map (embedMorphism localization X.idem)))
          (extension.descendedFunctor.map (karoubiProjection localization X)) := by
            rw [KaroubiExtensionDataQ.projectionCompatibility extension X.idem]
    _ = T.comp (extension.embedProjection X.obj)
          (T.comp (extension.descendedFunctor.map (embedMorphism localization X.idem))
            (extension.descendedFunctor.map (karoubiProjection localization X))) := by
            rw [T.assoc]
    _ = T.comp (extension.embedProjection X.obj)
          (extension.descendedFunctor.map
            (ConcreteKaroubiHomQ.comp (embedMorphism localization X.idem)
              (karoubiProjection localization X))) := by
            rw [← descendedFunctor_map_compQ extension]
    _ = T.comp (extension.embedProjection X.obj)
          (extension.descendedFunctor.map (karoubiProjection localization X)) := by
            rw [karoubiProjection_absorb_idemQ X]
    _ = inducedProjectionQ extension X := by
            rw [inducedProjectionQ]

private theorem inducedInclusion_idemQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms}
  {target : IdempotentCompleteTargetCategoryQ.{max u v, max u v}}
  {sourceFunctor : CategoryFunctorQ (sourceCategory localization) target.toTargetCategory}
  (extension : KaroubiExtensionDataQ localization target sourceFunctor)
  (X : ConcreteKaroubiObjectQ localization) :
  target.toTargetCategory.comp (inducedInclusionQ extension X)
      (sourceFunctor.map X.idem) =
    inducedInclusionQ extension X := by
  let T := target.toTargetCategory
  calc
    T.comp (inducedInclusionQ extension X) (sourceFunctor.map X.idem)
      = T.comp (extension.descendedFunctor.map (karoubiInclusion localization X))
          (T.comp (extension.embedInclusion X.obj) (sourceFunctor.map X.idem)) := by
            rw [inducedInclusionQ, T.assoc]
    _ = T.comp (extension.descendedFunctor.map (karoubiInclusion localization X))
          (T.comp (extension.descendedFunctor.map (embedMorphism localization X.idem))
            (extension.embedInclusion X.obj)) := by
            rw [extension.mapCompatibility X.idem]
    _ = T.comp
          (T.comp (extension.descendedFunctor.map (karoubiInclusion localization X))
            (extension.descendedFunctor.map (embedMorphism localization X.idem)))
          (extension.embedInclusion X.obj) := by
            rw [← T.assoc]
    _ = T.comp
          (extension.descendedFunctor.map
            (ConcreteKaroubiHomQ.comp (karoubiInclusion localization X)
              (embedMorphism localization X.idem)))
          (extension.embedInclusion X.obj) := by
            rw [descendedFunctor_map_compQ extension]
    _ = T.comp (extension.descendedFunctor.map (karoubiInclusion localization X))
          (extension.embedInclusion X.obj) := by
            rw [karoubiInclusion_absorb_idemQ X]
    _ = inducedInclusionQ extension X := by
            rw [inducedInclusionQ]

def canonicalDescendedKaroubiExtensionAgreementQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms}
  (target : IdempotentCompleteTargetCategoryQ.{max u v, max u v})
  (sourceFunctor : CategoryFunctorQ (sourceCategory localization) target.toTargetCategory)
  (extension : KaroubiExtensionDataQ localization target sourceFunctor) :
  KaroubiExtensionAgreementQ
    (canonicalDescendedKaroubiExtensionDataQ localization target sourceFunctor)
    extension where
  objectForward := fun X =>
    target.toTargetCategory.comp
      (canonicalSplitInclusionQ target sourceFunctor X)
      (inducedProjectionQ extension X)
  objectBackward := fun X =>
    target.toTargetCategory.comp
      (inducedInclusionQ extension X)
      (canonicalSplitProjectionQ target sourceFunctor X)
  forward_backward := by
    intro X
    let T := target.toTargetCategory
    calc
      T.comp
          (T.comp (canonicalSplitInclusionQ target sourceFunctor X)
            (inducedProjectionQ extension X))
          (T.comp (inducedInclusionQ extension X)
            (canonicalSplitProjectionQ target sourceFunctor X))
        = T.comp
            (canonicalSplitInclusionQ target sourceFunctor X)
            (T.comp
              (T.comp (inducedProjectionQ extension X) (inducedInclusionQ extension X))
              (canonicalSplitProjectionQ target sourceFunctor X)) := by
                  exact target_comp_four_split_assocQ
                    (T := T)
                    (canonicalSplitInclusionQ target sourceFunctor X)
                    (inducedProjectionQ extension X)
                    (inducedInclusionQ extension X)
                    (canonicalSplitProjectionQ target sourceFunctor X)
      _ = T.comp
            (canonicalSplitInclusionQ target sourceFunctor X)
            (T.comp (sourceFunctor.map X.idem)
              (canonicalSplitProjectionQ target sourceFunctor X)) := by
                  rw [inducedRetractionQ extension X]
      _ = T.comp
            (canonicalSplitInclusionQ target sourceFunctor X)
            (canonicalSplitProjectionQ target sourceFunctor X) := by
                  rw [canonicalSplitProjection_idemQ target sourceFunctor X]
      _ = T.id (canonicalSplitObjectQ target sourceFunctor X) := by
                  rw [canonicalSplitSectionQ target sourceFunctor X]
  backward_forward := by
    intro X
    let T := target.toTargetCategory
    calc
      T.comp
          (T.comp (inducedInclusionQ extension X)
            (canonicalSplitProjectionQ target sourceFunctor X))
          (T.comp (canonicalSplitInclusionQ target sourceFunctor X)
            (inducedProjectionQ extension X))
        = T.comp
            (inducedInclusionQ extension X)
            (T.comp
              (T.comp (canonicalSplitProjectionQ target sourceFunctor X)
                (canonicalSplitInclusionQ target sourceFunctor X))
              (inducedProjectionQ extension X)) := by
                  exact target_comp_four_split_assocQ
                    (T := T)
                    (inducedInclusionQ extension X)
                    (canonicalSplitProjectionQ target sourceFunctor X)
                    (canonicalSplitInclusionQ target sourceFunctor X)
                    (inducedProjectionQ extension X)
      _ = T.comp
            (inducedInclusionQ extension X)
            (T.comp (sourceFunctor.map X.idem)
              (inducedProjectionQ extension X)) := by
                  rw [canonicalSplitRetractionQ target sourceFunctor X]
      _ = T.comp (inducedInclusionQ extension X) (inducedProjectionQ extension X) := by
                  rw [inducedProjection_idemQ extension X]
      _ = T.id (extension.descendedFunctor.obj X) := by
                  rw [inducedSectionQ extension X]
  mapEq := by
    intro X Y f
    let T := target.toTargetCategory
    calc
      T.comp
          (T.comp (canonicalSplitInclusionQ target sourceFunctor X)
            (inducedProjectionQ extension X))
          (extension.descendedFunctor.map f)
        = T.comp
            (canonicalSplitInclusionQ target sourceFunctor X)
            (T.comp (inducedProjectionQ extension X)
              (extension.descendedFunctor.map f)) := by
                  rw [T.assoc]
      _ = T.comp
            (canonicalSplitInclusionQ target sourceFunctor X)
            (T.comp (sourceFunctor.map f.morphism)
              (inducedProjectionQ extension Y)) := by
                  rw [← inducedProjectionCompatibilityQ extension f]
      _ = T.comp
            (T.comp (canonicalSplitInclusionQ target sourceFunctor X)
              (sourceFunctor.map f.morphism))
            (inducedProjectionQ extension Y) := by
                  rw [← T.assoc]
      _ = T.comp
            (T.comp (canonicalSplitInclusionQ target sourceFunctor X)
              (sourceFunctor.map f.morphism))
            (T.comp (sourceFunctor.map Y.idem) (inducedProjectionQ extension Y)) := by
                  rw [inducedProjection_idemQ extension Y]
      _ = T.comp
            (T.comp (canonicalSplitInclusionQ target sourceFunctor X)
              (sourceFunctor.map f.morphism))
            (T.comp
              (T.comp (canonicalSplitProjectionQ target sourceFunctor Y)
                (canonicalSplitInclusionQ target sourceFunctor Y))
              (inducedProjectionQ extension Y)) := by
                  rw [← canonicalSplitRetractionQ target sourceFunctor Y]
      _ = T.comp
            (T.comp
              (T.comp (canonicalSplitInclusionQ target sourceFunctor X)
                (sourceFunctor.map f.morphism))
              (canonicalSplitProjectionQ target sourceFunctor Y))
            (T.comp (canonicalSplitInclusionQ target sourceFunctor Y)
              (inducedProjectionQ extension Y)) := by
                  calc
                    T.comp
                        (T.comp (canonicalSplitInclusionQ target sourceFunctor X)
                          (sourceFunctor.map f.morphism))
                        (T.comp
                          (T.comp (canonicalSplitProjectionQ target sourceFunctor Y)
                            (canonicalSplitInclusionQ target sourceFunctor Y))
                          (inducedProjectionQ extension Y))
                      = T.comp
                          (T.comp (canonicalSplitInclusionQ target sourceFunctor X)
                            (sourceFunctor.map f.morphism))
                          (T.comp (canonicalSplitProjectionQ target sourceFunctor Y)
                            (T.comp (canonicalSplitInclusionQ target sourceFunctor Y)
                              (inducedProjectionQ extension Y))) := by
                                congr 1
                                exact T.assoc
                                  (canonicalSplitProjectionQ target sourceFunctor Y)
                                  (canonicalSplitInclusionQ target sourceFunctor Y)
                                  (inducedProjectionQ extension Y)
                    _ = T.comp
                          (T.comp
                            (T.comp (canonicalSplitInclusionQ target sourceFunctor X)
                              (sourceFunctor.map f.morphism))
                            (canonicalSplitProjectionQ target sourceFunctor Y))
                          (T.comp (canonicalSplitInclusionQ target sourceFunctor Y)
                            (inducedProjectionQ extension Y)) := by
                                exact (target_comp_four_assocQ
                                  (T := T)
                                  (canonicalSplitInclusionQ target sourceFunctor X)
                                  (sourceFunctor.map f.morphism)
                                  (canonicalSplitProjectionQ target sourceFunctor Y)
                                  (T.comp (canonicalSplitInclusionQ target sourceFunctor Y)
                                    (inducedProjectionQ extension Y))).symm
      _ = T.comp
            (canonicalDescendedKaroubiMapQ target sourceFunctor f)
            (T.comp (canonicalSplitInclusionQ target sourceFunctor Y)
              (inducedProjectionQ extension Y)) := by
                  rw [canonicalDescendedKaroubiMapQ]
      _ = T.comp
            (canonicalDescendedKaroubiMapQ target sourceFunctor f)
            (target.toTargetCategory.comp
              (canonicalSplitInclusionQ target sourceFunctor Y)
              (inducedProjectionQ extension Y)) := by
                  change T.comp
                    (canonicalDescendedKaroubiMapQ target sourceFunctor f)
                    (T.comp (canonicalSplitInclusionQ target sourceFunctor Y)
                      (inducedProjectionQ extension Y)) = _
                  rfl

def canonicalKaroubiUniversalPropertyDataQ
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  (localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms) :
  UniversalForIdempotentCompleteTargetsDataQ localization where
  extend := fun target sourceFunctor =>
    canonicalDescendedKaroubiExtensionDataQ localization target sourceFunctor
  unique := fun target sourceFunctor extension =>
    canonicalDescendedKaroubiExtensionAgreementQ target sourceFunctor extension

def universalPropertyData
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms}
  (_karoubi : KaroubiEnvelopeConstruction localization) :
  UniversalForIdempotentCompleteTargetsDataQ localization :=
  canonicalKaroubiUniversalPropertyDataQ localization

def universalForIdempotentCompleteTargets
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms}
  (karoubi : KaroubiEnvelopeConstruction localization) :
  Type (max (u + 1) (v + 1)) :=
  karoubi.universalPropertyData.statement

def universalForIdempotentCompleteTargets_holds
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  {localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms}
  (karoubi : KaroubiEnvelopeConstruction localization) :
  karoubi.universalForIdempotentCompleteTargets :=
  UniversalForIdempotentCompleteTargetsDataQ.holds (karoubi.universalPropertyData)

/-- Canonical concrete Karoubi envelope built from the localized category using the existing
`(X,e)` objects, compatible morphisms, embedding, and explicit idempotent splittings.

The proof-relevant universal-property interface is retained here, but now the witness data is
expected to be concretely realized by the canonical envelope construction rather than treated as
mere transported equality data. -/
def canonicalKaroubiEnvelopeConstruction
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
  {localizing : A1NisLocalizingSubcategoryQ complexes}
  {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
  (localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms)
  (universalForIdempotentCompleteTargets :
    UniversalForIdempotentCompleteTargetsDataQ localization) :
  KaroubiEnvelopeConstruction localization where
  Karoubi := ConcreteKaroubiObjectQ localization
  hom := ConcreteKaroubiHomQ localization
  id := ConcreteKaroubiHomQ.id
  comp := fun f g => ConcreteKaroubiHomQ.comp f g
  embed := embedObject localization
  embedHom := fun f => embedMorphism localization f
  embed_id := by
    intro X
    apply ConcreteKaroubiHomQ.ext
    rfl
  embed_comp := by
    intro X Y Z f g
    apply ConcreteKaroubiHomQ.ext
    rfl
  splitIdempotent := fun e he => concreteSplitIdempotent localization e he
  id_comp := by
    intro X Y f
    exact ConcreteKaroubiHomQ.id_comp f
  comp_id := by
    intro X Y f
    exact ConcreteKaroubiHomQ.comp_id f
  assoc := by
    intro W X Y Z f g h
    exact ConcreteKaroubiHomQ.assoc f g h

end KaroubiEnvelopeConstruction

/-- Positive localization package sitting over the realized A1/Nis generators on bounded complexes.

This packages a generator-realization package, the localizing subcategory generated by those
realized witnesses, and the localized quotient interface. -/
structure A1NisLocalizationPackageQ
  {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  (complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory)
  {trace : TracePresentation.{u, v, w, x, y}}
  (presentation : ClassicalMotivicPresentation trace) where
  generatorRealization : A1NisGeneratorRealizationPackageQ complexes presentation
  localization :
    ZigzagLocalizationConstructionQ complexes
      generatorRealization.realizedLocalizingSubcategory
      (A1NisGeneratorRealizationPackageQ.localizingMorphismPresentation generatorRealization)
  universalProperty :
    A1NisLocalizationUniversalPropertyQ
      generatorRealization.realizedLocalizingSubcategory
      (A1NisGeneratorRealizationPackageQ.localizingMorphismPresentation generatorRealization)

namespace A1NisLocalizationPackageQ

def universalMap
  {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (package : A1NisLocalizationPackageQ complexes presentation) :
    complexes.Complex → complexes.Complex :=
  package.localization.quotientObj

def localizationFunctor
  {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (package : A1NisLocalizationPackageQ complexes presentation) :
    BoundedComplexFunctorQ complexes
      (ZigzagLocalizationConstructionQ.targetCategory
        (A1NisGeneratorRealizationPackageQ.localizingMorphismPresentation package.generatorRealization)) :=
  package.universalProperty.localizationFunctor

def factorization
  {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (package : A1NisLocalizationPackageQ complexes presentation)
    (target : LocalizationTargetCategoryQ)
    (sourceFunctor : BoundedComplexFunctorQ complexes target)
    (inverts :
      ZigzagLocalizationConstructionQ.FunctorInvertsA1NisWeakEquivalencesQ
        (A1NisGeneratorRealizationPackageQ.localizingMorphismPresentation package.generatorRealization)
        sourceFunctor) :
    ZigzagLocalizationConstructionQ.ZigzagLocalizationFactorizationQ
      (A1NisGeneratorRealizationPackageQ.localizingMorphismPresentation package.generatorRealization)
      target sourceFunctor :=
  package.universalProperty.factorization target sourceFunctor inverts

theorem a1GeneratorsInverted
  {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (package : A1NisLocalizationPackageQ complexes presentation)
    (gen : package.generatorRealization.bridge.closurePackage.primitiveWitnesses.a1.row.GeneratorIndex) :
    A1NisLocalizedHomQ.comp
      (A1NisGeneratorRealizationPackageQ.localizingMorphismPresentation package.generatorRealization)
      ((package.universalProperty.weakEquivalencesInvert.inverse
        (A1NisWeakEquivalenceQ.ofGenerator
          (localizingMorphisms :=
            A1NisGeneratorRealizationPackageQ.localizingMorphismPresentation package.generatorRealization)
          (.a1 gen))))
      (A1NisLocalizedHomQ.ofForward
        (A1NisGeneratorRealizationPackageQ.localizingMorphismPresentation package.generatorRealization)
        (package.generatorRealization.a1MapOfWitness gen)) =
      A1NisLocalizedHomQ.id
        (A1NisGeneratorRealizationPackageQ.localizingMorphismPresentation package.generatorRealization)
        (package.generatorRealization.a1TargetOfWitness gen) := by
  exact package.universalProperty.weakEquivalencesInvert.inverse_comp_forward
    (A1NisWeakEquivalenceQ.ofGenerator
      (localizingMorphisms :=
        A1NisGeneratorRealizationPackageQ.localizingMorphismPresentation package.generatorRealization)
      (.a1 gen))

theorem nisGeneratorsInverted
  {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (package : A1NisLocalizationPackageQ complexes presentation)
    (gen : package.generatorRealization.bridge.closurePackage.primitiveWitnesses.nis.row.GeneratorIndex) :
    A1NisLocalizedHomQ.comp
      (A1NisGeneratorRealizationPackageQ.localizingMorphismPresentation package.generatorRealization)
      ((package.universalProperty.weakEquivalencesInvert.inverse
        (A1NisWeakEquivalenceQ.ofGenerator
          (localizingMorphisms :=
            A1NisGeneratorRealizationPackageQ.localizingMorphismPresentation package.generatorRealization)
          (.nis gen))))
      (A1NisLocalizedHomQ.ofForward
        (A1NisGeneratorRealizationPackageQ.localizingMorphismPresentation package.generatorRealization)
        (package.generatorRealization.nisMapOfWitness gen)) =
      A1NisLocalizedHomQ.id
        (A1NisGeneratorRealizationPackageQ.localizingMorphismPresentation package.generatorRealization)
        (package.generatorRealization.nisMapTargetOfWitness gen) := by
  exact package.universalProperty.weakEquivalencesInvert.inverse_comp_forward
    (A1NisWeakEquivalenceQ.ofGenerator
      (localizingMorphisms :=
        A1NisGeneratorRealizationPackageQ.localizingMorphismPresentation package.generatorRealization)
      (.nis gen))

end A1NisLocalizationPackageQ

/-- Positive Karoubi-completion package over the realized A1/Nis localization. -/
structure KaroubiCompletionPackageQ
  {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  (complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory)
  {trace : TracePresentation.{u, v, w, x, y}}
  (presentation : ClassicalMotivicPresentation trace) where
  localizationPackage : A1NisLocalizationPackageQ complexes presentation

namespace KaroubiCompletionPackageQ

def karoubiEnvelope
  {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (package : KaroubiCompletionPackageQ complexes presentation) :
    KaroubiEnvelopeConstruction package.localizationPackage.localization :=
  KaroubiEnvelopeConstruction.canonicalKaroubiEnvelopeConstruction
    package.localizationPackage.localization
    (KaroubiEnvelopeConstruction.canonicalKaroubiUniversalPropertyDataQ
      package.localizationPackage.localization)

def karoubiUniversalProperty
  {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (package : KaroubiCompletionPackageQ complexes presentation) :
    package.karoubiEnvelope.universalForIdempotentCompleteTargets :=
  KaroubiEnvelopeConstruction.universalForIdempotentCompleteTargets_holds
    package.karoubiEnvelope

def universalMap
  {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (package : KaroubiCompletionPackageQ complexes presentation) :
    complexes.Complex → package.karoubiEnvelope.Karoubi :=
  fun complex => package.karoubiEnvelope.embed (package.localizationPackage.universalMap complex)

def splitIdempotentData
  {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (package : KaroubiCompletionPackageQ complexes presentation)
    {X : complexes.Complex}
    (e : package.localizationPackage.localization.hom X X)
    (he : package.localizationPackage.localization.comp e e = e) :=
  package.karoubiEnvelope.splitIdempotent e he

def universalForIdempotentCompleteTargets
  {category : FiniteCorrespondenceCategoryQ.{1, v, w, x} smoothQSchemeFromWall10A}
    {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
    {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (package : KaroubiCompletionPackageQ complexes presentation) :
    package.karoubiEnvelope.universalForIdempotentCompleteTargets :=
  package.karoubiUniversalProperty

end KaroubiCompletionPackageQ

abbrev DMgmQKaroubi
  {smooth : SmoothQSchemeConstruction.{u}}
  {category : FiniteCorrespondenceCategoryQ.{u, v, w, x} smooth}
  {rationalCategory : RationalFiniteCorrespondenceCategoryQ category}
  {complexes : BoundedComplexOfFiniteCorrespondencesQ rationalCategory}
    {localizing : A1NisLocalizingSubcategoryQ complexes}
    {localizingMorphisms : LocalizingMorphismPresentationQ localizing}
    {localization : ZigzagLocalizationConstructionQ complexes localizing localizingMorphisms}
    (karoubi : KaroubiEnvelopeConstruction localization) : Type (max u v) :=
  karoubi.Karoubi

/-- The assembled classical construction spine for `DM_gm(Q)_Q`.

The live category route is now:
rational finite correspondences -> bounded complexes -> quotient-zigzag A1/Nis localization ->
concrete Karoubi envelope.

This is enough to build `DMgmQWithQCoefficients` and project `DMgmQCategoryData`. The only
remaining construction-level Karoubi universal-property datum is now supplied canonically by the
concrete envelope construction. -/
structure Construction where
  smoothQScheme : SmoothQSchemeConstruction.{u}
  finiteCorrespondenceCategory : FiniteCorrespondenceCategoryQ.{u, v, w, x} smoothQScheme
  rationalCorrespondenceCategory : RationalFiniteCorrespondenceCategoryQ finiteCorrespondenceCategory
  boundedComplexes :
    BoundedComplexOfFiniteCorrespondencesQ rationalCorrespondenceCategory
  a1NisLocalizingSubcategory : A1NisLocalizingSubcategoryQ boundedComplexes
  localizingMorphisms : LocalizingMorphismPresentationQ a1NisLocalizingSubcategory
  localization :
    ZigzagLocalizationConstructionQ boundedComplexes a1NisLocalizingSubcategory localizingMorphisms

namespace Construction

def karoubiUniversalPropertyData (construction : Construction.{u, v, w, x}) :
    KaroubiEnvelopeConstruction.UniversalForIdempotentCompleteTargetsDataQ construction.localization :=
  KaroubiEnvelopeConstruction.canonicalKaroubiUniversalPropertyDataQ construction.localization

def karoubiEnvelope (construction : Construction.{u, v, w, x}) :
    KaroubiEnvelopeConstruction construction.localization :=
  KaroubiEnvelopeConstruction.canonicalKaroubiEnvelopeConstruction
    construction.localization construction.karoubiUniversalPropertyData

def karoubiUniversalProperty (construction : Construction.{u, v, w, x}) :
    construction.karoubiEnvelope.universalForIdempotentCompleteTargets :=
  KaroubiEnvelopeConstruction.universalForIdempotentCompleteTargets_holds
    construction.karoubiEnvelope

abbrev DMgmQWithQCoefficients (construction : Construction.{u, v, w, x}) : Type (max u v) :=
  construction.karoubiEnvelope.Karoubi

def hom (construction : Construction.{u, v, w, x})
  (X Y : construction.DMgmQWithQCoefficients) : Type (max u v) :=
  construction.karoubiEnvelope.hom X Y

def id (construction : Construction.{u, v, w, x})
    (X : construction.DMgmQWithQCoefficients) : construction.hom X X :=
  construction.karoubiEnvelope.id X

def comp (construction : Construction.{u, v, w, x})
    {X Y Z : construction.DMgmQWithQCoefficients}
    (f : construction.hom X Y) (g : construction.hom Y Z) : construction.hom X Z :=
  construction.karoubiEnvelope.comp f g

def distinguishedObject (construction : Construction.{u, v, w, x}) :
    construction.DMgmQWithQCoefficients :=
  construction.karoubiEnvelope.embed
    (construction.localization.quotientObj
      (construction.boundedComplexes.motiveOfSmoothScheme
        construction.finiteCorrespondenceCategory.distinguishedObject))

theorem id_comp (construction : Construction.{u, v, w, x})
    {X Y : construction.DMgmQWithQCoefficients} (f : construction.hom X Y) :
    construction.comp (construction.id X) f = f :=
  construction.karoubiEnvelope.id_comp f

theorem comp_id (construction : Construction.{u, v, w, x})
    {X Y : construction.DMgmQWithQCoefficients} (f : construction.hom X Y) :
    construction.comp f (construction.id Y) = f :=
  construction.karoubiEnvelope.comp_id f

theorem assoc (construction : Construction.{u, v, w, x})
    {W X Y Z : construction.DMgmQWithQCoefficients}
    (f : construction.hom W X) (g : construction.hom X Y) (h : construction.hom Y Z) :
    construction.comp (construction.comp f g) h =
      construction.comp f (construction.comp g h) :=
  construction.karoubiEnvelope.assoc f g h

/-- Fill the raw `DM_gm(Q)_Q` category-data interface from the actual construction spine. -/
def toDMgmQCategoryData (construction : Construction.{u, v, w, x}) :
  FinalMotivicMMQInfrastructure.DMgmQCategoryData.{max u v, max u v} where
  dm_gm_Q_Q_category := construction.DMgmQWithQCoefficients
  dm_gm_Q_Q_object := construction.distinguishedObject
  dm_gm_Q_Q_hom := construction.hom
  dm_gm_Q_Q_id := construction.id
  dm_gm_Q_Q_comp := fun f g => construction.comp f g
  id_comp := by
    intro X Y f
    exact construction.id_comp f
  comp_id := by
    intro X Y f
    exact construction.comp_id f
  assoc := by
    intro W X Y Z f g h
    exact construction.assoc f g h

/-- The first final-gate prefix assembled from the standard rational fields and the constructed
`DM_gm(Q)_Q` category data. -/
def toInfrastructurePrefixData (construction : Construction.{u, v, w, x}) :
  FinalMotivicMMQInfrastructure.InfrastructurePrefixData.{0, 0, max u v, max u v} :=
  FinalMotivicMMQInfrastructure.prefixDataWithStandardRationalFields
    (construction.toDMgmQCategoryData)

/-- The canonical quotient-zigzag localization universal property attached to the live
localizing-morphism presentation in the construction spine. -/
def localizationUniversalProperty (construction : Construction.{u, v, w, x}) :
    A1NisLocalizationUniversalPropertyQ construction.a1NisLocalizingSubcategory
      construction.localizingMorphisms :=
  zigzagUniversalPropertyOfLocalizingMorphisms construction.localizingMorphisms

/-- Construction-aware recognition target tying manuscript-level DMgmQ recognition to the
actual quotient-zigzag/Karoubi construction spine.

Any attempt to instantiate this target from `Construction` must in particular supply the
Karoubi universal-property proof for the concrete envelope. This is the intended blocker until
that theorem is genuinely available. -/
structure ConstructedDMgmQRecognitionTarget (construction : Construction.{u, v, w, x}) where
  constructedCategoryData : FinalMotivicMMQInfrastructure.DMgmQCategoryData.{max u v, max u v}
  categoryDataFromConstruction :
    constructedCategoryData = construction.toDMgmQCategoryData
  constructedInfrastructurePrefix :
    FinalMotivicMMQInfrastructure.InfrastructurePrefixData.{0, 0, max u v, max u v}
  infrastructurePrefixFromConstruction :
    constructedInfrastructurePrefix = construction.toInfrastructurePrefixData
  prefixCarriesConstructedCategoryData :
    constructedInfrastructurePrefix.categoryData = constructedCategoryData
  rationalCorrespondenceStage :
    RationalFiniteCorrespondenceCategoryQ construction.finiteCorrespondenceCategory
  rationalCorrespondenceStageMatchesConstruction :
    rationalCorrespondenceStage = construction.rationalCorrespondenceCategory
  boundedComplexStage :
    BoundedComplexOfFiniteCorrespondencesQ construction.rationalCorrespondenceCategory
  boundedComplexStageMatchesConstruction :
    boundedComplexStage = construction.boundedComplexes
  localizationStage :
    ZigzagLocalizationConstructionQ construction.boundedComplexes
      construction.a1NisLocalizingSubcategory construction.localizingMorphisms
  localizationStageMatchesConstruction :
    localizationStage = construction.localization
  localizationUniversalPropertyStage :
    A1NisLocalizationUniversalPropertyQ construction.a1NisLocalizingSubcategory
      construction.localizingMorphisms
  localizationUniversalPropertyMatchesCanonical :
    localizationUniversalPropertyStage = construction.localizationUniversalProperty
  karoubiEnvelopeStage : KaroubiEnvelopeConstruction construction.localization
  karoubiEnvelopeStageMatchesConstruction :
    karoubiEnvelopeStage = construction.karoubiEnvelope
  karoubiUniversalPropertyData :
    KaroubiEnvelopeConstruction.UniversalForIdempotentCompleteTargetsDataQ
      construction.localization
  karoubiUniversalPropertyDataMatchesConstruction :
    karoubiUniversalPropertyData = construction.karoubiUniversalPropertyData
  karoubiUniversalProperty :
    karoubiEnvelopeStage.universalForIdempotentCompleteTargets

namespace ConstructedDMgmQRecognitionTarget

/-- Build the construction-aware DMgmQ recognition witness directly from the live construction
spine, deriving the current proof-relevant Karoubi universal-property witness from the live
construction data. -/
def ofConstruction
    (construction : Construction.{u, v, w, x}) : ConstructedDMgmQRecognitionTarget construction where
  constructedCategoryData := construction.toDMgmQCategoryData
  categoryDataFromConstruction := rfl
  constructedInfrastructurePrefix := construction.toInfrastructurePrefixData
  infrastructurePrefixFromConstruction := rfl
  prefixCarriesConstructedCategoryData := rfl
  rationalCorrespondenceStage := construction.rationalCorrespondenceCategory
  rationalCorrespondenceStageMatchesConstruction := rfl
  boundedComplexStage := construction.boundedComplexes
  boundedComplexStageMatchesConstruction := rfl
  localizationStage := construction.localization
  localizationStageMatchesConstruction := rfl
  localizationUniversalPropertyStage := construction.localizationUniversalProperty
  localizationUniversalPropertyMatchesCanonical := rfl
  karoubiEnvelopeStage := construction.karoubiEnvelope
  karoubiEnvelopeStageMatchesConstruction := rfl
  karoubiUniversalPropertyData := construction.karoubiUniversalPropertyData
  karoubiUniversalPropertyDataMatchesConstruction := rfl
  karoubiUniversalProperty :=
    KaroubiEnvelopeConstruction.universalForIdempotentCompleteTargets_holds
      construction.karoubiEnvelope

end ConstructedDMgmQRecognitionTarget

end Construction

end DMgmQConstruction
end MotivicRecognition
end TraceCalc

end
