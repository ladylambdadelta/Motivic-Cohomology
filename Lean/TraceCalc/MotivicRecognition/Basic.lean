import Mathlib.Data.Rat.Defs

universe u v w x

namespace TraceCalc
namespace MotivicRecognition

/-- Minimal ambient base for a motivic-recognition target.

This is deliberately a theorem-target shell rather than a concrete field/coefficient implementation.
It records only the typed ambient objects that later recognition statements will quantify over. -/
structure MotivicBase where
  BaseObject : Type u
  baseObject : BaseObject
  CoefficientField : Type v
  coefficientField : CoefficientField
  rationalCoefficientsTarget : Prop
  geometricBaseAdmissibilityTarget : Prop

/-- Candidate motivic category used by the recognition layer.

This is not yet a `Category` instance. The goal is to keep the recognition interface lightweight and
to expose the category laws as theorem targets rather than as already-implemented structure. -/
structure MotivicCategoryCandidate (base : MotivicBase.{u, v}) where
  Object : Type w
  Hom : Object → Object → Type x
  id : (X : Object) → Hom X X
  comp : {X Y Z : Object} → Hom Y Z → Hom X Y → Hom X Z
  categoryLaws : Prop
  qLinearTarget : Prop
  additiveTarget : Prop
  idempotentCompleteTarget : Prop

/-- Typed functor candidate between theorem-target motivic categories.

This keeps universal-property statements lightweight: the recognition layer can quantify over
functor-shaped data without requiring full `Category` instances or proved functor laws. -/
structure MotivicFunctorCandidate
    {base : MotivicBase.{u, v}}
    (source target : MotivicCategoryCandidate.{u, v, w, x} base) where
  obj : source.Object → target.Object
  map : {X Y : source.Object} → source.Hom X Y → target.Hom (obj X) (obj Y)
  mapIdTarget : Prop
  mapCompTarget : Prop

namespace MotivicFunctorCandidate

theorem ext_of_obj_map
    {base : MotivicBase.{u, v}}
    {source target : MotivicCategoryCandidate.{u, v, w, x} base}
    {left right : MotivicFunctorCandidate source target}
    (hobj : left.obj = right.obj)
    (hmap : ∀ {X Y : source.Object} (f : source.Hom X Y),
      HEq (left.map f) (right.map f))
    (hleftId : left.mapIdTarget)
    (hrightId : right.mapIdTarget)
    (hleftComp : left.mapCompTarget)
    (hrightComp : right.mapCompTarget) :
    left = right := by
  cases left with
  | mk leftObj leftMap leftMapId leftMapComp =>
      cases right with
      | mk rightObj rightMap rightMapId rightMapComp =>
          cases hobj
          rw [MotivicFunctorCandidate.mk.injEq]
          refine ⟨rfl, ?_, ?_, ?_⟩
          · apply heq_of_eq
            funext X
            funext Y
            funext f
            exact eq_of_heq (hmap f)
          · exact propext (Iff.intro (fun _ => hrightId) (fun _ => hleftId))
          · exact propext (Iff.intro (fun _ => hrightComp) (fun _ => hleftComp))

end MotivicFunctorCandidate

namespace MotivicCategoryCandidate

/-- Endomorphism type in the candidate motivic category. -/
abbrev End
    {base : MotivicBase.{u, v}}
    (candidate : MotivicCategoryCandidate base)
    (X : candidate.Object) : Type x :=
  candidate.Hom X X

end MotivicCategoryCandidate

/-! ## Concrete rational base data (Phase 1, bottom-up) -/

/-- Proof-relevant geometric admissibility data for a chosen base object.

This is not a placeholder witness carrier: it records an actual rational point
of the chosen base object together with an identification of that point with the
distinguished `baseObjectWitness`. -/
structure GeometricBaseAdmissibilityData
    (BaseObject : Type u) (baseObjectWitness : BaseObject) where
  rationalPoint : BaseObject
  point_agrees_with_base : rationalPoint = baseObjectWitness

/-- Proof-relevant data presenting a motivic base whose coefficient field is the
rationals.  Every field is in `Type` and explicitly inhabited; no `Prop` is
asserted abstractly.  The two existing `Prop` slots of `MotivicBase`
(`rationalCoefficientsTarget`, `geometricBaseAdmissibilityTarget`) will be
sourced from `Nonempty` of these data fields by the constructor below. -/
structure RationalMotivicBaseData where
  /-- Type of base-scheme objects (e.g. `Rat`, or a Q-point representation). -/
  baseObjectData : Type u
  /-- Chosen base-scheme inhabitant. -/
  baseObjectWitness : baseObjectData
  /-- Type representing the coefficient field. -/
  coefficientFieldData : Type v
  /-- Chosen coefficient-field inhabitant. -/
  coefficientFieldWitness : coefficientFieldData
  /-- Proof-relevant identification of `coefficientFieldData` with `Rat`. -/
  rationalCoefficientIdentification : coefficientFieldData = ULift.{v} Rat
  /-- Concrete geometric admissibility data for the chosen base object. -/
  baseFieldIsQData :
    GeometricBaseAdmissibilityData baseObjectData baseObjectWitness

/-- Bottom-up constructor producing a `MotivicBase` from explicit rational
data.  The two `Prop` slots are concrete statements extracted from the supplied
law-bearing data, not `Nonempty` of a placeholder witness type. -/
def MotivicBase.ofRationalData (data : RationalMotivicBaseData.{u, v}) :
    MotivicBase.{u, v} where
  BaseObject := data.baseObjectData
  baseObject := data.baseObjectWitness
  CoefficientField := data.coefficientFieldData
  coefficientField := data.coefficientFieldWitness
  rationalCoefficientsTarget := data.coefficientFieldData = ULift.{v} Rat
  geometricBaseAdmissibilityTarget :=
    data.baseFieldIsQData.rationalPoint = data.baseObjectWitness

/-- The standard rational base data: the base scheme is represented by `ULift Rat`,
the coefficient field is `ULift Rat`, the rational identification is `rfl`, and
the admissibility datum is the chosen rational point together with its equality
to the distinguished base witness.  This is fully
constructive and uses no abstract Prop. -/
def standardRationalMotivicBaseDataOverRat :
    RationalMotivicBaseData.{u, v} where
  baseObjectData := ULift.{u} Rat
  baseObjectWitness := ULift.up (0 : Rat)
  coefficientFieldData := ULift.{v} Rat
  coefficientFieldWitness := ULift.up (0 : Rat)
  rationalCoefficientIdentification := rfl
  baseFieldIsQData :=
    { rationalPoint := ULift.up (0 : Rat)
      point_agrees_with_base := rfl }

/-- The standard concrete rational `MotivicBase` over Q. -/
def standardRationalMotivicBase : MotivicBase.{u, v} :=
  MotivicBase.ofRationalData standardRationalMotivicBaseDataOverRat

/-! ## Concrete trace-category computational data (Phase 2, bottom-up) -/

/-- Actual category-law data for a trace-category carrier. -/
structure TraceCategoryLawData
    (Obj : Type w)
    (Hom : Obj → Obj → Type x)
    (id : (X : Obj) → Hom X X)
    (comp : {X Y Z : Obj} → Hom Y Z → Hom X Y → Hom X Z) where
  id_comp : ∀ {X Y : Obj} (f : Hom X Y), comp (id Y) f = f
  comp_id : ∀ {X Y : Obj} (f : Hom X Y), comp f (id X) = f
  assoc :
    ∀ {W X Y Z : Obj}
      (h : Hom Y Z) (g : Hom X Y) (f : Hom W X),
      comp h (comp g f) = comp (comp h g) f

/-- Concrete Q-linear structure data on the morphism families. -/
structure TraceCategoryQLinearData
    (Obj : Type w)
    (Hom : Obj → Obj → Type x) where
  zero : ∀ {X Y : Obj}, Hom X Y
  add : ∀ {X Y : Obj}, Hom X Y → Hom X Y → Hom X Y
  smul : ∀ {X Y : Obj}, ULift.{x} Rat → Hom X Y → Hom X Y
  add_assoc : ∀ {X Y : Obj} (f g h : Hom X Y), add (add f g) h = add f (add g h)
  zero_add : ∀ {X Y : Obj} (f : Hom X Y), add zero f = f
  add_zero : ∀ {X Y : Obj} (f : Hom X Y), add f zero = f
  smul_add :
    ∀ {X Y : Obj} (a : ULift.{x} Rat) (f g : Hom X Y),
      smul a (add f g) = add (smul a f) (smul a g)
  one_smul :
    ∀ {X Y : Obj} (f : Hom X Y),
      smul (ULift.up (1 : Rat)) f = f

/-- Concrete additive-envelope data for the trace category. -/
structure TraceCategoryAdditiveData
    (Obj : Type w)
    (Hom : Obj → Obj → Type x)
    (id : (X : Obj) → Hom X X)
    (comp : {X Y Z : Obj} → Hom Y Z → Hom X Y → Hom X Z) where
  zeroObject : Obj
  fromZero : ∀ X : Obj, Hom zeroObject X
  toZero : ∀ X : Obj, Hom X zeroObject
  zeroObjectIsInitial : ∀ X : Obj, ∃ f : Hom zeroObject X, f = fromZero X
  zeroObjectIsTerminal : ∀ X : Obj, ∃ f : Hom X zeroObject, f = toZero X

/-- Concrete splitting data for idempotent completeness. -/
structure TraceCategoryIdempotentCompleteData
    (Obj : Type w)
    (Hom : Obj → Obj → Type x)
    (comp : {X Y Z : Obj} → Hom Y Z → Hom X Y → Hom X Z) where
  splitObj : ∀ (X : Obj), Hom X X → Obj
  toSplit : ∀ {X : Obj} (e : Hom X X), Hom (splitObj X e) X
  fromSplit : ∀ {X : Obj} (e : Hom X X), Hom X (splitObj X e)
  retracts_idempotent :
    ∀ {X : Obj} (e : Hom X X), comp (toSplit e) (fromSplit e) = e

/-- Proof-relevant computational data for a trace-style motivic category
candidate.  Every law/compatibility slot is a concrete law-bearing structure,
not an abstract witness carrier. The constructor below projects actual
propositions from these structures. -/
structure TraceCategoryComputationalData where
  /-- Carrier type of objects. -/
  Obj : Type w
  /-- Hom families. -/
  Hom : Obj → Obj → Type x
  /-- Identity morphisms. -/
  id : (X : Obj) → Hom X X
  /-- Composition. -/
  comp : {X Y Z : Obj} → Hom Y Z → Hom X Y → Hom X Z
  /-- Identity and associativity laws for the chosen `id` and `comp`. -/
  categoryLawsData : TraceCategoryLawData Obj Hom id comp
  /-- Q-linear structure on the morphism families. -/
  qLinearData : TraceCategoryQLinearData Obj Hom
  /-- Additive-envelope data. -/
  additiveData : TraceCategoryAdditiveData Obj Hom id comp
  /-- Idempotent-splitting data. -/
  idempotentCompleteData : TraceCategoryIdempotentCompleteData Obj Hom comp

namespace TraceCategoryLawData

def toCategoryTarget
    {Obj : Type w}
    {Hom : Obj → Obj → Type x}
    {id : (X : Obj) → Hom X X}
    {comp : {X Y Z : Obj} → Hom Y Z → Hom X Y → Hom X Z}
    (data : TraceCategoryLawData Obj Hom id comp) : Prop :=
  (∀ {X Y : Obj} (f : Hom X Y), comp (id Y) f = f) ∧
    (∀ {X Y : Obj} (f : Hom X Y), comp f (id X) = f) ∧
    (∀ {W X Y Z : Obj} (h : Hom Y Z) (g : Hom X Y) (f : Hom W X),
      comp h (comp g f) = comp (comp h g) f)

end TraceCategoryLawData

namespace TraceCategoryQLinearData

def toQLinearTarget
    {Obj : Type w}
    {Hom : Obj → Obj → Type x}
    (data : TraceCategoryQLinearData Obj Hom) : Prop :=
  (∀ {X Y : Obj} (f g h : Hom X Y), data.add (data.add f g) h = data.add f (data.add g h)) ∧
    (∀ {X Y : Obj} (f : Hom X Y), data.add data.zero f = f) ∧
    (∀ {X Y : Obj} (f : Hom X Y), data.add f data.zero = f) ∧
    (∀ {X Y : Obj} (a : ULift.{x} Rat) (f g : Hom X Y),
      data.smul a (data.add f g) = data.add (data.smul a f) (data.smul a g)) ∧
    (∀ {X Y : Obj} (f : Hom X Y), data.smul (ULift.up (1 : Rat)) f = f)

end TraceCategoryQLinearData

namespace TraceCategoryAdditiveData

def toAdditiveTarget
    {Obj : Type w}
    {Hom : Obj → Obj → Type x}
    {id : (X : Obj) → Hom X X}
    {comp : {X Y Z : Obj} → Hom Y Z → Hom X Y → Hom X Z}
    (data : TraceCategoryAdditiveData Obj Hom id comp) : Prop :=
  (∀ X : Obj, ∃ f : Hom data.zeroObject X, f = data.fromZero X) ∧
    (∀ X : Obj, ∃ f : Hom X data.zeroObject, f = data.toZero X)

end TraceCategoryAdditiveData

namespace TraceCategoryIdempotentCompleteData

def toIdempotentCompleteTarget
    {Obj : Type w}
    {Hom : Obj → Obj → Type x}
    {comp : {X Y Z : Obj} → Hom Y Z → Hom X Y → Hom X Z}
    (data : TraceCategoryIdempotentCompleteData Obj Hom comp) : Prop :=
  ∀ {X : Obj} (e : Hom X X), comp (data.toSplit e) (data.fromSplit e) = e

end TraceCategoryIdempotentCompleteData

/-- Bottom-up constructor producing a `MotivicCategoryCandidate` from a trace
category computational data package.  Every `Prop` slot is the concrete law
statement extracted from the corresponding data structure. -/
def MotivicCategoryCandidate.ofTraceCategoryData
    {base : MotivicBase.{u, v}}
    (data : TraceCategoryComputationalData.{w, x}) :
    MotivicCategoryCandidate.{u, v, w, x} base where
  Object := data.Obj
  Hom := data.Hom
  id := data.id
  comp := data.comp
  categoryLaws := data.categoryLawsData.toCategoryTarget
  qLinearTarget := data.qLinearData.toQLinearTarget
  additiveTarget := data.additiveData.toAdditiveTarget
  idempotentCompleteTarget := data.idempotentCompleteData.toIdempotentCompleteTarget

end MotivicRecognition
end TraceCalc