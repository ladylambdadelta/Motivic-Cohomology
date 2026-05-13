import TraceCalc.CategoryInfra.Pretriangulated

universe u v

namespace TraceCalc
namespace CategoryInfra

/-- Quotient data defining the canonical `H^0` homs as cycles modulo a chosen
boundary equivalence relation. -/
structure H0QuotientData {C} (P : PretriangulatedHull C) where
  cycles : ∀ {X Y : P.hull.Obj}, P.hull.HomComplex X Y → Prop
  boundaries : ∀ {X Y : P.hull.Obj}, P.hull.HomComplex X Y → Prop
  boundaryRel :
    ∀ {X Y : P.hull.Obj},
      { f : P.hull.HomComplex X Y // cycles f } →
        { g : P.hull.HomComplex X Y // cycles g } → Prop
  boundaryRel_refl :
    ∀ {X Y : P.hull.Obj} (f : { f : P.hull.HomComplex X Y // cycles f }),
      boundaryRel f f
  boundaryRel_symm :
    ∀ {X Y : P.hull.Obj} {f g : { f : P.hull.HomComplex X Y // cycles f }},
      boundaryRel f g → boundaryRel g f
  boundaryRel_trans :
    ∀ {X Y : P.hull.Obj} {f g h : { f : P.hull.HomComplex X Y // cycles f }},
      boundaryRel f g → boundaryRel g h → boundaryRel f h
  toH0Functor : P.hull.differentialSquaredZero

namespace H0QuotientData

abbrev CycleHom {C} {P : PretriangulatedHull C}
    (data : H0QuotientData P) (X Y : P.hull.Obj) : Type v :=
  { f : P.hull.HomComplex X Y // data.cycles f }

def boundarySetoid {C} {P : PretriangulatedHull C}
    (data : H0QuotientData P) (X Y : P.hull.Obj) : Setoid (data.CycleHom X Y) where
  r := data.boundaryRel
  iseqv := ⟨data.boundaryRel_refl, data.boundaryRel_symm, data.boundaryRel_trans⟩

abbrev H0Hom {C} {P : PretriangulatedHull C}
    (data : H0QuotientData P) (X Y : P.hull.Obj) : Type v :=
  Quotient (data.boundarySetoid X Y)

def quotientMap {C} {P : PretriangulatedHull C}
    (data : H0QuotientData P) {X Y : P.hull.Obj} :
    data.CycleHom X Y → data.H0Hom X Y :=
  Quotient.mk (data.boundarySetoid X Y)

theorem quotientMap_eq_of_boundaryRel {C} {P : PretriangulatedHull C}
    (data : H0QuotientData P) {X Y : P.hull.Obj}
    {f g : data.CycleHom X Y} :
    data.boundaryRel f g → data.quotientMap f = data.quotientMap g :=
  fun h => Quotient.sound h

end H0QuotientData

/-- Triangulated/localization data carried by the `H^0` passage once the
canonical hom quotients are fixed. -/
structure H0TriangulatedData {C} (P : PretriangulatedHull C) where
  distinguishedTriangles : P.coneClosed
  triangulatedAxioms : P.shiftClosed ∧ P.coneClosed
  localizationAtAcyclics : P.universalProperty

/-- Layer B raw data needed to define canonical `H^0` hom quotients before
transport into a hull. -/
structure LayerBHomComplexData where
  objects : Type u
  morphismData : objects → objects → Type v
  differentialRel : ∀ {X Y : objects}, morphismData X Y → morphismData X Y → Prop
  cycles : ∀ {X Y : objects}, morphismData X Y → Prop
  boundaries : ∀ {X Y : objects}, morphismData X Y → Prop
  boundaryRel :
    ∀ {X Y : objects},
      { f : morphismData X Y // cycles f } →
        { g : morphismData X Y // cycles g } → Prop
  boundaryRel_refl :
    ∀ {X Y : objects} (f : { f : morphismData X Y // cycles f }),
      boundaryRel f f
  boundaryRel_symm :
    ∀ {X Y : objects} {f g : { f : morphismData X Y // cycles f }},
      boundaryRel f g → boundaryRel g f
  boundaryRel_trans :
    ∀ {X Y : objects} {f g h : { f : morphismData X Y // cycles f }},
      boundaryRel f g → boundaryRel g h → boundaryRel f h

namespace LayerBHomComplexData

abbrev CycleHom (data : LayerBHomComplexData) (X Y : data.objects) : Type v :=
  { f : data.morphismData X Y // data.cycles f }

def boundarySetoid (data : LayerBHomComplexData) (X Y : data.objects) : Setoid (data.CycleHom X Y) where
  r := data.boundaryRel
  iseqv := ⟨data.boundaryRel_refl, data.boundaryRel_symm, data.boundaryRel_trans⟩

abbrev H0Hom (data : LayerBHomComplexData) (X Y : data.objects) : Type v :=
  Quotient (data.boundarySetoid X Y)

def quotientMap (data : LayerBHomComplexData) {X Y : data.objects} :
    data.CycleHom X Y → data.H0Hom X Y :=
  Quotient.mk (data.boundarySetoid X Y)

end LayerBHomComplexData

/-- Source-side dg data whose cycle quotient canonically determines the `H^0`
homs on the hull. -/
structure LayerBPretriangulatedDGSourceData {C} (P : PretriangulatedHull C) where
  objects : Type u
  objectEquiv : objects ≃ P.hull.Obj
  morphismComplex : objects → objects → Type v
  morphismComplexEquiv :
    ∀ X Y : objects,
      morphismComplex X Y ≃ P.hull.HomComplex (objectEquiv X) (objectEquiv Y)
  cycles : ∀ {X Y : objects}, morphismComplex X Y → Prop
  boundaries : ∀ {X Y : objects}, morphismComplex X Y → Prop
  boundaryRel :
    ∀ {X Y : objects},
      { f : morphismComplex X Y // cycles f } →
        { g : morphismComplex X Y // cycles g } → Prop
  boundaryRel_refl :
    ∀ {X Y : objects} (f : { f : morphismComplex X Y // cycles f }),
      boundaryRel f f
  boundaryRel_symm :
    ∀ {X Y : objects} {f g : { f : morphismComplex X Y // cycles f }},
      boundaryRel f g → boundaryRel g f
  boundaryRel_trans :
    ∀ {X Y : objects} {f g h : { f : morphismComplex X Y // cycles f }},
      boundaryRel f g → boundaryRel g h → boundaryRel f h
  toH0Functor : P.hull.differentialSquaredZero

namespace LayerBPretriangulatedDGSourceData

abbrev CycleHom {C} {P : PretriangulatedHull C}
    (data : LayerBPretriangulatedDGSourceData P) (X Y : data.objects) : Type v :=
  { f : data.morphismComplex X Y // data.cycles f }

def boundarySetoid {C} {P : PretriangulatedHull C}
    (data : LayerBPretriangulatedDGSourceData P) (X Y : data.objects) : Setoid (data.CycleHom X Y) where
  r := data.boundaryRel
  iseqv := ⟨data.boundaryRel_refl, data.boundaryRel_symm, data.boundaryRel_trans⟩

abbrev H0Hom {C} {P : PretriangulatedHull C}
    (data : LayerBPretriangulatedDGSourceData P) (X Y : data.objects) : Type v :=
  Quotient (data.boundarySetoid X Y)

def quotientMap {C} {P : PretriangulatedHull C}
    (data : LayerBPretriangulatedDGSourceData P) {X Y : data.objects} :
    data.CycleHom X Y → data.H0Hom X Y :=
  Quotient.mk (data.boundarySetoid X Y)

end LayerBPretriangulatedDGSourceData

namespace LayerBHomComplexData

def toPretriangulatedDGSourceData {C} {P : PretriangulatedHull C}
    (homData : LayerBHomComplexData)
    (objectEquiv : homData.objects ≃ P.hull.Obj)
    (morphismComplexEquiv :
      ∀ X Y : homData.objects,
        homData.morphismData X Y ≃ P.hull.HomComplex (objectEquiv X) (objectEquiv Y))
    (toH0Functor : P.hull.differentialSquaredZero) : LayerBPretriangulatedDGSourceData P where
  objects := homData.objects
  objectEquiv := objectEquiv
  morphismComplex := homData.morphismData
  morphismComplexEquiv := morphismComplexEquiv
  cycles := @homData.cycles
  boundaries := @homData.boundaries
  boundaryRel := @homData.boundaryRel
  boundaryRel_refl := @homData.boundaryRel_refl
  boundaryRel_symm := @homData.boundaryRel_symm
  boundaryRel_trans := @homData.boundaryRel_trans
  toH0Functor := toH0Functor

@[simp] theorem toPretriangulatedDGSourceData_objects
    {C} {P : PretriangulatedHull C}
    (homData : LayerBHomComplexData)
    (objectEquiv : homData.objects ≃ P.hull.Obj)
    (morphismComplexEquiv :
      ∀ X Y : homData.objects,
        homData.morphismData X Y ≃ P.hull.HomComplex (objectEquiv X) (objectEquiv Y))
    (toH0Functor : P.hull.differentialSquaredZero) :
    (homData.toPretriangulatedDGSourceData objectEquiv morphismComplexEquiv
      toH0Functor).objects = homData.objects :=
  rfl

end LayerBHomComplexData

namespace LayerBPretriangulatedDGSourceData

def toH0QuotientData {C} {P : PretriangulatedHull C}
    (sourceData : LayerBPretriangulatedDGSourceData P) : H0QuotientData P :=
  let pullback : ∀ {X Y : P.hull.Obj}, P.hull.HomComplex X Y →
      sourceData.morphismComplex (sourceData.objectEquiv.symm X) (sourceData.objectEquiv.symm Y) :=
    fun {X} {Y} morphism =>
      let transported :
          P.hull.HomComplex
            (sourceData.objectEquiv (sourceData.objectEquiv.symm X))
            (sourceData.objectEquiv (sourceData.objectEquiv.symm Y)) := by
        simpa using morphism
      (sourceData.morphismComplexEquiv
        (sourceData.objectEquiv.symm X)
        (sourceData.objectEquiv.symm Y)).symm transported
  { cycles := fun morphism => sourceData.cycles (pullback morphism)
    boundaries := fun morphism => sourceData.boundaries (pullback morphism)
    boundaryRel := fun f g =>
      sourceData.boundaryRel
        ⟨pullback f.1, f.2⟩
        ⟨pullback g.1, g.2⟩
    boundaryRel_refl := by
      intro X Y f
      exact sourceData.boundaryRel_refl ⟨pullback f.1, f.2⟩
    boundaryRel_symm := by
      intro X Y f g hfg
      exact sourceData.boundaryRel_symm hfg
    boundaryRel_trans := by
      intro X Y f g h hfg hgh
      exact sourceData.boundaryRel_trans hfg hgh
    toH0Functor := sourceData.toH0Functor }

end LayerBPretriangulatedDGSourceData

/-- Canonical `H^0` category construction data carried by cycle representatives,
their quotient homs, and the induced category laws. -/
structure H0Category {C} (P : PretriangulatedHull C) where
  quotientData : H0QuotientData P
  idCycle : ∀ X : P.hull.Obj, quotientData.CycleHom X X
  compCycle : ∀ {X Y Z : P.hull.Obj},
    quotientData.CycleHom X Y → quotientData.CycleHom Y Z → quotientData.CycleHom X Z
  comp_respects_boundary_left :
    ∀ {X Y Z : P.hull.Obj}
      {f f' : quotientData.CycleHom X Y} (g : quotientData.CycleHom Y Z),
        quotientData.boundaryRel f f' →
          quotientData.boundaryRel (compCycle f g) (compCycle f' g)
  comp_respects_boundary_right :
    ∀ {X Y Z : P.hull.Obj}
      (f : quotientData.CycleHom X Y) {g g' : quotientData.CycleHom Y Z},
        quotientData.boundaryRel g g' →
          quotientData.boundaryRel (compCycle f g) (compCycle f g')
  id_comp
    :
    ∀ {X Y : P.hull.Obj} (f : quotientData.CycleHom X Y),
      quotientData.boundaryRel (compCycle (idCycle X) f) f
  comp_id
    :
    ∀ {X Y : P.hull.Obj} (f : quotientData.CycleHom X Y),
      quotientData.boundaryRel (compCycle f (idCycle Y)) f
  assoc :
    ∀ {W X Y Z : P.hull.Obj}
      (f : quotientData.CycleHom W X)
      (g : quotientData.CycleHom X Y)
      (h : quotientData.CycleHom Y Z),
        quotientData.boundaryRel
          (compCycle (compCycle f g) h)
          (compCycle f (compCycle g h))
  distinguishedTriangles : P.coneClosed
  triangulatedAxioms : P.shiftClosed ∧ P.coneClosed
  localizationAtAcyclics : P.universalProperty

namespace H0Category

abbrev CycleHom {C} {P : PretriangulatedHull C}
    (data : H0Category P) (X Y : P.hull.Obj) : Type v :=
  data.quotientData.CycleHom X Y

abbrev H0Hom {C} {P : PretriangulatedHull C}
    (data : H0Category P) (X Y : P.hull.Obj) : Type v :=
  data.quotientData.H0Hom X Y

def boundarySetoid {C} {P : PretriangulatedHull C}
    (data : H0Category P) (X Y : P.hull.Obj) : Setoid (data.CycleHom X Y) :=
  data.quotientData.boundarySetoid X Y

def quotientMap {C} {P : PretriangulatedHull C}
    (data : H0Category P) {X Y : P.hull.Obj} :
    data.CycleHom X Y → data.H0Hom X Y :=
  data.quotientData.quotientMap

def identity {C} {P : PretriangulatedHull C}
    (data : H0Category P) (X : P.hull.Obj) : data.H0Hom X X :=
  data.quotientMap (data.idCycle X)

def compose {C} {P : PretriangulatedHull C}
    (data : H0Category P) {X Y Z : P.hull.Obj} :
    data.H0Hom X Y → data.H0Hom Y Z → data.H0Hom X Z := by
  intro left right
  refine Quotient.liftOn₂ left right
    (fun f g => data.quotientMap (data.compCycle f g)) ?_
  intro f g f' g' hff' hgg'
  have hLeft :
      data.quotientData.boundaryRel (data.compCycle f g) (data.compCycle f' g) :=
    @H0Category.comp_respects_boundary_left _ _ data X Y Z f f' g hff'
  have hRight :
      data.quotientData.boundaryRel (data.compCycle f' g) (data.compCycle f' g') :=
    @H0Category.comp_respects_boundary_right _ _ data X Y Z f' g g' hgg'
  apply data.quotientData.quotientMap_eq_of_boundaryRel
  exact data.quotientData.boundaryRel_trans hLeft hRight

abbrev toH0Functor {C} {P : PretriangulatedHull C}
    (data : H0Category P) : P.hull.differentialSquaredZero :=
  data.quotientData.toH0Functor

def triangulatedData {C} {P : PretriangulatedHull C}
    (data : H0Category P) : H0TriangulatedData P where
  distinguishedTriangles := data.distinguishedTriangles
  triangulatedAxioms := data.triangulatedAxioms
  localizationAtAcyclics := data.localizationAtAcyclics

theorem identity_comp {C} {P : PretriangulatedHull C}
    (data : H0Category P) {X Y : P.hull.Obj} (f : data.H0Hom X Y) :
    data.compose (data.identity X) f = f := by
  refine Quotient.inductionOn f ?_
  intro representative
  change data.quotientMap (data.compCycle (data.idCycle X) representative) =
    data.quotientMap representative
  exact data.quotientData.quotientMap_eq_of_boundaryRel (data.id_comp representative)

theorem comp_identity {C} {P : PretriangulatedHull C}
    (data : H0Category P) {X Y : P.hull.Obj} (f : data.H0Hom X Y) :
    data.compose f (data.identity Y) = f := by
  refine Quotient.inductionOn f ?_
  intro representative
  change data.quotientMap (data.compCycle representative (data.idCycle Y)) =
    data.quotientMap representative
  exact data.quotientData.quotientMap_eq_of_boundaryRel (data.comp_id representative)

theorem assoc_holds {C} {P : PretriangulatedHull C}
    (data : H0Category P)
    {W X Y Z : P.hull.Obj}
    (f : data.H0Hom W X)
    (g : data.H0Hom X Y)
    (h : data.H0Hom Y Z) :
    data.compose (data.compose f g) h = data.compose f (data.compose g h) := by
  refine Quotient.inductionOn₃ f g h ?_
  intro fRep gRep hRep
  change data.quotientMap (data.compCycle (data.compCycle fRep gRep) hRep) =
    data.quotientMap (data.compCycle fRep (data.compCycle gRep hRep))
  exact data.quotientData.quotientMap_eq_of_boundaryRel (data.assoc fRep gRep hRep)

def ofPieces {C} {P : PretriangulatedHull C}
    (quotientData : H0QuotientData P)
    (idCycle : ∀ X : P.hull.Obj, quotientData.CycleHom X X)
    (compCycle : ∀ {X Y Z : P.hull.Obj},
      quotientData.CycleHom X Y → quotientData.CycleHom Y Z → quotientData.CycleHom X Z)
    (comp_respects_boundary_left :
      ∀ {X Y Z : P.hull.Obj}
        {f f' : quotientData.CycleHom X Y} (g : quotientData.CycleHom Y Z),
          quotientData.boundaryRel f f' →
            quotientData.boundaryRel (compCycle f g) (compCycle f' g))
    (comp_respects_boundary_right :
      ∀ {X Y Z : P.hull.Obj}
        (f : quotientData.CycleHom X Y) {g g' : quotientData.CycleHom Y Z},
          quotientData.boundaryRel g g' →
            quotientData.boundaryRel (compCycle f g) (compCycle f g'))
    (id_comp
      :
      ∀ {X Y : P.hull.Obj} (f : quotientData.CycleHom X Y),
        quotientData.boundaryRel (compCycle (idCycle X) f) f)
    (comp_id
      :
      ∀ {X Y : P.hull.Obj} (f : quotientData.CycleHom X Y),
        quotientData.boundaryRel (compCycle f (idCycle Y)) f)
    (assoc :
      ∀ {W X Y Z : P.hull.Obj}
        (f : quotientData.CycleHom W X)
        (g : quotientData.CycleHom X Y)
        (h : quotientData.CycleHom Y Z),
          quotientData.boundaryRel
            (compCycle (compCycle f g) h)
            (compCycle f (compCycle g h)))
    (triangulatedData : H0TriangulatedData P) : H0Category P where
  quotientData := quotientData
  idCycle := idCycle
  compCycle := compCycle
  comp_respects_boundary_left := comp_respects_boundary_left
  comp_respects_boundary_right := comp_respects_boundary_right
  id_comp
    := id_comp
  comp_id
    := comp_id
  assoc := assoc
  distinguishedTriangles := triangulatedData.distinguishedTriangles
  triangulatedAxioms := triangulatedData.triangulatedAxioms
  localizationAtAcyclics := triangulatedData.localizationAtAcyclics

def ofSourcePieces {C} {P : PretriangulatedHull C}
    (sourceData : LayerBPretriangulatedDGSourceData P)
    (idCycle : ∀ X : P.hull.Obj, sourceData.toH0QuotientData.CycleHom X X)
    (compCycle : ∀ {X Y Z : P.hull.Obj},
      sourceData.toH0QuotientData.CycleHom X Y →
        sourceData.toH0QuotientData.CycleHom Y Z →
          sourceData.toH0QuotientData.CycleHom X Z)
    (comp_respects_boundary_left :
      ∀ {X Y Z : P.hull.Obj}
        {f f' : sourceData.toH0QuotientData.CycleHom X Y}
        (g : sourceData.toH0QuotientData.CycleHom Y Z),
          sourceData.toH0QuotientData.boundaryRel f f' →
            sourceData.toH0QuotientData.boundaryRel (compCycle f g) (compCycle f' g))
    (comp_respects_boundary_right :
      ∀ {X Y Z : P.hull.Obj}
        (f : sourceData.toH0QuotientData.CycleHom X Y)
        {g g' : sourceData.toH0QuotientData.CycleHom Y Z},
          sourceData.toH0QuotientData.boundaryRel g g' →
            sourceData.toH0QuotientData.boundaryRel (compCycle f g) (compCycle f g'))
    (id_comp
      :
      ∀ {X Y : P.hull.Obj} (f : sourceData.toH0QuotientData.CycleHom X Y),
        sourceData.toH0QuotientData.boundaryRel (compCycle (idCycle X) f) f)
    (comp_id
      :
      ∀ {X Y : P.hull.Obj} (f : sourceData.toH0QuotientData.CycleHom X Y),
        sourceData.toH0QuotientData.boundaryRel (compCycle f (idCycle Y)) f)
    (assoc :
      ∀ {W X Y Z : P.hull.Obj}
        (f : sourceData.toH0QuotientData.CycleHom W X)
        (g : sourceData.toH0QuotientData.CycleHom X Y)
        (h : sourceData.toH0QuotientData.CycleHom Y Z),
          sourceData.toH0QuotientData.boundaryRel
            (compCycle (compCycle f g) h)
            (compCycle f (compCycle g h)))
    (triangulatedData : H0TriangulatedData P) : H0Category P :=
  ofPieces sourceData.toH0QuotientData idCycle compCycle
    comp_respects_boundary_left comp_respects_boundary_right
    id_comp comp_id assoc triangulatedData

def ofData {C} (P : PretriangulatedHull C)
    (cycles : ∀ {X Y : P.hull.Obj}, P.hull.HomComplex X Y → Prop)
    (boundaries : ∀ {X Y : P.hull.Obj}, P.hull.HomComplex X Y → Prop)
    (boundaryRel :
      ∀ {X Y : P.hull.Obj},
        { f : P.hull.HomComplex X Y // cycles f } →
          { g : P.hull.HomComplex X Y // cycles g } → Prop)
    (boundaryRel_refl :
      ∀ {X Y : P.hull.Obj} (f : { f : P.hull.HomComplex X Y // cycles f }),
        boundaryRel f f)
    (boundaryRel_symm :
      ∀ {X Y : P.hull.Obj} {f g : { f : P.hull.HomComplex X Y // cycles f }},
        boundaryRel f g → boundaryRel g f)
    (boundaryRel_trans :
      ∀ {X Y : P.hull.Obj} {f g h : { f : P.hull.HomComplex X Y // cycles f }},
        boundaryRel f g → boundaryRel g h → boundaryRel f h)
    (toH0Functor : P.hull.differentialSquaredZero)
    (idCycle : ∀ X : P.hull.Obj,
      { f : P.hull.HomComplex X X // cycles f })
    (compCycle : ∀ {X Y Z : P.hull.Obj},
      { f : P.hull.HomComplex X Y // cycles f } →
        { g : P.hull.HomComplex Y Z // cycles g } →
          { h : P.hull.HomComplex X Z // cycles h })
    (comp_respects_boundary_left :
      ∀ {X Y Z : P.hull.Obj}
        {f f' : { f : P.hull.HomComplex X Y // cycles f }}
        (g : { g : P.hull.HomComplex Y Z // cycles g }),
          boundaryRel f f' → boundaryRel (compCycle f g) (compCycle f' g))
    (comp_respects_boundary_right :
      ∀ {X Y Z : P.hull.Obj}
        (f : { f : P.hull.HomComplex X Y // cycles f })
        {g g' : { g : P.hull.HomComplex Y Z // cycles g }},
          boundaryRel g g' → boundaryRel (compCycle f g) (compCycle f g'))
    (id_comp
      :
      ∀ {X Y : P.hull.Obj} (f : { f : P.hull.HomComplex X Y // cycles f }),
        boundaryRel (compCycle (idCycle X) f) f)
    (comp_id
      :
      ∀ {X Y : P.hull.Obj} (f : { f : P.hull.HomComplex X Y // cycles f }),
        boundaryRel (compCycle f (idCycle Y)) f)
    (assoc :
      ∀ {W X Y Z : P.hull.Obj}
        (f : { f : P.hull.HomComplex W X // cycles f })
        (g : { g : P.hull.HomComplex X Y // cycles g })
        (h : { h : P.hull.HomComplex Y Z // cycles h }),
          boundaryRel (compCycle (compCycle f g) h) (compCycle f (compCycle g h)))
    (triangulatedData : H0TriangulatedData P) : H0Category P :=
  ofPieces
    { cycles := cycles
      boundaries := boundaries
      boundaryRel := boundaryRel
      boundaryRel_refl := boundaryRel_refl
      boundaryRel_symm := boundaryRel_symm
      boundaryRel_trans := boundaryRel_trans
      toH0Functor := toH0Functor }
    idCycle compCycle comp_respects_boundary_left comp_respects_boundary_right
    id_comp comp_id assoc triangulatedData

@[simp] theorem ofPieces_quotientData {C} {P : PretriangulatedHull C}
    (quotientData : H0QuotientData P)
    (idCycle : ∀ X : P.hull.Obj, quotientData.CycleHom X X)
    (compCycle : ∀ {X Y Z : P.hull.Obj},
      quotientData.CycleHom X Y → quotientData.CycleHom Y Z → quotientData.CycleHom X Z)
    (comp_respects_boundary_left :
      ∀ {X Y Z : P.hull.Obj}
        {f f' : quotientData.CycleHom X Y} (g : quotientData.CycleHom Y Z),
          quotientData.boundaryRel f f' →
            quotientData.boundaryRel (compCycle f g) (compCycle f' g))
    (comp_respects_boundary_right :
      ∀ {X Y Z : P.hull.Obj}
        (f : quotientData.CycleHom X Y) {g g' : quotientData.CycleHom Y Z},
          quotientData.boundaryRel g g' →
            quotientData.boundaryRel (compCycle f g) (compCycle f g'))
    (id_comp
      :
      ∀ {X Y : P.hull.Obj} (f : quotientData.CycleHom X Y),
        quotientData.boundaryRel (compCycle (idCycle X) f) f)
    (comp_id
      :
      ∀ {X Y : P.hull.Obj} (f : quotientData.CycleHom X Y),
        quotientData.boundaryRel (compCycle f (idCycle Y)) f)
    (assoc :
      ∀ {W X Y Z : P.hull.Obj}
        (f : quotientData.CycleHom W X)
        (g : quotientData.CycleHom X Y)
        (h : quotientData.CycleHom Y Z),
          quotientData.boundaryRel
            (compCycle (compCycle f g) h)
            (compCycle f (compCycle g h)))
    (triangulatedData : H0TriangulatedData P) :
    (ofPieces quotientData idCycle compCycle comp_respects_boundary_left
      comp_respects_boundary_right id_comp comp_id assoc triangulatedData).quotientData =
      quotientData := by
  rfl

@[simp] theorem ofPieces_triangulatedData {C} {P : PretriangulatedHull C}
    (quotientData : H0QuotientData P)
    (idCycle : ∀ X : P.hull.Obj, quotientData.CycleHom X X)
    (compCycle : ∀ {X Y Z : P.hull.Obj},
      quotientData.CycleHom X Y → quotientData.CycleHom Y Z → quotientData.CycleHom X Z)
    (comp_respects_boundary_left :
      ∀ {X Y Z : P.hull.Obj}
        {f f' : quotientData.CycleHom X Y} (g : quotientData.CycleHom Y Z),
          quotientData.boundaryRel f f' →
            quotientData.boundaryRel (compCycle f g) (compCycle f' g))
    (comp_respects_boundary_right :
      ∀ {X Y Z : P.hull.Obj}
        (f : quotientData.CycleHom X Y) {g g' : quotientData.CycleHom Y Z},
          quotientData.boundaryRel g g' →
            quotientData.boundaryRel (compCycle f g) (compCycle f g'))
    (id_comp
      :
      ∀ {X Y : P.hull.Obj} (f : quotientData.CycleHom X Y),
        quotientData.boundaryRel (compCycle (idCycle X) f) f)
    (comp_id
      :
      ∀ {X Y : P.hull.Obj} (f : quotientData.CycleHom X Y),
        quotientData.boundaryRel (compCycle f (idCycle Y)) f)
    (assoc :
      ∀ {W X Y Z : P.hull.Obj}
        (f : quotientData.CycleHom W X)
        (g : quotientData.CycleHom X Y)
        (h : quotientData.CycleHom Y Z),
          quotientData.boundaryRel
            (compCycle (compCycle f g) h)
            (compCycle f (compCycle g h)))
    (triangulatedData : H0TriangulatedData P) :
    (ofPieces quotientData idCycle compCycle comp_respects_boundary_left
      comp_respects_boundary_right id_comp comp_id assoc triangulatedData).triangulatedData =
      triangulatedData := by
  cases triangulatedData
  rfl

end H0Category

end CategoryInfra
end TraceCalc