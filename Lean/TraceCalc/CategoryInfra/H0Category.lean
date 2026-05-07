import TraceCalc.CategoryInfra.Pretriangulated

universe u v

namespace TraceCalc
namespace CategoryInfra

/-- Raw quotient-level data needed to build an `H^0` category from a
pretriangulated dg source. -/
structure H0QuotientData {C : DGCategoryLike.{u, v}} (P : PretriangulatedHull C) where
  Hom : P.hull.Obj → P.hull.Obj → Type v
  id : ∀ X : P.hull.Obj, Hom X X
  comp : ∀ {X Y Z : P.hull.Obj}, Hom X Y → Hom Y Z → Hom X Z
  cycles : ∀ {X Y : P.hull.Obj}, P.hull.HomComplex X Y → Prop
  boundaries : ∀ {X Y : P.hull.Obj}, P.hull.HomComplex X Y → Prop
  quotientMap : ∀ {X Y : P.hull.Obj}, P.hull.HomComplex X Y → Hom X Y
  quotientMapRespectsCycles : Prop
  quotientMapKillsBoundaries : Prop
  toH0Functor : Prop
  quotientMapRespectsCycles_holds : quotientMapRespectsCycles
  quotientMapKillsBoundaries_holds : quotientMapKillsBoundaries
  toH0Functor_holds : toH0Functor

/-- Triangulated/localization data carried by the `H^0` passage once the
underlying quotient category is available. -/
structure H0TriangulatedData {C : DGCategoryLike.{u, v}} (P : PretriangulatedHull C) where
  distinguishedTriangles : Prop
  triangulatedAxioms : Prop
  localizationAtAcyclics : Prop
  distinguishedTriangles_holds : distinguishedTriangles
  triangulatedAxioms_holds : triangulatedAxioms
  localizationAtAcyclics_holds : localizationAtAcyclics

/-- Minimal missing Layer B hom-complex package.

This is the honest fallback when existing Layer B carriers supply object-level
or quotient-level data but still do not expose a pretriangulated dg source.
It records exactly the local data needed before one can build a concrete
`LayerBPretriangulatedDGSourceData`: an object carrier, raw morphism data,
cycle/boundary information, quotient-level homs, and the quotient map. -/
structure LayerBHomComplexData where
  objects : Type u
  morphismData : objects → objects → Type v
  quotientHom : objects → objects → Type v
  id : ∀ X : objects, quotientHom X X
  comp : ∀ {X Y Z : objects}, quotientHom X Y → quotientHom Y Z → quotientHom X Z
  differentialRel : ∀ {X Y : objects}, morphismData X Y → morphismData X Y → Prop
  cycles : ∀ {X Y : objects}, morphismData X Y → Prop
  boundaries : ∀ {X Y : objects}, morphismData X Y → Prop
  quotientMap : ∀ {X Y : objects}, morphismData X Y → quotientHom X Y
  quotientMapRespectsCycles : Prop
  quotientMapKillsBoundaries : Prop
  quotientMapRespectsCycles_holds : quotientMapRespectsCycles
  quotientMapKillsBoundaries_holds : quotientMapKillsBoundaries

/-- Exact missing source package for building a first non-fake `H^0` quotient
candidate from Layer B data.

It records a pretriangulated dg source together with an explicit object carrier,
its morphism complexes, cycle/boundary predicates, a quotient-level hom type,
and the quotient map / `H^0` functor data needed to assemble
`H0QuotientData`. -/
structure LayerBPretriangulatedDGSourceData {C : DGCategoryLike.{u, v}}
    (P : PretriangulatedHull C) where
  objects : Type u
  objectEquiv : objects ≃ P.hull.Obj
  morphismComplex : objects → objects → Type v
  morphismComplexEquiv :
    ∀ X Y : objects,
      morphismComplex X Y ≃ P.hull.HomComplex (objectEquiv X) (objectEquiv Y)
  H0Hom : objects → objects → Type v
  id : ∀ X : objects, H0Hom X X
  comp : ∀ {X Y Z : objects}, H0Hom X Y → H0Hom Y Z → H0Hom X Z
  cycles : ∀ {X Y : objects}, morphismComplex X Y → Prop
  boundaries : ∀ {X Y : objects}, morphismComplex X Y → Prop
  quotientMap : ∀ {X Y : objects}, morphismComplex X Y → H0Hom X Y
  quotientMapRespectsCycles : Prop
  quotientMapKillsBoundaries : Prop
  toH0Functor : Prop
  quotientMapRespectsCycles_holds : quotientMapRespectsCycles
  quotientMapKillsBoundaries_holds : quotientMapKillsBoundaries
  toH0Functor_holds : toH0Functor

namespace LayerBHomComplexData

def toPretriangulatedDGSourceData {C : DGCategoryLike.{u, v}} {P : PretriangulatedHull C}
    (homData : LayerBHomComplexData)
    (objectEquiv : homData.objects ≃ P.hull.Obj)
    (morphismComplexEquiv :
      ∀ X Y : homData.objects,
        homData.morphismData X Y ≃ P.hull.HomComplex (objectEquiv X) (objectEquiv Y))
    (toH0Functor : Prop)
    (toH0Functor_holds : toH0Functor) : LayerBPretriangulatedDGSourceData P where
  objects := homData.objects
  objectEquiv := objectEquiv
  morphismComplex := homData.morphismData
  morphismComplexEquiv := morphismComplexEquiv
  H0Hom := homData.quotientHom
  id := homData.id
  comp := @homData.comp
  cycles := @homData.cycles
  boundaries := @homData.boundaries
  quotientMap := @homData.quotientMap
  quotientMapRespectsCycles := homData.quotientMapRespectsCycles
  quotientMapKillsBoundaries := homData.quotientMapKillsBoundaries
  toH0Functor := toH0Functor
  quotientMapRespectsCycles_holds := homData.quotientMapRespectsCycles_holds
  quotientMapKillsBoundaries_holds := homData.quotientMapKillsBoundaries_holds
  toH0Functor_holds := toH0Functor_holds

@[simp] theorem toPretriangulatedDGSourceData_objects
    {C : DGCategoryLike.{u, v}} {P : PretriangulatedHull C}
    (homData : LayerBHomComplexData)
    (objectEquiv : homData.objects ≃ P.hull.Obj)
    (morphismComplexEquiv :
      ∀ X Y : homData.objects,
        homData.morphismData X Y ≃ P.hull.HomComplex (objectEquiv X) (objectEquiv Y))
    (toH0Functor : Prop)
    (toH0Functor_holds : toH0Functor) :
    (homData.toPretriangulatedDGSourceData objectEquiv morphismComplexEquiv
      toH0Functor toH0Functor_holds).objects = homData.objects :=
  rfl

@[simp] theorem toPretriangulatedDGSourceData_H0Hom
    {C : DGCategoryLike.{u, v}} {P : PretriangulatedHull C}
    (homData : LayerBHomComplexData)
    (objectEquiv : homData.objects ≃ P.hull.Obj)
    (morphismComplexEquiv :
      ∀ X Y : homData.objects,
        homData.morphismData X Y ≃ P.hull.HomComplex (objectEquiv X) (objectEquiv Y))
    (toH0Functor : Prop)
    (toH0Functor_holds : toH0Functor) :
    (homData.toPretriangulatedDGSourceData objectEquiv morphismComplexEquiv
      toH0Functor toH0Functor_holds).H0Hom = homData.quotientHom :=
  rfl

@[simp] theorem toPretriangulatedDGSourceData_quotientMapRespectsCycles
    {C : DGCategoryLike.{u, v}} {P : PretriangulatedHull C}
    (homData : LayerBHomComplexData)
    (objectEquiv : homData.objects ≃ P.hull.Obj)
    (morphismComplexEquiv :
      ∀ X Y : homData.objects,
        homData.morphismData X Y ≃ P.hull.HomComplex (objectEquiv X) (objectEquiv Y))
    (toH0Functor : Prop)
    (toH0Functor_holds : toH0Functor) :
    (homData.toPretriangulatedDGSourceData objectEquiv morphismComplexEquiv
      toH0Functor toH0Functor_holds).quotientMapRespectsCycles =
      homData.quotientMapRespectsCycles :=
  rfl

@[simp] theorem toPretriangulatedDGSourceData_quotientMapKillsBoundaries
    {C : DGCategoryLike.{u, v}} {P : PretriangulatedHull C}
    (homData : LayerBHomComplexData)
    (objectEquiv : homData.objects ≃ P.hull.Obj)
    (morphismComplexEquiv :
      ∀ X Y : homData.objects,
        homData.morphismData X Y ≃ P.hull.HomComplex (objectEquiv X) (objectEquiv Y))
    (toH0Functor : Prop)
    (toH0Functor_holds : toH0Functor) :
    (homData.toPretriangulatedDGSourceData objectEquiv morphismComplexEquiv
      toH0Functor toH0Functor_holds).quotientMapKillsBoundaries =
      homData.quotientMapKillsBoundaries :=
  rfl

end LayerBHomComplexData

namespace LayerBPretriangulatedDGSourceData

def toH0QuotientData {C : DGCategoryLike.{u, v}} {P : PretriangulatedHull C}
    (sourceData : LayerBPretriangulatedDGSourceData P) : H0QuotientData P where
  Hom X Y :=
    sourceData.H0Hom
      (sourceData.objectEquiv.symm X)
      (sourceData.objectEquiv.symm Y)
  id X := sourceData.id (sourceData.objectEquiv.symm X)
  comp := by
    intro X Y Z left right
    exact sourceData.comp left right
  cycles := by
    intro X Y morphism
    have transported :
        P.hull.HomComplex
          (sourceData.objectEquiv (sourceData.objectEquiv.symm X))
          (sourceData.objectEquiv (sourceData.objectEquiv.symm Y)) := by
      simpa using morphism
    exact sourceData.cycles
      (((sourceData.morphismComplexEquiv
          (sourceData.objectEquiv.symm X)
          (sourceData.objectEquiv.symm Y)).symm.toFun) transported)
  boundaries := by
    intro X Y morphism
    have transported :
        P.hull.HomComplex
          (sourceData.objectEquiv (sourceData.objectEquiv.symm X))
          (sourceData.objectEquiv (sourceData.objectEquiv.symm Y)) := by
      simpa using morphism
    exact sourceData.boundaries
      (((sourceData.morphismComplexEquiv
          (sourceData.objectEquiv.symm X)
          (sourceData.objectEquiv.symm Y)).symm.toFun) transported)
  quotientMap := by
    intro X Y morphism
    have transported :
        P.hull.HomComplex
          (sourceData.objectEquiv (sourceData.objectEquiv.symm X))
          (sourceData.objectEquiv (sourceData.objectEquiv.symm Y)) := by
      simpa using morphism
    exact sourceData.quotientMap
      (((sourceData.morphismComplexEquiv
          (sourceData.objectEquiv.symm X)
          (sourceData.objectEquiv.symm Y)).symm.toFun) transported)
  quotientMapRespectsCycles := sourceData.quotientMapRespectsCycles
  quotientMapKillsBoundaries := sourceData.quotientMapKillsBoundaries
  toH0Functor := sourceData.toH0Functor
  quotientMapRespectsCycles_holds := sourceData.quotientMapRespectsCycles_holds
  quotientMapKillsBoundaries_holds := sourceData.quotientMapKillsBoundaries_holds
  toH0Functor_holds := sourceData.toH0Functor_holds

@[simp] theorem toH0QuotientData_toH0Functor {C : DGCategoryLike.{u, v}}
    {P : PretriangulatedHull C}
    (sourceData : LayerBPretriangulatedDGSourceData P) :
    sourceData.toH0QuotientData.toH0Functor = sourceData.toH0Functor :=
  rfl

@[simp] theorem toH0QuotientData_quotientMapRespectsCycles {C : DGCategoryLike.{u, v}}
    {P : PretriangulatedHull C}
    (sourceData : LayerBPretriangulatedDGSourceData P) :
    sourceData.toH0QuotientData.quotientMapRespectsCycles =
      sourceData.quotientMapRespectsCycles :=
  rfl

@[simp] theorem toH0QuotientData_quotientMapKillsBoundaries {C : DGCategoryLike.{u, v}}
    {P : PretriangulatedHull C}
    (sourceData : LayerBPretriangulatedDGSourceData P) :
    sourceData.toH0QuotientData.quotientMapKillsBoundaries =
      sourceData.quotientMapKillsBoundaries :=
  rfl

end LayerBPretriangulatedDGSourceData

/-- Abstract zeroth-cohomology category attached to a pretriangulated dg hull. -/
structure H0Category {C : DGCategoryLike.{u, v}} (P : PretriangulatedHull C) where
  Hom : P.hull.Obj → P.hull.Obj → Type v
  id : ∀ X : P.hull.Obj, Hom X X
  comp : ∀ {X Y Z : P.hull.Obj}, Hom X Y → Hom Y Z → Hom X Z
  cycles : ∀ {X Y : P.hull.Obj}, P.hull.HomComplex X Y → Prop
  boundaries : ∀ {X Y : P.hull.Obj}, P.hull.HomComplex X Y → Prop
  quotientMap : ∀ {X Y : P.hull.Obj}, P.hull.HomComplex X Y → Hom X Y
  quotientMapRespectsCycles : Prop
  quotientMapKillsBoundaries : Prop
  toH0Functor : Prop
  distinguishedTriangles : Prop
  triangulatedAxioms : Prop
  localizationAtAcyclics : Prop
  quotientMapRespectsCycles_holds : quotientMapRespectsCycles
  quotientMapKillsBoundaries_holds : quotientMapKillsBoundaries
  toH0Functor_holds : toH0Functor
  distinguishedTriangles_holds : distinguishedTriangles
  triangulatedAxioms_holds : triangulatedAxioms
  localizationAtAcyclics_holds : localizationAtAcyclics

namespace H0Category

def ofPieces {C : DGCategoryLike.{u, v}} {P : PretriangulatedHull C}
    (quotientData : H0QuotientData P)
    (triangulatedData : H0TriangulatedData P) : H0Category P where
  Hom := quotientData.Hom
  id := quotientData.id
  comp := quotientData.comp
  cycles := quotientData.cycles
  boundaries := quotientData.boundaries
  quotientMap := quotientData.quotientMap
  quotientMapRespectsCycles := quotientData.quotientMapRespectsCycles
  quotientMapKillsBoundaries := quotientData.quotientMapKillsBoundaries
  toH0Functor := quotientData.toH0Functor
  distinguishedTriangles := triangulatedData.distinguishedTriangles
  triangulatedAxioms := triangulatedData.triangulatedAxioms
  localizationAtAcyclics := triangulatedData.localizationAtAcyclics
  quotientMapRespectsCycles_holds := quotientData.quotientMapRespectsCycles_holds
  quotientMapKillsBoundaries_holds := quotientData.quotientMapKillsBoundaries_holds
  toH0Functor_holds := quotientData.toH0Functor_holds
  distinguishedTriangles_holds := triangulatedData.distinguishedTriangles_holds
  triangulatedAxioms_holds := triangulatedData.triangulatedAxioms_holds
  localizationAtAcyclics_holds := triangulatedData.localizationAtAcyclics_holds

def ofSourcePieces {C : DGCategoryLike.{u, v}} {P : PretriangulatedHull C}
    (sourceData : LayerBPretriangulatedDGSourceData P)
    (triangulatedData : H0TriangulatedData P) : H0Category P :=
  ofPieces sourceData.toH0QuotientData triangulatedData

def quotientData {C : DGCategoryLike.{u, v}} {P : PretriangulatedHull C}
    (H : H0Category P) : H0QuotientData P where
  Hom := H.Hom
  id := H.id
  comp := H.comp
  cycles := H.cycles
  boundaries := H.boundaries
  quotientMap := H.quotientMap
  quotientMapRespectsCycles := H.quotientMapRespectsCycles
  quotientMapKillsBoundaries := H.quotientMapKillsBoundaries
  toH0Functor := H.toH0Functor
  quotientMapRespectsCycles_holds := H.quotientMapRespectsCycles_holds
  quotientMapKillsBoundaries_holds := H.quotientMapKillsBoundaries_holds
  toH0Functor_holds := H.toH0Functor_holds

def triangulatedData {C : DGCategoryLike.{u, v}} {P : PretriangulatedHull C}
    (H : H0Category P) : H0TriangulatedData P where
  distinguishedTriangles := H.distinguishedTriangles
  triangulatedAxioms := H.triangulatedAxioms
  localizationAtAcyclics := H.localizationAtAcyclics
  distinguishedTriangles_holds := H.distinguishedTriangles_holds
  triangulatedAxioms_holds := H.triangulatedAxioms_holds
  localizationAtAcyclics_holds := H.localizationAtAcyclics_holds

def ofData {C : DGCategoryLike.{u, v}} (P : PretriangulatedHull C)
    (Hom : P.hull.Obj → P.hull.Obj → Type v)
    (id : ∀ X : P.hull.Obj, Hom X X)
    (comp : ∀ {X Y Z : P.hull.Obj}, Hom X Y → Hom Y Z → Hom X Z)
    (cycles : ∀ {X Y : P.hull.Obj}, P.hull.HomComplex X Y → Prop)
    (boundaries : ∀ {X Y : P.hull.Obj}, P.hull.HomComplex X Y → Prop)
    (quotientMap : ∀ {X Y : P.hull.Obj}, P.hull.HomComplex X Y → Hom X Y)
    (quotientMapRespectsCycles : Prop)
    (quotientMapKillsBoundaries : Prop)
    (toH0Functor : Prop)
    (distinguishedTriangles : Prop)
    (triangulatedAxioms : Prop)
    (localizationAtAcyclics : Prop)
    (quotientMapRespectsCycles_holds : quotientMapRespectsCycles)
    (quotientMapKillsBoundaries_holds : quotientMapKillsBoundaries)
    (toH0Functor_holds : toH0Functor)
    (distinguishedTriangles_holds : distinguishedTriangles)
    (triangulatedAxioms_holds : triangulatedAxioms)
    (localizationAtAcyclics_holds : localizationAtAcyclics) :
    H0Category P :=
  ofPieces
    { Hom := Hom
      id := id
      comp := comp
      cycles := cycles
      boundaries := boundaries
      quotientMap := quotientMap
      quotientMapRespectsCycles := quotientMapRespectsCycles
      quotientMapKillsBoundaries := quotientMapKillsBoundaries
      toH0Functor := toH0Functor
      quotientMapRespectsCycles_holds := quotientMapRespectsCycles_holds
      quotientMapKillsBoundaries_holds := quotientMapKillsBoundaries_holds
      toH0Functor_holds := toH0Functor_holds }
    { distinguishedTriangles := distinguishedTriangles
      triangulatedAxioms := triangulatedAxioms
      localizationAtAcyclics := localizationAtAcyclics
      distinguishedTriangles_holds := distinguishedTriangles_holds
      triangulatedAxioms_holds := triangulatedAxioms_holds
      localizationAtAcyclics_holds := localizationAtAcyclics_holds }

def existenceTarget {C : DGCategoryLike.{u, v}} {P : PretriangulatedHull C}
    (H : H0Category P) : Prop :=
  Nonempty (H0Category.{u, v} P)

theorem existenceTarget_holds {C : DGCategoryLike.{u, v}}
    {P : PretriangulatedHull C} (H : H0Category P) : H.existenceTarget := by
  exact ⟨H⟩

def distinguishedTrianglesTarget {C : DGCategoryLike.{u, v}}
    {P : PretriangulatedHull C} (H : H0Category P) : Prop :=
  H.distinguishedTriangles

theorem distinguishedTrianglesTarget_holds {C : DGCategoryLike.{u, v}}
    {P : PretriangulatedHull C} (H : H0Category P) :
    H.distinguishedTrianglesTarget :=
  H.distinguishedTriangles_holds

def triangulatedAxiomsTarget {C : DGCategoryLike.{u, v}}
    {P : PretriangulatedHull C} (H : H0Category P) : Prop :=
  H.triangulatedAxioms

theorem triangulatedAxiomsTarget_holds {C : DGCategoryLike.{u, v}}
    {P : PretriangulatedHull C} (H : H0Category P) :
    H.triangulatedAxiomsTarget :=
  H.triangulatedAxioms_holds

def localizationAtAcyclicsTarget {C : DGCategoryLike.{u, v}}
    {P : PretriangulatedHull C} (H : H0Category P) : Prop :=
  H.localizationAtAcyclics

theorem localizationAtAcyclicsTarget_holds {C : DGCategoryLike.{u, v}}
    {P : PretriangulatedHull C} (H : H0Category P) :
    H.localizationAtAcyclicsTarget :=
  H.localizationAtAcyclics_holds

def theoremTarget {C : DGCategoryLike.{u, v}} {P : PretriangulatedHull C}
    (H : H0Category P) : Prop :=
  H.existenceTarget ∧
    H.distinguishedTrianglesTarget ∧
      H.triangulatedAxiomsTarget ∧
        H.localizationAtAcyclicsTarget

theorem theoremTarget_holds {C : DGCategoryLike.{u, v}}
    {P : PretriangulatedHull C} (H : H0Category P) : H.theoremTarget := by
  exact ⟨H.existenceTarget_holds, H.distinguishedTrianglesTarget_holds,
    H.triangulatedAxiomsTarget_holds, H.localizationAtAcyclicsTarget_holds⟩

@[simp] theorem ofPieces_quotientData {C : DGCategoryLike.{u, v}}
    {P : PretriangulatedHull C}
    (quotientData : H0QuotientData P)
    (triangulatedData : H0TriangulatedData P) :
    (ofPieces quotientData triangulatedData).quotientData = quotientData := by
  cases quotientData
  cases triangulatedData
  rfl

@[simp] theorem ofPieces_triangulatedData {C : DGCategoryLike.{u, v}}
    {P : PretriangulatedHull C}
    (quotientData : H0QuotientData P)
    (triangulatedData : H0TriangulatedData P) :
    (ofPieces quotientData triangulatedData).triangulatedData = triangulatedData := by
  cases quotientData
  cases triangulatedData
  rfl

@[simp] theorem quotientData_ofData {C : DGCategoryLike.{u, v}}
    (P : PretriangulatedHull C)
    (Hom : P.hull.Obj → P.hull.Obj → Type v)
    (id : ∀ X : P.hull.Obj, Hom X X)
    (comp : ∀ {X Y Z : P.hull.Obj}, Hom X Y → Hom Y Z → Hom X Z)
    (cycles : ∀ {X Y : P.hull.Obj}, P.hull.HomComplex X Y → Prop)
    (boundaries : ∀ {X Y : P.hull.Obj}, P.hull.HomComplex X Y → Prop)
    (quotientMap : ∀ {X Y : P.hull.Obj}, P.hull.HomComplex X Y → Hom X Y)
    (quotientMapRespectsCycles : Prop)
    (quotientMapKillsBoundaries : Prop)
    (toH0Functor : Prop)
    (distinguishedTriangles : Prop)
    (triangulatedAxioms : Prop)
    (localizationAtAcyclics : Prop)
    (quotientMapRespectsCycles_holds : quotientMapRespectsCycles)
    (quotientMapKillsBoundaries_holds : quotientMapKillsBoundaries)
    (toH0Functor_holds : toH0Functor)
    (distinguishedTriangles_holds : distinguishedTriangles)
    (triangulatedAxioms_holds : triangulatedAxioms)
    (localizationAtAcyclics_holds : localizationAtAcyclics) :
    (ofData P Hom id comp cycles boundaries quotientMap
      quotientMapRespectsCycles quotientMapKillsBoundaries toH0Functor
      distinguishedTriangles triangulatedAxioms localizationAtAcyclics
      quotientMapRespectsCycles_holds quotientMapKillsBoundaries_holds
      toH0Functor_holds distinguishedTriangles_holds
      triangulatedAxioms_holds localizationAtAcyclics_holds).quotientData =
      { Hom := Hom
        id := id
        comp := comp
        cycles := cycles
        boundaries := boundaries
        quotientMap := quotientMap
        quotientMapRespectsCycles := quotientMapRespectsCycles
        quotientMapKillsBoundaries := quotientMapKillsBoundaries
        toH0Functor := toH0Functor
        quotientMapRespectsCycles_holds := quotientMapRespectsCycles_holds
        quotientMapKillsBoundaries_holds := quotientMapKillsBoundaries_holds
        toH0Functor_holds := toH0Functor_holds } := by
  rfl

@[simp] theorem triangulatedData_ofData {C : DGCategoryLike.{u, v}}
    (P : PretriangulatedHull C)
    (Hom : P.hull.Obj → P.hull.Obj → Type v)
    (id : ∀ X : P.hull.Obj, Hom X X)
    (comp : ∀ {X Y Z : P.hull.Obj}, Hom X Y → Hom Y Z → Hom X Z)
    (cycles : ∀ {X Y : P.hull.Obj}, P.hull.HomComplex X Y → Prop)
    (boundaries : ∀ {X Y : P.hull.Obj}, P.hull.HomComplex X Y → Prop)
    (quotientMap : ∀ {X Y : P.hull.Obj}, P.hull.HomComplex X Y → Hom X Y)
    (quotientMapRespectsCycles : Prop)
    (quotientMapKillsBoundaries : Prop)
    (toH0Functor : Prop)
    (distinguishedTriangles : Prop)
    (triangulatedAxioms : Prop)
    (localizationAtAcyclics : Prop)
    (quotientMapRespectsCycles_holds : quotientMapRespectsCycles)
    (quotientMapKillsBoundaries_holds : quotientMapKillsBoundaries)
    (toH0Functor_holds : toH0Functor)
    (distinguishedTriangles_holds : distinguishedTriangles)
    (triangulatedAxioms_holds : triangulatedAxioms)
    (localizationAtAcyclics_holds : localizationAtAcyclics) :
    (ofData P Hom id comp cycles boundaries quotientMap
      quotientMapRespectsCycles quotientMapKillsBoundaries toH0Functor
      distinguishedTriangles triangulatedAxioms localizationAtAcyclics
      quotientMapRespectsCycles_holds quotientMapKillsBoundaries_holds
      toH0Functor_holds distinguishedTriangles_holds
      triangulatedAxioms_holds localizationAtAcyclics_holds).triangulatedData =
      { distinguishedTriangles := distinguishedTriangles
        triangulatedAxioms := triangulatedAxioms
        localizationAtAcyclics := localizationAtAcyclics
        distinguishedTriangles_holds := distinguishedTriangles_holds
        triangulatedAxioms_holds := triangulatedAxioms_holds
        localizationAtAcyclics_holds := localizationAtAcyclics_holds } := by
  rfl

@[simp] theorem existenceTarget_iff {C : DGCategoryLike.{u, v}}
    {P : PretriangulatedHull C} (H : H0Category P) :
    H.existenceTarget :=
  H.existenceTarget_holds

@[simp] theorem distinguishedTrianglesTarget_iff {C : DGCategoryLike.{u, v}}
    {P : PretriangulatedHull C} (H : H0Category P) :
    H.distinguishedTrianglesTarget :=
  H.distinguishedTrianglesTarget_holds

@[simp] theorem triangulatedAxiomsTarget_iff {C : DGCategoryLike.{u, v}}
    {P : PretriangulatedHull C} (H : H0Category P) :
    H.triangulatedAxiomsTarget :=
  H.triangulatedAxiomsTarget_holds

@[simp] theorem localizationAtAcyclicsTarget_iff {C : DGCategoryLike.{u, v}}
    {P : PretriangulatedHull C} (H : H0Category P) :
    H.localizationAtAcyclicsTarget :=
  H.localizationAtAcyclicsTarget_holds

end H0Category

end CategoryInfra
end TraceCalc