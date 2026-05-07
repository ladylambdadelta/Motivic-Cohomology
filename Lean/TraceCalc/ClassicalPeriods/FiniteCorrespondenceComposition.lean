import TraceCalc.ClassicalPeriods.FiniteCorrespondenceIdentity

noncomputable section

namespace TraceCalc
namespace ClassicalPeriods
namespace Wall10A

namespace SchemeOverQ

inductive FiniteCorrespondenceCompositionExpr : SchemeOverQ → SchemeOverQ → Type 1
  | atom {X Y : SchemeOverQ} (a : ConcreteFiniteCorrespondence X Y) :
      FiniteCorrespondenceCompositionExpr X Y
  | identity (X : SchemeOverQ) : FiniteCorrespondenceCompositionExpr X X
  | comp {X Y Z : SchemeOverQ}
      (a : FiniteCorrespondenceCompositionExpr X Y)
      (b : FiniteCorrespondenceCompositionExpr Y Z) :
      FiniteCorrespondenceCompositionExpr X Z

inductive FiniteCorrespondenceCompositionSpine : SchemeOverQ → SchemeOverQ → Type 1
  | nil (X : SchemeOverQ) : FiniteCorrespondenceCompositionSpine X X
  | cons {X Y Z : SchemeOverQ}
      (head : ConcreteFiniteCorrespondence X Y)
      (tail : FiniteCorrespondenceCompositionSpine Y Z) :
      FiniteCorrespondenceCompositionSpine X Z

namespace FiniteCorrespondenceCompositionSpine

def append : {X Y Z : SchemeOverQ} →
    FiniteCorrespondenceCompositionSpine X Y →
    FiniteCorrespondenceCompositionSpine Y Z →
    FiniteCorrespondenceCompositionSpine X Z
  | _, _, _, nil _, right => right
  | _, _, _, cons head tail, right => cons head (append tail right)

@[simp]
theorem append_nil {X Y : SchemeOverQ}
    (spine : FiniteCorrespondenceCompositionSpine X Y) :
    append spine (nil Y) = spine := by
  induction spine with
  | nil X => rfl
  | cons head tail ih => simp [append, ih]

@[simp]
theorem nil_append {X Y : SchemeOverQ}
    (spine : FiniteCorrespondenceCompositionSpine X Y) :
    append (nil X) spine = spine := by
  rfl

@[simp]
theorem append_assoc {W X Y Z : SchemeOverQ}
    (a : FiniteCorrespondenceCompositionSpine W X)
    (b : FiniteCorrespondenceCompositionSpine X Y)
    (c : FiniteCorrespondenceCompositionSpine Y Z) :
    append (append a b) c = append a (append b c) := by
  induction a with
  | nil W => rfl
  | cons head tail ih => simp [append, ih]

def rebuild : {X Y : SchemeOverQ} →
    FiniteCorrespondenceCompositionSpine X Y → FiniteCorrespondenceCompositionExpr X Y
  | X, _, nil _ => FiniteCorrespondenceCompositionExpr.identity X
  | _, _, cons head (nil _) => FiniteCorrespondenceCompositionExpr.atom head
  | _, _, cons head tail => FiniteCorrespondenceCompositionExpr.comp
      (FiniteCorrespondenceCompositionExpr.atom head) (rebuild tail)

end FiniteCorrespondenceCompositionSpine

structure FiniteCorrespondenceCompositionNF (X Y : SchemeOverQ) where
  expr : FiniteCorrespondenceCompositionExpr X Y

namespace FiniteCorrespondenceCompositionNF

def ofCorrespondence {X Y : SchemeOverQ} (a : ConcreteFiniteCorrespondence X Y) :
    FiniteCorrespondenceCompositionNF X Y where
  expr := FiniteCorrespondenceCompositionExpr.atom a

def identity {X : SchemeOverQ} : FiniteCorrespondenceCompositionNF X X where
  expr := FiniteCorrespondenceCompositionExpr.identity X

def comp {X Y Z : SchemeOverQ}
    (a : FiniteCorrespondenceCompositionNF X Y)
    (b : FiniteCorrespondenceCompositionNF Y Z) : FiniteCorrespondenceCompositionNF X Z where
  expr := FiniteCorrespondenceCompositionExpr.comp a.expr b.expr

end FiniteCorrespondenceCompositionNF

namespace FiniteCorrespondenceCompositionExpr

def flatten : {X Y : SchemeOverQ} →
    FiniteCorrespondenceCompositionExpr X Y → FiniteCorrespondenceCompositionSpine X Y
  | _, _, atom a => FiniteCorrespondenceCompositionSpine.cons a (FiniteCorrespondenceCompositionSpine.nil _)
  | X, _, identity _ => FiniteCorrespondenceCompositionSpine.nil X
  | _, _, comp a b => FiniteCorrespondenceCompositionSpine.append (flatten a) (flatten b)

def normalize : {X Y : SchemeOverQ} →
    FiniteCorrespondenceCompositionExpr X Y → FiniteCorrespondenceCompositionExpr X Y
  | _, _, expr => FiniteCorrespondenceCompositionSpine.rebuild (flatten expr)

@[simp]
theorem normalize_comp_left_identity {X Y : SchemeOverQ}
    (e : FiniteCorrespondenceCompositionExpr X Y) :
  normalize (comp (identity X) e) = normalize e := by
  rfl

@[simp]
theorem normalize_comp_right_identity {X Y : SchemeOverQ}
    (e : FiniteCorrespondenceCompositionExpr X Y) :
  normalize (comp e (identity Y)) = normalize e := by
  simp [normalize, flatten]

@[simp]
theorem flatten_comp_assoc {W X Y Z : SchemeOverQ}
    (a : FiniteCorrespondenceCompositionExpr W X)
    (b : FiniteCorrespondenceCompositionExpr X Y)
    (c : FiniteCorrespondenceCompositionExpr Y Z) :
    flatten (comp (comp a b) c) = flatten (comp a (comp b c)) := by
  simp [flatten, FiniteCorrespondenceCompositionSpine.append_assoc]

@[simp]
theorem normalize_comp_assoc {W X Y Z : SchemeOverQ}
    (a : FiniteCorrespondenceCompositionExpr W X)
    (b : FiniteCorrespondenceCompositionExpr X Y)
    (c : FiniteCorrespondenceCompositionExpr Y Z) :
    normalize (comp (comp a b) c) = normalize (comp a (comp b c)) := by
  simp [normalize]

  @[simp]
  theorem flatten_rebuild {X Y : SchemeOverQ}
    (spine : FiniteCorrespondenceCompositionSpine X Y) :
    flatten (FiniteCorrespondenceCompositionSpine.rebuild spine) = spine := by
    induction spine with
    | nil X => rfl
    | cons head tail ih =>
      cases tail with
      | nil Y => rfl
      | cons next rest =>
          simp [FiniteCorrespondenceCompositionSpine.rebuild, flatten,
        FiniteCorrespondenceCompositionSpine.append, ih]

end FiniteCorrespondenceCompositionExpr

namespace FiniteCorrespondenceCompositionNF

def ofExprNormalize {X Y : SchemeOverQ} (e : FiniteCorrespondenceCompositionExpr X Y) :
    FiniteCorrespondenceCompositionNF X Y where
  expr := FiniteCorrespondenceCompositionExpr.normalize e

def compNormalized {X Y Z : SchemeOverQ}
    (a : FiniteCorrespondenceCompositionNF X Y)
    (b : FiniteCorrespondenceCompositionNF Y Z) : FiniteCorrespondenceCompositionNF X Z :=
  ofExprNormalize (FiniteCorrespondenceCompositionExpr.comp a.expr b.expr)

@[simp]
theorem ofExprNormalize_left_identity {X Y : SchemeOverQ}
    (a : FiniteCorrespondenceCompositionNF X Y) :
  ofExprNormalize (FiniteCorrespondenceCompositionExpr.comp
    (FiniteCorrespondenceCompositionExpr.identity X) a.expr) =
      ofExprNormalize a.expr := by
  cases a
  simp [ofExprNormalize, FiniteCorrespondenceCompositionExpr.normalize_comp_left_identity]

@[simp]
theorem ofExprNormalize_right_identity {X Y : SchemeOverQ}
    (a : FiniteCorrespondenceCompositionNF X Y) :
  ofExprNormalize (FiniteCorrespondenceCompositionExpr.comp a.expr
    (FiniteCorrespondenceCompositionExpr.identity Y)) =
      ofExprNormalize a.expr := by
  cases a
  simp [ofExprNormalize, FiniteCorrespondenceCompositionExpr.normalize_comp_right_identity]

@[simp]
theorem ofExprNormalize_assoc {W X Y Z : SchemeOverQ}
    (a : FiniteCorrespondenceCompositionNF W X)
    (b : FiniteCorrespondenceCompositionNF X Y)
    (c : FiniteCorrespondenceCompositionNF Y Z) :
  ofExprNormalize (FiniteCorrespondenceCompositionExpr.comp
      (FiniteCorrespondenceCompositionExpr.comp a.expr b.expr) c.expr) =
    ofExprNormalize (FiniteCorrespondenceCompositionExpr.comp a.expr
      (FiniteCorrespondenceCompositionExpr.comp b.expr c.expr)) := by
  cases a
  cases b
  cases c
  simp [ofExprNormalize, FiniteCorrespondenceCompositionExpr.normalize_comp_assoc]

@[simp]
theorem compNormalized_assoc {W X Y Z : SchemeOverQ}
    (a : FiniteCorrespondenceCompositionNF W X)
    (b : FiniteCorrespondenceCompositionNF X Y)
    (c : FiniteCorrespondenceCompositionNF Y Z) :
    compNormalized (compNormalized a b) c = compNormalized a (compNormalized b c) := by
  cases a
  cases b
  cases c
  simp [compNormalized, ofExprNormalize, FiniteCorrespondenceCompositionExpr.normalize,
    FiniteCorrespondenceCompositionExpr.flatten,
    FiniteCorrespondenceCompositionSpine.append_assoc]

end FiniteCorrespondenceCompositionNF

structure CorrespondenceCompositionData where
  normalize : ∀ {X Y : SchemeOverQ},
    ConcreteFiniteCorrespondence X Y → FiniteCorrespondenceCompositionNF X Y
  realize : ∀ {X Y : SchemeOverQ},
    FiniteCorrespondenceCompositionNF X Y → ConcreteFiniteCorrespondence X Y
  normalize_realize : ∀ {X Y : SchemeOverQ} (a : ConcreteFiniteCorrespondence X Y),
    realize (normalize a) = a
  normalize_realize_nf : ∀ {X Y : SchemeOverQ} (a : FiniteCorrespondenceCompositionNF X Y),
    normalize (realize a) = a
  normalize_identity : ∀ {X : SchemeOverQ} (D : DiagonalFiniteCorrespondenceData X),
    normalize (ConcreteFiniteCorrespondence.identity D) = FiniteCorrespondenceCompositionNF.identity
  compose : ∀ {X Y Z : SchemeOverQ},
    ConcreteFiniteCorrespondence X Y →
    ConcreteFiniteCorrespondence Y Z →
    ConcreteFiniteCorrespondence X Z
  compose_eq_normal_form : ∀ {X Y Z : SchemeOverQ}
    (a : ConcreteFiniteCorrespondence X Y) (b : ConcreteFiniteCorrespondence Y Z),
    compose a b = realize (FiniteCorrespondenceCompositionNF.compNormalized (normalize a) (normalize b))
  realize_nf_left_identity : ∀ {X Y : SchemeOverQ}
    (a : FiniteCorrespondenceCompositionNF X Y),
    realize (FiniteCorrespondenceCompositionNF.compNormalized FiniteCorrespondenceCompositionNF.identity a) = realize a
  realize_nf_right_identity : ∀ {X Y : SchemeOverQ}
    (a : FiniteCorrespondenceCompositionNF X Y),
    realize (FiniteCorrespondenceCompositionNF.compNormalized a FiniteCorrespondenceCompositionNF.identity) = realize a
  diagonal_left_is_empty : ∀ {X : SchemeOverQ} (D : DiagonalFiniteCorrespondenceData X),
    (ConcreteFiniteCorrespondence.identity D).cycle = FiniteCorrespondenceCycle.zero X X
  compose_with_left_identity_cycle : ∀ {X Y : SchemeOverQ}
    (D : DiagonalFiniteCorrespondenceData X) (a : ConcreteFiniteCorrespondence X Y),
    compose (ConcreteFiniteCorrespondence.identity D) a = a
  diagonal_right_is_empty : ∀ {Y : SchemeOverQ} (D : DiagonalFiniteCorrespondenceData Y),
    (ConcreteFiniteCorrespondence.identity D).cycle = FiniteCorrespondenceCycle.zero Y Y
  compose_with_right_identity_cycle : ∀ {X Y : SchemeOverQ}
    (a : ConcreteFiniteCorrespondence X Y) (D : DiagonalFiniteCorrespondenceData Y),
    compose a (ConcreteFiniteCorrespondence.identity D) = a
  compose_add_left : ∀ {X Y Z : SchemeOverQ}
    (a b : ConcreteFiniteCorrespondence X Y) (c : ConcreteFiniteCorrespondence Y Z),
    compose (ConcreteFiniteCorrespondence.add a b) c =
      ConcreteFiniteCorrespondence.add (compose a c) (compose b c)
  compose_add_right : ∀ {X Y Z : SchemeOverQ}
    (a : ConcreteFiniteCorrespondence X Y) (b c : ConcreteFiniteCorrespondence Y Z),
    compose a (ConcreteFiniteCorrespondence.add b c) =
      ConcreteFiniteCorrespondence.add (compose a b) (compose a c)
  generator_support_is_projection_intersection :
    ∀ {X Y Z : SchemeOverQ}
      (_a : FiniteCorrespondenceGenerator X Y) (_b : FiniteCorrespondenceGenerator Y Z), Prop
  generator_composition_finite_over_source :
    ∀ {X Y Z : SchemeOverQ}
      (_a : FiniteCorrespondenceGenerator X Y) (_b : FiniteCorrespondenceGenerator Y Z), Prop

namespace CorrespondenceCompositionData

def composeCycle (C : CorrespondenceCompositionData) {X Y Z : SchemeOverQ}
    (a : ConcreteFiniteCorrespondence X Y) (b : ConcreteFiniteCorrespondence Y Z) :
    ConcreteFiniteCorrespondence X Z :=
  C.compose a b

theorem compose_left_identity (C : CorrespondenceCompositionData)
    {X Y : SchemeOverQ} (D : DiagonalFiniteCorrespondenceData X)
    (a : ConcreteFiniteCorrespondence X Y) :
    C.compose (ConcreteFiniteCorrespondence.identity D) a = a := by
  rw [C.compose_eq_normal_form]
  rw [C.normalize_identity D]
  rw [C.realize_nf_left_identity]
  exact C.normalize_realize a

theorem compose_right_identity (C : CorrespondenceCompositionData)
    {X Y : SchemeOverQ} (a : ConcreteFiniteCorrespondence X Y)
    (D : DiagonalFiniteCorrespondenceData Y) :
    C.compose a (ConcreteFiniteCorrespondence.identity D) = a := by
  rw [C.compose_eq_normal_form]
  rw [C.normalize_identity D]
  rw [C.realize_nf_right_identity]
  exact C.normalize_realize a

theorem compose_assoc (C : CorrespondenceCompositionData)
    {W X Y Z : SchemeOverQ}
    (a : ConcreteFiniteCorrespondence W X)
    (b : ConcreteFiniteCorrespondence X Y)
    (c : ConcreteFiniteCorrespondence Y Z) :
    C.compose (C.compose a b) c = C.compose a (C.compose b c) := by
  rw [C.compose_eq_normal_form]
  rw [C.compose_eq_normal_form]
  rw [C.compose_eq_normal_form]
  rw [C.compose_eq_normal_form]
  rw [C.normalize_realize_nf]
  rw [C.normalize_realize_nf]
  have h := FiniteCorrespondenceCompositionNF.compNormalized_assoc
    (C.normalize a) (C.normalize b) (C.normalize c)
  change C.realize (FiniteCorrespondenceCompositionNF.compNormalized
      (FiniteCorrespondenceCompositionNF.compNormalized (C.normalize a) (C.normalize b)) (C.normalize c)) =
    C.realize (FiniteCorrespondenceCompositionNF.compNormalized (C.normalize a)
      (FiniteCorrespondenceCompositionNF.compNormalized (C.normalize b) (C.normalize c)))
  rw [h]

end CorrespondenceCompositionData
end SchemeOverQ
end Wall10A
end ClassicalPeriods
end TraceCalc
