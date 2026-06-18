import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.MeasureTheory.Integral.SetIntegral
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaFiniteHoleSubdivision

/-!
# Foundation lemmas for endpoint cap-collar Cauchy balances

Generic algebraic lemmas for AddCommGroup, specialized to Complex.

Strategy: generic lemmas work for any AddCommGroup, then specialize to ℂ with thin wrappers.
This dramatically reduces the lemma count from ~92 to ~20 generic + 15 specializations.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology
open MeasureTheory

notation:max "[[" a "," b "]]" => Set.Icc a b

/-! ## Generic AddCommGroup Rearrangements -/

/-- Commutativity. -/
theorem add_comm_2 {α : Type*} [AddCommGroup α] (a b : α) : a + b = b + a :=
  add_comm a b

/-- Left-associative three-term sum. -/
theorem add_assoc_3 {α : Type*} [AddCommGroup α] (a b c : α) : a + b + c = a + (b + c) :=
  add_assoc a b c

/-- Right-associative three-term sum. -/
theorem add_assoc_3_symm {α : Type*} [AddCommGroup α] (a b c : α) : a + (b + c) = a + b + c :=
  (add_assoc a b c).symm

/-- Swap middle two terms in three-term sum. -/
theorem add_swap_middle {α : Type*} [AddCommGroup α] (a b c : α) : a + b + c = a + c + b :=
  Eq.trans (add_assoc_3 a b c)
    (Eq.trans (congrArg (fun x => a + x) (add_comm b c)) (add_assoc_3_symm a c b))

/-- Move term e past three terms b, c, d by repeated swapping.
This proof chains: move e past d, then past c, then past b. -/
theorem add_six_rearrange {α : Type*} [AddCommGroup α] (a b c d e f : α) :
    a + b + c + d + e + f = a + e + c + b + d + f :=
  let eq1 : a + b + c + d + e + f = a + b + c + e + d + f :=
    congrArg (· + f) (add_swap_middle (a + b + c) d e)
  let eq2 : a + b + c + e + d + f = a + b + e + c + d + f :=
    congrArg (fun x => x + d + f) (add_swap_middle (a + b) c e)
  let eq3 : a + b + e + c + d + f = a + e + b + c + d + f :=
    congrArg (fun x => x + c + d + f) (add_swap_middle a b e)
  let eq4 : a + e + b + c + d + f = a + e + c + b + d + f :=
    congrArg (fun x => x + d + f) (add_swap_middle (a + e) b c)
  Eq.trans eq1 (Eq.trans eq2 (Eq.trans eq3 eq4))

/-- Distribution of multiplication over addition. -/
theorem mul_add_dist_2 {α : Type*} [Ring α] (r a b : α) : r * a + r * b = r * (a + b) :=
  (mul_add r a b).symm

/-- Distribution of multiplication over three summands. -/
theorem mul_add_dist_3 {α : Type*} [Ring α] (r a b c : α) : r * a + r * b + r * c = r * (a + b + c) :=
  Eq.trans (congrArg (· + r * c) (mul_add_dist_2 r a b)) (mul_add_dist_2 r (a + b) c)

/-- Negation distributes over sum. -/
theorem neg_add_dist {α : Type*} [AddCommGroup α] (a b : α) : (-a) + (-b) = -(a + b) :=
  Eq.trans (add_comm (-a) (-b)) ((neg_add_rev a b).symm)

/-- Cancel outer terms: a + b + (-a) = b. -/
theorem add_cancel_outer {α : Type*} [AddCommGroup α] (a b : α) : a + b + (-a) = b :=
  let h1 : a + b + (-a) = a + (b + (-a)) := add_assoc a b (-a)
  let h2 : a + (b + (-a)) = a + ((-a) + b) := congrArg (a + ·) (add_comm b (-a))
  let h3 : a + ((-a) + b) = a + (-a) + b := (add_assoc a (-a) b).symm
  let h4 : a + (-a) + b = (0 : α) + b := congrArg (· + b) (add_neg_cancel a)
  let h5 : (0 : α) + b = b := zero_add b
  Eq.trans h1 (Eq.trans h2 (Eq.trans h3 (Eq.trans h4 h5)))

/-- Subtraction to negation. -/
theorem sub_eq_neg {α : Type*} [AddCommGroup α] (a b : α) : a - b = a + (-b) :=
  sub_eq_add_neg a b

/-- Negation of sum equals sum of negations. -/
theorem neg_sum_two {α : Type*} [AddCommGroup α] (a b : α) : -(a + b) = -a + (-b) :=
  neg_add a b

/-- Cancel identity for three terms. -/
theorem add_cancel_three {α : Type*} [AddCommGroup α] (a b : α) : a + b + (-a) = b :=
  add_cancel_outer a b

/-- Flatten an addition over a subtraction: `a + (b - c) = a + b - c`. -/
theorem add_sub_flat {α : Type*} [AddCommGroup α] (a b c : α) : a + (b - c) = a + b - c :=
  Eq.trans (congrArg (a + ·) (sub_eq_add_neg b c))
    (Eq.trans (add_assoc a b (-c)).symm (sub_eq_add_neg (a + b) c).symm)

/-- Cancel a subtracted term by re-adding it: `a - b + b = a`. -/
theorem sub_add_cancel_self {α : Type*} [AddCommGroup α] (a b : α) : a - b + b = a :=
  Eq.trans (congrArg (· + b) (sub_eq_add_neg a b))
    (Eq.trans (add_assoc a (-b) b)
      (Eq.trans (congrArg (a + ·) (neg_add_cancel b)) (add_zero a)))

/-- Generic eight-term reordering used to bring a flattened cap/collar sum into
its canonical oriented-boundary order.  Pure `add_swap_middle` bubbling. -/
theorem add_eight_to_canon {α : Type*} [AddCommGroup α]
    (p1 p2 p3 p4 p5 p6 p7 p8 : α) :
    p1 + p2 + p3 + p4 + p5 + p6 + p7 + p8 =
      p1 + p6 + p2 + p4 + p7 + p3 + p8 + p5 :=
  let sA := congrArg (fun w => w + p7 + p8) (add_swap_middle (p1 + p2 + p3 + p4) p5 p6)
  let sB := congrArg (fun w => w + p5 + p7 + p8) (add_swap_middle (p1 + p2 + p3) p4 p6)
  let sC := congrArg (fun w => w + p4 + p5 + p7 + p8) (add_swap_middle (p1 + p2) p3 p6)
  let sD := congrArg (fun w => w + p3 + p4 + p5 + p7 + p8) (add_swap_middle p1 p2 p6)
  let sE := congrArg (fun w => w + p5 + p7 + p8) (add_swap_middle (p1 + p6 + p2) p3 p4)
  let sF := congrArg (fun w => w + p8) (add_swap_middle (p1 + p6 + p2 + p4 + p3) p5 p7)
  let sG := congrArg (fun w => w + p5 + p8) (add_swap_middle (p1 + p6 + p2 + p4) p3 p7)
  let sH := add_swap_middle (p1 + p6 + p2 + p4 + p7 + p3) p5 p8
  Eq.trans sA (Eq.trans sB (Eq.trans sC (Eq.trans sD
    (Eq.trans sE (Eq.trans sF (Eq.trans sG sH))))))

/-- Generic cap/collar boundary collection: the two rectangular groups and the
deleted-disk group, with the two chords `l` and `c` cancelling, collapse to the
single oriented-boundary expression.  This is pure `AddCommGroup` rearrangement
and is shared by the left and right endpoint collars. -/
theorem add_collect_caps {α : Type*} [AddCommGroup α]
    (t u x₁ x₂ x₃ y₁ y₂ a l c : α) :
    (t - l + x₁ - y₁) + (c - u + x₂ - y₂) + (l - c + x₃ - a) =
      t - u + (x₁ + x₃ + x₂) - (y₁ + y₂) - a :=
  -- Normalise both sides to the flat all-`neg` canonical form
  --   t + -u + x₁ + x₃ + x₂ + -y₁ + -y₂ + -a.
  let canon : α := t + -u + x₁ + x₃ + x₂ + -y₁ + -y₂ + -a
  -- RHS = canon.
  let hRHS : t - u + (x₁ + x₃ + x₂) - (y₁ + y₂) - a = canon :=
    let r1 : t - u + (x₁ + x₃ + x₂) - (y₁ + y₂) - a
          = t - u + (x₁ + x₃ + x₂) + (-(y₁ + y₂)) - a :=
      congrArg (· - a) (sub_eq_add_neg (t - u + (x₁ + x₃ + x₂)) (y₁ + y₂))
    let r2 : t - u + (x₁ + x₃ + x₂) + (-(y₁ + y₂)) - a
          = t - u + (x₁ + x₃ + x₂) + (-(y₁ + y₂)) + (-a) :=
      sub_eq_add_neg (t - u + (x₁ + x₃ + x₂) + (-(y₁ + y₂))) a
    let r3 : t - u + (x₁ + x₃ + x₂) + (-(y₁ + y₂)) + (-a)
          = t - u + (x₁ + x₃ + x₂) + (-y₁ + -y₂) + (-a) :=
      congrArg (fun w => t - u + (x₁ + x₃ + x₂) + w + (-a)) (neg_add y₁ y₂)
    -- expand the `x` sum and the `t - u`
    let r4 : t - u + (x₁ + x₃ + x₂) + (-y₁ + -y₂) + (-a)
          = (t + -u) + (x₁ + x₃ + x₂) + (-y₁ + -y₂) + (-a) :=
      congrArg (fun w => w + (x₁ + x₃ + x₂) + (-y₁ + -y₂) + (-a)) (sub_eq_add_neg t u)
    let r5 : (t + -u) + (x₁ + x₃ + x₂) + (-y₁ + -y₂) + (-a)
          = (t + -u) + (x₁ + x₃) + x₂ + (-y₁ + -y₂) + (-a) :=
      congrArg (fun w => w + (-y₁ + -y₂) + (-a)) (add_assoc (t + -u) (x₁ + x₃) x₂).symm
    let r6 : (t + -u) + (x₁ + x₃) + x₂ + (-y₁ + -y₂) + (-a)
          = (t + -u) + x₁ + x₃ + x₂ + (-y₁ + -y₂) + (-a) :=
      congrArg (fun w => w + x₂ + (-y₁ + -y₂) + (-a)) (add_assoc (t + -u) x₁ x₃).symm
    let r7 : (t + -u) + x₁ + x₃ + x₂ + (-y₁ + -y₂) + (-a)
          = (t + -u) + x₁ + x₃ + x₂ + -y₁ + -y₂ + (-a) :=
      congrArg (· + (-a)) (add_assoc ((t + -u) + x₁ + x₃ + x₂) (-y₁) (-y₂)).symm
    Eq.trans r1 (Eq.trans r2 (Eq.trans r3 (Eq.trans r4 (Eq.trans r5 (Eq.trans r6 r7)))))
  -- LHS = canon.
  let hLHS : (t - l + x₁ - y₁) + (c - u + x₂ - y₂) + (l - c + x₃ - a) = canon :=
    -- swap the two trailing groups so the chord `l` meets `-l`
    let s0 : (t - l + x₁ - y₁) + (c - u + x₂ - y₂) + (l - c + x₃ - a)
          = (t - l + x₁ - y₁) + (l - c + x₃ - a) + (c - u + x₂ - y₂) :=
      add_swap_middle (t - l + x₁ - y₁) (c - u + x₂ - y₂) (l - c + x₃ - a)
    -- flatten `P + (l - c + x₃ - a)` and cancel `l`
    let P : α := t - l + x₁ - y₁
    let R : α := c - u + x₂ - y₂
    -- P + (l - c + x₃ - a) = P + l - c + x₃ - a
    let f1 : P + (l - c + x₃ - a) = P + l - c + x₃ - a :=
      let a1 : P + (l - c + x₃ - a) = P + (l - c + x₃) - a :=
        add_sub_flat P (l - c + x₃) a
      let a2 : P + (l - c + x₃) - a = (P + (l - c)) + x₃ - a :=
        congrArg (· - a) (add_assoc P (l - c) x₃).symm
      let a3 : (P + (l - c)) + x₃ - a = (P + l - c) + x₃ - a :=
        congrArg (fun w => w + x₃ - a) (add_sub_flat P l c)
      Eq.trans a1 (Eq.trans a2 a3)
    -- P + l = t + x₁ - y₁  (the `-l` cancels)
    let hPl : P + l = t + x₁ - y₁ :=
      let b0 : P + l = ((t - l) + x₁ + (-y₁)) + l :=
        congrArg (· + l) (sub_eq_add_neg ((t - l) + x₁) y₁)
      let b1 : ((t - l) + x₁ + (-y₁)) + l = ((t - l) + x₁ + l) + (-y₁) :=
        add_swap_middle ((t - l) + x₁) (-y₁) l
      let b2 : ((t - l) + x₁ + l) + (-y₁) = ((t - l) + l + x₁) + (-y₁) :=
        congrArg (· + (-y₁)) (add_swap_middle (t - l) x₁ l)
      let b3 : ((t - l) + l + x₁) + (-y₁) = (t + x₁) + (-y₁) :=
        congrArg (fun w => w + x₁ + (-y₁)) (sub_add_cancel_self t l)
      let b4 : (t + x₁) + (-y₁) = t + x₁ - y₁ := (sub_eq_add_neg (t + x₁) y₁).symm
      Eq.trans b0 (Eq.trans b1 (Eq.trans b2 (Eq.trans b3 b4)))
    -- assemble: P + l - c + x₃ - a = (t + x₁ - y₁) - c + x₃ - a
    let f2 : P + l - c + x₃ - a = (t + x₁ - y₁) - c + x₃ - a :=
      congrArg (fun w => w - c + x₃ - a) hPl
    let hPR : P + (l - c + x₃ - a) = (t + x₁ - y₁) - c + x₃ - a := Eq.trans f1 f2
    -- now add R and cancel `c`
    let s1 : (t - l + x₁ - y₁) + (l - c + x₃ - a) + (c - u + x₂ - y₂)
          = ((t + x₁ - y₁) - c + x₃ - a) + (c - u + x₂ - y₂) :=
      congrArg (· + R) hPR
    -- D := (t + x₁ - y₁) - c + x₃ - a ; flatten D + R and cancel c
    let D : α := (t + x₁ - y₁) - c + x₃ - a
    -- D + (c - u + x₂ - y₂) = D + c - u + x₂ - y₂
    let g1 : D + (c - u + x₂ - y₂) = D + c - u + x₂ - y₂ :=
      let c1 : D + (c - u + x₂ - y₂) = D + (c - u + x₂) - y₂ :=
        add_sub_flat D (c - u + x₂) y₂
      let c2 : D + (c - u + x₂) - y₂ = (D + (c - u)) + x₂ - y₂ :=
        congrArg (· - y₂) (add_assoc D (c - u) x₂).symm
      let c3 : (D + (c - u)) + x₂ - y₂ = (D + c - u) + x₂ - y₂ :=
        congrArg (fun w => w + x₂ - y₂) (add_sub_flat D c u)
      Eq.trans c1 (Eq.trans c2 c3)
    -- D + c = t + x₁ - y₁ + x₃ - a  (the `-c` cancels)
    let hDc : D + c = t + x₁ - y₁ + x₃ - a :=
      -- D = ((t + x₁ - y₁) - c + x₃) - a
      let d0 : D + c = (((t + x₁ - y₁) - c + x₃) + (-a)) + c :=
        congrArg (· + c) (sub_eq_add_neg ((t + x₁ - y₁) - c + x₃) a)
      let d1 : (((t + x₁ - y₁) - c + x₃) + (-a)) + c
            = (((t + x₁ - y₁) - c + x₃) + c) + (-a) :=
        add_swap_middle ((t + x₁ - y₁) - c + x₃) (-a) c
      let d2 : (((t + x₁ - y₁) - c + x₃) + c) + (-a)
            = (((t + x₁ - y₁) - c) + c + x₃) + (-a) :=
        congrArg (· + (-a)) (add_swap_middle ((t + x₁ - y₁) - c) x₃ c)
      let d3 : (((t + x₁ - y₁) - c) + c + x₃) + (-a)
            = ((t + x₁ - y₁) + x₃) + (-a) :=
        congrArg (fun w => w + x₃ + (-a)) (sub_add_cancel_self (t + x₁ - y₁) c)
      let d4 : ((t + x₁ - y₁) + x₃) + (-a) = t + x₁ - y₁ + x₃ - a :=
        (sub_eq_add_neg ((t + x₁ - y₁) + x₃) a).symm
      Eq.trans d0 (Eq.trans d1 (Eq.trans d2 (Eq.trans d3 d4)))
    let g2 : D + c - u + x₂ - y₂ = (t + x₁ - y₁ + x₃ - a) - u + x₂ - y₂ :=
      congrArg (fun w => w - u + x₂ - y₂) hDc
    let hDR : D + (c - u + x₂ - y₂) = (t + x₁ - y₁ + x₃ - a) - u + x₂ - y₂ :=
      Eq.trans g1 g2
    -- E := (t + x₁ - y₁ + x₃ - a) - u + x₂ - y₂ ; reorder to canon
    let E : α := (t + x₁ - y₁ + x₃ - a) - u + x₂ - y₂
    -- fully expand E into +neg flat form and reorder atoms to canon order
    -- atoms of E (in order): t, x₁, -y₁, x₃, -a, -u, x₂, -y₂
    -- canon order:            t, -u, x₁, x₃, x₂, -y₁, -y₂, -a
    let hE : E = canon :=
      -- expand all subtractions
      let e1 : E = ((((((t + x₁ + (-y₁) + x₃ + (-a)) + (-u)) + x₂) + (-y₂))) ) :=
        let p1 : (t + x₁ - y₁ + x₃ - a) = t + x₁ + (-y₁) + x₃ + (-a) :=
          let q1 : t + x₁ - y₁ + x₃ - a = (t + x₁ - y₁ + x₃) + (-a) :=
            sub_eq_add_neg (t + x₁ - y₁ + x₃) a
          let q2 : (t + x₁ - y₁ + x₃) + (-a) = ((t + x₁ + (-y₁)) + x₃) + (-a) :=
            congrArg (fun w => w + x₃ + (-a)) (sub_eq_add_neg (t + x₁) y₁)
          Eq.trans q1 q2
        let p2 : E = ((t + x₁ + (-y₁) + x₃ + (-a)) - u + x₂ - y₂) :=
          congrArg (fun w => w - u + x₂ - y₂) p1
        let p3 : (t + x₁ + (-y₁) + x₃ + (-a)) - u + x₂ - y₂
              = (t + x₁ + (-y₁) + x₃ + (-a)) + (-u) + x₂ + (-y₂) :=
          let w1 : (t + x₁ + (-y₁) + x₃ + (-a)) - u + x₂ - y₂
                = (t + x₁ + (-y₁) + x₃ + (-a)) - u + x₂ + (-y₂) :=
            sub_eq_add_neg ((t + x₁ + (-y₁) + x₃ + (-a)) - u + x₂) y₂
          let w2 : (t + x₁ + (-y₁) + x₃ + (-a)) - u + x₂ + (-y₂)
                = (t + x₁ + (-y₁) + x₃ + (-a)) + (-u) + x₂ + (-y₂) :=
            congrArg (fun w => w + x₂ + (-y₂)) (sub_eq_add_neg (t + x₁ + (-y₁) + x₃ + (-a)) u)
          Eq.trans w1 w2
        Eq.trans p2 p3
      -- Now E = t + x₁ + -y₁ + x₃ + -a + -u + x₂ + -y₂  (left assoc, 8 atoms)
      -- reorder to canon = t + -u + x₁ + x₃ + x₂ + -y₁ + -y₂ + -a
      -- use add_eight_rearrange (proved below)
      Eq.trans e1
        (add_eight_to_canon t x₁ (-y₁) x₃ (-a) (-u) x₂ (-y₂))
    Eq.trans s0 (Eq.trans s1 (Eq.trans hDR hE))
  Eq.trans hLHS hRHS.symm

/-! ## Complex-Specific Lemmas -/

/-- Left distributivity two-term. -/
theorem Complex.left_mul_add_two_collect (a b c : ℂ) : a * b + a * c = a * (b + c) :=
  mul_add_dist_2 a b c

/-- Left distributivity three-term. -/
theorem Complex.left_mul_add_three_collect (a b c d : ℂ) : a * b + a * c + a * d = a * (b + c + d) :=
  mul_add_dist_3 a b c d

/-- Group I*safe terms. -/
theorem Complex.boundaryGroupISafeTerms (s₁ s₂ s₃ : ℂ) :
    Complex.I * s₁ + Complex.I * s₂ + Complex.I * s₃ = Complex.I * (s₁ + s₂ + s₃) :=
  Complex.left_mul_add_three_collect Complex.I s₁ s₂ s₃

/-- Group I*pv terms. -/
theorem Complex.boundaryGroupIPvTerms (p₁ p₂ : ℂ) :
    Complex.I * p₁ + Complex.I * p₂ = Complex.I * (p₁ + p₂) :=
  Complex.left_mul_add_two_collect Complex.I p₁ p₂

/-- Swap middle two. -/
theorem Complex.add_swap_middle (a b c : ℂ) : a + b + c = a + c + b :=
  _root_.Boundary.LFunctions.add_swap_middle a b c

/-- Six-term rearrange. -/
theorem Complex.six_term_center_move (a b c d e f : ℂ) : a + b + c + d + e + f = a + e + c + b + d + f :=
  add_six_rearrange a b c d e f

/-- Negation over sum. -/
theorem Complex.neg_dist_add (a b : ℂ) : (-a) + (-b) = -(a + b) :=
  neg_add_dist a b

/-- Cancel outer chord terms. -/
theorem Complex.add_chords_cancel (u l : ℂ) : u + l + (-u) = l :=
  add_cancel_outer u l

/-- Helper: A + (B - A) = B. -/
theorem add_sub_self {α : Type*} [AddCommGroup α] (A B : α) : A + (B - A) = B :=
  let h1 : A + (B - A) = A + (B + (-A)) := congrArg (A + ·) (sub_eq_add_neg B A)
  let h2 : A + (B + (-A)) = A + ((-A) + B) := congrArg (A + ·) (add_comm B (-A))
  let h3 : A + ((-A) + B) = A + (-A) + B := (add_assoc A (-A) B).symm
  let h4 : A + (-A) + B = (0 : α) + B := congrArg (· + B) (add_neg_cancel A)
  let h5 : (0 : α) + B = B := zero_add B
  Eq.trans h1 (Eq.trans h2 (Eq.trans h3 (Eq.trans h4 h5)))

/-- Basic cancellation: A + (B - A) - B = 0. -/
theorem Complex.finiteAbelPlana_log_verticalStrip_add_deleted_sub_verticalStrip_sub_deleted (A B : ℂ) :
    A + (B - A) - B = 0 :=
  calc A + (B - A) - B
    _ = B - B := congrArg (· - B) (add_sub_self A B)
    _ = 0 := sub_self B

/-- Flatten nested additions. -/
theorem Complex.leftEndpointCapCollarBoundary_flatten
    (t l u c s₁ s₂ s₃ p₁ p₂ a : ℂ) :
    (t - l + Complex.I * s₁ - Complex.I * p₁) +
        (c - u + Complex.I * s₃ - Complex.I * p₂) +
          (l - c + Complex.I * s₂ - a) =
      t - l + Complex.I * s₁ - Complex.I * p₁ +
        c - u + Complex.I * s₃ - Complex.I * p₂ +
        l - c + Complex.I * s₂ - a :=
  let G1 := t - l + Complex.I * s₁ - Complex.I * p₁
  let F := G1 + c - u + Complex.I * s₃ - Complex.I * p₂
  -- Flatten the second group `G2 = (c - u + I*s₃) - I*p₂` onto `G1`.
  let a1 : G1 + (c - u + Complex.I * s₃ - Complex.I * p₂)
        = (G1 + (c - u + Complex.I * s₃)) - Complex.I * p₂ :=
    add_sub_flat G1 (c - u + Complex.I * s₃) (Complex.I * p₂)
  let b1 : (G1 + (c - u + Complex.I * s₃)) - Complex.I * p₂
        = (G1 + (c - u) + Complex.I * s₃) - Complex.I * p₂ :=
    congrArg (· - Complex.I * p₂) (add_assoc G1 (c - u) (Complex.I * s₃)).symm
  let c1 : (G1 + (c - u) + Complex.I * s₃) - Complex.I * p₂ = F :=
    congrArg (fun y => (y + Complex.I * s₃) - Complex.I * p₂) (add_sub_flat G1 c u)
  let g1 : G1 + (c - u + Complex.I * s₃ - Complex.I * p₂) = F :=
    Eq.trans a1 (Eq.trans b1 c1)
  -- Flatten the third group `G3 = (l - c + I*s₂) - a` onto `F`.
  let a2 : F + (l - c + Complex.I * s₂ - a)
        = (F + (l - c + Complex.I * s₂)) - a :=
    add_sub_flat F (l - c + Complex.I * s₂) a
  let b2 : (F + (l - c + Complex.I * s₂)) - a
        = (F + (l - c) + Complex.I * s₂) - a :=
    congrArg (· - a) (add_assoc F (l - c) (Complex.I * s₂)).symm
  let c2 : (F + (l - c) + Complex.I * s₂) - a
        = F + l - c + Complex.I * s₂ - a :=
    congrArg (fun y => (y + Complex.I * s₂) - a) (add_sub_flat F l c)
  let g2 : F + (l - c + Complex.I * s₂ - a) = F + l - c + Complex.I * s₂ - a :=
    Eq.trans a2 (Eq.trans b2 c2)
  Eq.trans (congrArg (· + (l - c + Complex.I * s₂ - a)) g1) g2

/-- Chord cancellation in sum. -/
theorem Complex.boundaryChordsCancelInSum (l c r : ℂ) :
    (-l + r + c) + l - c = r :=
  let e0 : (-l + r + c) + l - c = (-l + r + c) + l + (-c) :=
    sub_eq_add_neg ((-l + r + c) + l) c
  let e1 : (-l + r + c) + l + (-c) = ((-l + r) + l + c) + (-c) :=
    congrArg (· + (-c)) (add_swap_middle (-l + r) c l)
  let e2 : ((-l + r) + l + c) + (-c) = (((-l) + l + r) + c) + (-c) :=
    congrArg (fun x => x + c + (-c)) (add_swap_middle (-l) r l)
  let e3 : (((-l) + l + r) + c) + (-c) = ((0 + r) + c) + (-c) :=
    congrArg (fun x => x + r + c + (-c)) (neg_add_cancel l)
  let e4 : ((0 + r) + c) + (-c) = (r + c) + (-c) :=
    congrArg (fun x => x + c + (-c)) (zero_add r)
  let e5 : (r + c) + (-c) = r := add_neg_cancel_right r c
  Eq.trans e0 (Eq.trans e1 (Eq.trans e2 (Eq.trans e3 (Eq.trans e4 e5))))

/-! ## Real-Theoretic Lemmas -/

/-- Positive nat ≥ 1 in ℝ. -/
theorem Real.one_le_natCast_of_pos {m : ℕ} (hm : 0 < m) : (1 : ℝ) ≤ (m : ℝ) :=
  by exact_mod_cast Nat.succ_le_iff.mpr hm

/-- Succ nat ≥ 1 in ℝ. -/
theorem Real.one_le_natCast_succ (N : ℕ) : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) :=
  by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)

/-- Nat order to ℝ. -/
theorem Real.natCast_le_natCast {m N : ℕ} (h : m ≤ N) : (m : ℝ) ≤ (N : ℝ) :=
  (Nat.cast_le : ((m : ℝ) ≤ (N : ℝ) ↔ m ≤ N)).mpr h

/-- Succ coercion. -/
theorem Real.natCast_succ_eq (N : ℕ) : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 :=
  Nat.cast_succ N

/-- Quarter gap < half gap. -/
theorem Real.lt_one_div_two_of_lt_one_div_four {ρ : ℝ} (hρ : ρ < (1 : ℝ) / 4) :
    ρ < (1 : ℝ) / 2 :=
  lt_trans hρ Real.finiteAbelPlana_one_div_four_lt_one_div_two

/-- Subtracting positive moves left. -/
theorem Real.sub_nonneg_le_self (x ρ : ℝ) (hρ : 0 ≤ ρ) : x - ρ ≤ x :=
  sub_le_self x hρ

/-- Negate reverses. -/
theorem Real.endpoint_neg_le_neg_of_le {a b : ℝ} (h : a ≤ b) : -b ≤ -a :=
  neg_le_neg h

/-- Lower indent height < upper. -/
theorem Real.endpoint_neg_radius_le_height {T ρ : ℝ} (hT : 0 < T) (hρ : 0 < ρ) : -ρ ≤ T :=
  (neg_nonpos.mpr hρ.le).trans hT.le

/-- Lower height < upper indent. -/
theorem Real.endpoint_neg_height_le_radius {T ρ : ℝ} (hT : 0 < T) (hρ : 0 < ρ) : -T ≤ ρ :=
  (neg_nonpos.mpr hT.le).trans hρ.le

/-- Lower < lower indent. -/
theorem Real.endpoint_neg_height_le_neg_radius {T ρ : ℝ} (hρT : ρ < T) : -T ≤ -ρ :=
  Real.endpoint_neg_le_neg_of_le hρT.le

/-- Half-height condition. -/
theorem Real.endpoint_radius_lt_height_of_lt_abs_height_half {T ρ : ℝ}
    (hT : 0 < T) (hρ_abs : ρ < |T| / 2) : ρ < T :=
  let hT_abs : |T| = T := abs_of_pos hT
  let hρ_half : ρ < T / 2 := hT_abs ▸ hρ_abs
  hρ_half.trans (half_lt_self hT)

/-- Radius < |height|. -/
theorem Real.endpoint_radius_lt_abs_height {T ρ : ℝ} (hT : 0 < T) (hρT : ρ < T) : ρ < |T| :=
  lt_of_lt_of_eq hρT (abs_of_pos hT).symm

/-- Lower interval in full height. -/
theorem Real.endpoint_lower_interval_subset_height {T ρ : ℝ}
    (hT : 0 < T) (hρ : 0 < ρ) (hρT : ρ < T) :
    ∀ y ∈ [[(-T), (-ρ)]], y ∈ [[-T, T]] :=
  fun y hy => ⟨hy.1, hy.2.trans (Real.endpoint_neg_radius_le_height hT hρ)⟩

/-- Middle interval in full height. -/
theorem Real.endpoint_middle_interval_subset_height {T ρ : ℝ}
    (hρ : 0 < ρ) (hρT : ρ < T) :
    ∀ y ∈ [[(-ρ), ρ]], y ∈ [[-T, T]] :=
  fun y hy => ⟨(Real.endpoint_neg_height_le_neg_radius hρT).trans hy.1, hy.2.trans hρT.le⟩

/-- Upper interval in full height. -/
theorem Real.endpoint_upper_interval_subset_height {T ρ : ℝ}
    (hT : 0 < T) (hρ : 0 < ρ) (hρT : ρ < T) :
    ∀ y ∈ [[ρ, T]], y ∈ [[-T, T]] :=
  fun y hy => ⟨(Real.endpoint_neg_height_le_radius hT hρ).trans hy.1, hy.2⟩

/-- Double radius ≤ 1. -/
theorem Real.endpoint_two_radius_le_one_of_lt_half {ρ : ℝ} (hρ : ρ < (1 : ℝ) / 2) :
    ρ + ρ ≤ (1 : ℝ) :=
  let hsum : ρ + ρ ≤ (1 : ℝ) / 2 + (1 : ℝ) / 2 := add_le_add hρ.le hρ.le
  hsum.trans_eq (add_halves (1 : ℝ))

/-- Disk separation inequality. -/
theorem Real.endpoint_radius_sub_one_le_neg_radius_of_lt_half {ρ : ℝ}
    (hρ : ρ < (1 : ℝ) / 2) : ρ - 1 ≤ -ρ :=
  let hdouble : ρ + ρ ≤ (1 : ℝ) := Real.endpoint_two_radius_le_one_of_lt_half hρ
  let hle_sub : ρ ≤ 1 - ρ := le_sub_iff_add_le.mpr hdouble
  let hle_conv : 1 - ρ = -ρ + 1 := (sub_eq_add_neg 1 ρ).trans (add_comm 1 (-ρ))
  let hle_add : ρ ≤ -ρ + 1 := hle_sub.trans (hle_conv ▸ le_refl _)
  sub_le_iff_le_add.mpr hle_add

/-- Left endpoint separation. -/
theorem Real.endpoint_left_re_sub_integer_le_neg_radius {x ρ m : ℝ}
    (hx : x ≤ ρ) (hm : 1 ≤ m) (hρ : ρ < (1 : ℝ) / 2) : x - m ≤ -ρ :=
  let hxm : x - m ≤ ρ - 1 := sub_le_sub hx hm
  hxm.trans (Real.endpoint_radius_sub_one_le_neg_radius_of_lt_half hρ)

/-- Rebracketing. -/
theorem Real.endpoint_add_one_sub_radius_eq (M ρ : ℝ) : M + (1 - ρ) = (M + 1) - ρ :=
  Eq.trans (congrArg (M + ·) (sub_eq_add_neg 1 ρ))
    (Eq.trans (Eq.symm (add_assoc M 1 (-ρ))) (Eq.symm (sub_eq_add_neg (M + 1) ρ)))

/-- Right endpoint separation. -/
theorem Real.endpoint_radius_le_successor_minus_radius_sub_nat (N : ℕ) {ρ : ℝ}
    (hρ : ρ < (1 : ℝ) / 2) : ρ ≤ (((N + 1 : ℕ) : ℝ) - ρ) - (N : ℝ) :=
  let hdouble : ρ + ρ ≤ (1 : ℝ) := Real.endpoint_two_radius_le_one_of_lt_half hρ
  let htarget : ρ ≤ 1 - ρ := le_sub_iff_add_le.mpr hdouble
  let c : ℝ := (N : ℝ)
  let s1 : (((N + 1 : ℕ) : ℝ) - ρ) - (N : ℝ) = ((c + 1) - ρ) - c :=
    congrArg (fun t => (t - ρ) - c) (Real.natCast_succ_eq N)
  let s2 : ((c + 1) - ρ) - c = ((c + 1) + (-ρ)) - c :=
    congrArg (· - c) (sub_eq_add_neg (c + 1) ρ)
  let s3 : ((c + 1) + (-ρ)) - c = ((c + 1) + (-ρ)) + (-c) :=
    sub_eq_add_neg ((c + 1) + (-ρ)) c
  let s4 : ((c + 1) + (-ρ)) + (-c) = (c + (1 + (-ρ))) + (-c) :=
    congrArg (· + (-c)) (add_assoc c 1 (-ρ))
  let s5 : (c + (1 + (-ρ))) + (-c) = 1 + (-ρ) := add_cancel_outer c (1 + (-ρ))
  let s6 : (1 : ℝ) + (-ρ) = 1 - ρ := (sub_eq_add_neg 1 ρ).symm
  let h_eq : (((N + 1 : ℕ) : ℝ) - ρ) - (N : ℝ) = 1 - ρ :=
    Eq.trans s1 (Eq.trans s2 (Eq.trans s3 (Eq.trans s4 (Eq.trans s5 s6))))
  h_eq ▸ htarget

/-- Transport to the closed interval from bounds. -/
theorem Real.endpoint_mem_uIcc_of_bounds {a b x : ℝ}
    (_horder : a ≤ b) (h : a ≤ x ∧ x ≤ b) : x ∈ Set.Icc a b :=
  Set.mem_Icc.mpr h

/-- Transport from the closed interval to bounds. -/
theorem Real.endpoint_bounds_of_mem_uIcc {a b x : ℝ}
    (_horder : a ≤ b) (h : x ∈ Set.Icc a b) : a ≤ x ∧ x ≤ b :=
  Set.mem_Icc.mp h

/-- Equality transport for the closed interval. -/
theorem Real.endpoint_mem_uIcc_congr {a b x y : ℝ}
    (hxy : x = y) (hy : y ∈ Set.Icc a b) : x ∈ Set.Icc a b :=
  hxy.symm ▸ hy

/-- Equality transport for the closed interval (reverse). -/
theorem Real.endpoint_mem_uIcc_congr_symm {a b x y : ℝ}
    (hxy : x = y) (hx : x ∈ Set.Icc a b) : y ∈ Set.Icc a b :=
  hxy ▸ hx

/-- Ball membership as norm. -/
theorem Complex.endpoint_norm_lt_of_mem_ball (z c : ℂ) {ρ : ℝ}
    (h : z ∈ Metric.ball c ρ) : ‖z - c‖ < ρ :=
  Eq.mp (congrArg (fun r : ℝ => r < ρ) (dist_eq_norm z c)) (Metric.mem_ball.mp h)

/-- Real part of subtraction. -/
theorem Complex.endpoint_sub_natCast_re (z : ℂ) (m : ℕ) : (z - (m : ℂ)).re = z.re - (m : ℝ) :=
  Eq.trans (Complex.sub_re z (m : ℂ)) rfl

/-- Imaginary part of subtraction. -/
theorem Complex.endpoint_sub_natCast_im (z : ℂ) (m : ℕ) : (z - (m : ℂ)).im = z.im :=
  Eq.trans (Complex.sub_im z (m : ℂ)) (Eq.trans rfl (sub_zero z.im))

/-- Norm dominates real part. -/
theorem Complex.endpoint_abs_re_le_norm (z : ℂ) : |z.re| ≤ ‖z‖ :=
  Complex.abs_re_le_abs z

/-- Norm dominates imaginary part. -/
theorem Complex.endpoint_abs_im_le_norm (z : ℂ) : |z.im| ≤ ‖z‖ :=
  Complex.abs_im_le_abs z

/-- Large imaginary part outside ball. -/
theorem Complex.endpoint_not_mem_center_ball_of_radius_le_abs_im {z : ℂ} {ρ : ℝ}
    (hρ : ρ ≤ |z.im|) : z ∉ Metric.ball (0 : ℂ) ρ :=
  fun hball =>
    let hdist_raw : ‖z - 0‖ < ρ := Complex.endpoint_norm_lt_of_mem_ball z (0 : ℂ) hball
    let hdist : ‖z‖ < ρ := (sub_zero z) ▸ hdist_raw
    let him_norm : |z.im| ≤ ‖z‖ := Complex.endpoint_abs_im_le_norm z
    not_lt_of_ge (hρ.trans him_norm) hdist

/-- Large centered real part outside ball. -/
theorem Complex.endpoint_not_mem_ball_of_radius_le_abs_re_sub_center {z c : ℂ} {ρ : ℝ}
    (hρ : ρ ≤ |(z - c).re|) : z ∉ Metric.ball c ρ :=
  fun hball =>
    let hdist : ‖z - c‖ < ρ := Complex.endpoint_norm_lt_of_mem_ball z c hball
    let hre_norm : |(z - c).re| ≤ ‖z - c‖ := Complex.endpoint_abs_re_le_norm (z - c)
    not_lt_of_ge (hρ.trans hre_norm) hdist

/-! ## Coordinate and integrand helpers for rectangle-boundary transport

These are shared by the left and right endpoint cap/collar transports. -/

theorem I_mul_ofReal_re (r : ℝ) : (Complex.I * (r : ℂ)).re = 0 :=
  Eq.trans (Complex.I_mul_re (r : ℂ))
    (Eq.trans (congrArg Neg.neg (Complex.ofReal_im r)) neg_zero)
theorem I_mul_ofReal_im (r : ℝ) : (Complex.I * (r : ℂ)).im = r :=
  Eq.trans (Complex.I_mul_im (r : ℂ)) (Complex.ofReal_re r)
theorem negI_mul_re (r : ℝ) : (-Complex.I * (r : ℂ)).re = 0 :=
  Eq.trans (congrArg Complex.re (neg_mul Complex.I (r : ℂ)))
    (Eq.trans (Complex.neg_re (Complex.I * (r : ℂ))) (congrArg Neg.neg (I_mul_ofReal_re r)) |>.trans
      neg_zero)
theorem negI_mul_im (r : ℝ) : (-Complex.I * (r : ℂ)).im = -r :=
  Eq.trans (congrArg Complex.im (neg_mul Complex.I (r : ℂ)))
    (Eq.trans (Complex.neg_im (Complex.I * (r : ℂ))) (congrArg Neg.neg (I_mul_ofReal_im r)))
theorem ofReal_sub_I_mul_re (a r : ℝ) :
    ((a : ℂ) - Complex.I * (r : ℂ)).re = a :=
  Eq.trans (Complex.sub_re (a : ℂ) (Complex.I * (r : ℂ)))
    (Eq.trans (congrArg₂ (· - ·) (Complex.ofReal_re a) (I_mul_ofReal_re r)) (sub_zero a))
theorem ofReal_sub_I_mul_im (a r : ℝ) :
    ((a : ℂ) - Complex.I * (r : ℂ)).im = -r :=
  Eq.trans (Complex.sub_im (a : ℂ) (Complex.I * (r : ℂ)))
    (Eq.trans (congrArg₂ (· - ·) (Complex.ofReal_im a) (I_mul_ofReal_im r)) (zero_sub r))
theorem ofReal_add_I_mul_re (a r : ℝ) :
    ((a : ℂ) + Complex.I * (r : ℂ)).re = a :=
  Eq.trans (Complex.add_re (a : ℂ) (Complex.I * (r : ℂ)))
    (Eq.trans (congrArg₂ (· + ·) (Complex.ofReal_re a) (I_mul_ofReal_re r)) (add_zero a))
theorem ofReal_add_I_mul_im (a r : ℝ) :
    ((a : ℂ) + Complex.I * (r : ℂ)).im = r :=
  Eq.trans (Complex.add_im (a : ℂ) (Complex.I * (r : ℂ)))
    (Eq.trans (congrArg₂ (· + ·) (Complex.ofReal_im a) (I_mul_ofReal_im r)) (zero_add r))

/-- Horizontal integrand normalization with a subtracted imaginary part:
`f (x + ↑(-r)·I) = f (x - I·r)`. -/
theorem integrand_horiz_sub (f : ℂ → ℂ) (r : ℝ) :
    (fun x : ℝ => f ((x : ℂ) + ((-r : ℝ) : ℂ) * Complex.I)) =
      (fun x : ℝ => f ((x : ℂ) - Complex.I * (r : ℂ))) :=
  funext fun x =>
    congrArg f
      (Eq.trans
        (congrArg (fun w => (x : ℂ) + w)
          (Eq.trans (congrArg (· * Complex.I) (Complex.ofReal_neg r))
            (Eq.trans (neg_mul (r : ℂ) Complex.I)
              (congrArg Neg.neg (mul_comm (r : ℂ) Complex.I)))))
        (sub_eq_add_neg (x : ℂ) (Complex.I * (r : ℂ))).symm)
/-- Horizontal integrand normalization: `f (x + ↑r·I) = f (x + I·r)`. -/
theorem integrand_horiz_add (f : ℂ → ℂ) (r : ℝ) :
    (fun x : ℝ => f ((x : ℂ) + (r : ℂ) * Complex.I)) =
      (fun x : ℝ => f ((x : ℂ) + Complex.I * (r : ℂ))) :=
  funext fun x =>
    congrArg f (congrArg (fun w => (x : ℂ) + w) (mul_comm (r : ℂ) Complex.I))
/-- Vertical integrand normalization: `f (↑a + ↑y·I) = f (a + I·y)`. -/
theorem integrand_vert (f : ℂ → ℂ) (a : ℝ) :
    (fun y : ℝ => f ((a : ℂ) + (y : ℂ) * Complex.I)) =
      (fun y : ℝ => f ((a : ℂ) + Complex.I * (y : ℂ))) :=
  funext fun y =>
    congrArg f (congrArg (fun w => (a : ℂ) + w) (mul_comm (y : ℂ) Complex.I))
/-- Principal-value vertical integrand normalization at the origin:
`f (↑0 + ↑y·I) = f (I·y)`. -/
theorem integrand_pv_zero (f : ℂ → ℂ) :
    (fun y : ℝ => f (((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) =
      (fun y : ℝ => f (Complex.I * (y : ℂ))) :=
  funext fun y =>
    congrArg f
      (Eq.trans (congrArg (· + (y : ℂ) * Complex.I) Complex.ofReal_zero)
        (Eq.trans (zero_add ((y : ℂ) * Complex.I)) (mul_comm (y : ℂ) Complex.I)))

/-- Congruence of an interval integral in integrand and both endpoints. -/
theorem intervalIntegral_congr3 {g g' : ℝ → ℂ} {a a' b b' : ℝ}
    (hg : g = g') (ha : a = a') (hb : b = b') :
    (∫ x : ℝ in a..b, g x) = ∫ x : ℝ in a'..b', g' x :=
  Eq.trans (congrArg (fun w => intervalIntegral w a b MeasureTheory.volume) hg)
    (Eq.trans (congrArg (fun w => intervalIntegral g' w b MeasureTheory.volume) ha)
      (congrArg (fun w => intervalIntegral g' a' w MeasureTheory.volume) hb))

end

end LFunctions
end Boundary
