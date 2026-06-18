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
  let step1_de : d + e = e + d := add_comm d e
  let step1 : a + b + c + d + e + f = a + b + c + e + d + f :=
    let h1 : a + b + c + (d + e) + f = a + b + c + (e + d) + f := congrArg (fun x => a + b + c + x + f) step1_de
    let h2 : a + b + c + d + e + f = a + b + c + (d + e) + f := rfl
    Eq.trans h2 h1
  let step2_bc : b + c = c + b := add_comm b c
  let step2 : a + b + c + e + d + f = a + c + b + e + d + f :=
    let h1 : a + (b + c) + e + d + f = a + (c + b) + e + d + f := congrArg (fun x => a + x + e + d + f) step2_bc
    let h2 : a + b + c + e + d + f = a + (b + c) + e + d + f := rfl
    Eq.trans h2 h1
  let step3_cb : c + b = b + c := add_comm c b
  let step3_be : b + e = e + b := add_comm b e
  let step3 : a + c + b + e + d + f = a + e + c + b + d + f :=
    let h1 : a + (c + b) + (e + d) + f = a + (e + b) + (c + d) + f :=
      let cb_be : (c + b) + (e + d) = (e + b) + (c + d) :=
        Eq.trans (add_assoc c b (e + d))
          (Eq.trans (congrArg (c + ·) (add_assoc b e d))
            (Eq.trans (congrArg (c + ·) (congrArg (b + ·) (add_comm e d)))
              (Eq.trans (congrArg (c + ·) (add_assoc b d e).symm)
                (Eq.trans (add_assoc c b d e).symm
                  (Eq.trans (congrArg (· + (d + e)) (add_comm c b))
                    (add_assoc b c d e))))))
      congrArg (fun x => a + x + f) cb_be
    let h2 : a + (c + b) + e + d + f = a + (c + b) + (e + d) + f := rfl
    Eq.trans h2 h1
  Eq.trans step1 (Eq.trans step2 step3)

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
  let h1 : a + b + (-a) = a + (b + (-a)) := (add_assoc a b (-a)).symm
  let h2 : b + (-a) = b - a := rfl
  let h3 : a + (b - a) = a + (b + (-a)) := rfl
  let h4 : a + (b + (-a)) = (a + b) + (-a) := add_assoc a b (-a)
  let h5 : (a + b) + (-a) = b + (a + (-a)) :=
    Eq.trans (add_comm (a + b) (-a)) (Eq.trans (add_assoc (-a) a b) (congrArg (· + b) (add_comm (-a) a)))
  let h6 : a + (-a) = 0 := add_neg_cancel a
  let h7 : b + 0 = b := add_zero b
  Eq.trans h1 (Eq.trans h4 (Eq.trans h5 (Eq.trans (congrArg (· + b) h6) h7)))

/-- Subtraction to negation. -/
theorem sub_eq_neg {α : Type*} [AddCommGroup α] (a b : α) : a - b = a + (-b) :=
  sub_eq_add_neg a b

/-- Negation of sum equals sum of negations. -/
theorem neg_sum_two {α : Type*} [AddCommGroup α] (a b : α) : -(a + b) = -a + (-b) :=
  neg_add a b

/-- Cancel identity for three terms. -/
theorem add_cancel_three {α : Type*} [AddCommGroup α] (a b : α) : a + b + (-a) = b :=
  add_cancel_outer a b

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
  add_swap_middle a b c

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
  let h1 : B - A = B + (-A) := sub_eq_add_neg B A
  let h2 : A + (B + (-A)) = (A + B) + (-A) := add_assoc A B (-A)
  let h3 : (A + B) + (-A) = (B + A) + (-A) := congrArg (· + (-A)) (add_comm A B)
  let h4 : (B + A) + (-A) = B + (A + (-A)) := (add_assoc B A (-A)).symm
  let h5 : A + (-A) = 0 := add_neg_cancel A
  let h6 : B + 0 = B := add_zero B
  Eq.trans (congrArg (A + ·) h1)
    (Eq.trans h2 (Eq.trans h3 (Eq.trans h4 (Eq.trans (congrArg (B + ·) h5) h6))))

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
  rfl

/-- Chord cancellation in sum. -/
theorem Complex.boundaryChordsCancelInSum (l c r : ℂ) :
    (-l + r + c) + l - c = r :=
  let h : (-l + r + c) + l - c = r + ((-l + l) - c) :=
    Eq.trans (Eq.trans (Eq.symm (add_assoc (-l + r + c) l (-c)))
      (congrArg ((-l + r + c) + ·) (sub_eq_add_neg l c)))
      (Eq.trans (Eq.symm (add_assoc (-l) (r + c) (l + (-c))))
        (congrArg ((-l) + ·) (Eq.trans (add_assoc (r + c) l (-c))
          (congrArg (r + ·) (Eq.trans (add_comm c l) (Eq.symm (add_assoc l c (-c))))))))
  Eq.trans h (Eq.trans (congrArg (r + ·) (Eq.trans (add_neg_cancel l) (Eq.trans (zero_add (-c)) (Eq.symm (sub_eq_add_neg 0 c))))) (add_zero r))

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
  let h_eq : (((N + 1 : ℕ) : ℝ) - ρ) - (N : ℝ) = 1 - ρ :=
    Eq.trans (Eq.trans (congrArg (· - (N : ℝ)) (Eq.trans (Nat.cast_succ N) rfl))
      (Eq.trans (sub_eq_add_neg _ _)
        (Eq.trans (add_assoc (N : ℝ) 1 (-(ρ))) rfl)))
      (sub_eq_add_neg 1 ρ).symm)
  h_eq ▸ htarget

/-- Transport to uIcc from bounds. -/
theorem Real.endpoint_mem_uIcc_of_bounds {a b x : ℝ}
    (horder : a ≤ b) (h : a ≤ x ∧ x ≤ b) : x ∈ Set.uIcc a b :=
  Set.mem_uIcc.mpr (Or.inl h)

/-- Transport from uIcc to bounds. -/
theorem Real.endpoint_bounds_of_mem_uIcc {a b x : ℝ}
    (horder : a ≤ b) (h : x ∈ Set.uIcc a b) : a ≤ x ∧ x ≤ b :=
  Set.mem_Icc.mp ((Set.uIcc_of_le horder) ▸ h)

/-- Equality transport for uIcc. -/
theorem Real.endpoint_mem_uIcc_congr {a b x y : ℝ}
    (hxy : x = y) (hy : y ∈ Set.uIcc a b) : x ∈ Set.uIcc a b :=
  hxy.symm ▸ hy

/-- Equality transport uIcc (reverse). -/
theorem Real.endpoint_mem_uIcc_congr_symm {a b x y : ℝ}
    (hxy : x = y) (hx : x ∈ Set.uIcc a b) : y ∈ Set.uIcc a b :=
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

end

end LFunctions
end Boundary
