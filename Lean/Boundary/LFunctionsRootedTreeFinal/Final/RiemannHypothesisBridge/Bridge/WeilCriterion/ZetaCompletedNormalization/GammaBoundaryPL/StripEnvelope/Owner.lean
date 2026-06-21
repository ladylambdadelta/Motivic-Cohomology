import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaBoundaryPL.GammaGrowth.Owner

/-!
# Strip boundary envelope algebra

This owner layer contains the bounded-boundary strip theorem and finite-order envelope algebra.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

/-- Mathlib's bounded-boundary vertical-strip Phragmen-Lindelöf theorem, specialized to
complex-valued functions and exposed in the local strip-growth language.

The damping proof of the polynomial/exponential strip theorem reduces to this bounded
form after multiplying by the standard strip damping factor. -/
theorem strip_uniform_bound_of_holomorphic_boundary_bound_and_mathlib_growth
    (f : ℂ → ℂ)
    (a b C : ℝ)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (hgrowth :
      ∃ c : ℝ,
        c < Real.pi / (b - a) ∧
        ∃ D : ℝ,
          f =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)))
    (hleft :
      ∀ z : ℂ,
        z.re = a →
        ‖f z‖ ≤ C)
    (hright :
      ∀ z : ℂ,
        z.re = b →
        ‖f z‖ ≤ C) :
    ∀ z : ℂ,
      a ≤ z.re →
      z.re ≤ b →
      ‖f z‖ ≤ C := by
  exact
    fun z hza hzb =>
      PhragmenLindelof.vertical_strip
        (f := f)
        (a := a)
        (b := b)
        (C := C)
        hhol
        hgrowth
        hleft
        hright
        hza
        hzb

/-- Separate finite-order boundary envelopes on the two vertical sides can be dominated by
a single common finite-order envelope.

This is the algebraic normalization used before applying the strip damping argument. -/
theorem strip_boundary_growth_envelopes_common_bound
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hleft :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re = a →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hright :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re = b →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      (∀ z : ℂ,
        z.re = a →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) ∧
      (∀ z : ℂ,
        z.re = b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) := by
  match hleft, hright with
  | ⟨Al, Bl, ml, hAl, hBl, hleft_bound⟩,
    ⟨Ar, Br, mr, hAr, hBr, hright_bound⟩ =>
      have hleft_common :
          ∀ z : ℂ,
            z.re = a →
            1 ≤ ‖z.im‖ →
            ‖f z‖ ≤ (Al + Ar) * Real.exp ((Bl + Br) * (1 + ‖z‖) ^ (ml + mr)) :=
        fun z hz_re hz_im =>
          le_trans (hleft_bound z hz_re hz_im)
            (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
              (le_of_lt hAl)
              (le_add_of_nonneg_right (le_of_lt hAr))
              (le_add_of_nonneg_right (le_of_lt hBr))
              (le_of_lt hBl)
              (Nat.le_add_right ml mr))
      have hright_common :
          ∀ z : ℂ,
            z.re = b →
            1 ≤ ‖z.im‖ →
            ‖f z‖ ≤ (Al + Ar) * Real.exp ((Bl + Br) * (1 + ‖z‖) ^ (ml + mr)) :=
        fun z hz_re hz_im =>
          by
            have hdegree : mr ≤ ml + mr :=
              Eq.subst
                (motive := fun d : ℕ => mr ≤ d)
                (Nat.add_comm mr ml)
                (Nat.le_add_right mr ml)
            exact le_trans (hright_bound z hz_re hz_im)
              (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
                (le_of_lt hAr)
                (le_add_of_nonneg_left (le_of_lt hAl))
                (le_add_of_nonneg_left (le_of_lt hBl))
                (le_of_lt hBr)
                hdegree)
      exact
        ⟨Al + Ar, Bl + Br, ml + mr,
          add_pos hAl hAr, add_pos hBl hBr, hleft_common, hright_common⟩

/-- The negative left endpoint is bounded below by the negative sum of endpoint sizes. -/
theorem strip_negative_abs_sum_le_negative_left_abs
    (a b S : ℝ)
    (hS : S = |a| + |b|) :
    -S ≤ -|a| := by
  have hneg_sum :
      -S = -|a| + -|b| := by
    calc
      -S = -(|a| + |b|) := congrArg Neg.neg hS
      _ = -|a| + -|b| := neg_add |a| |b|
  have hsum_le : -|a| + -|b| ≤ -|a| := by
    have hb_nonpos : -|b| ≤ 0 :=
      neg_nonpos.mpr (abs_nonneg b)
    have hstep : -|a| + -|b| ≤ -|a| + 0 :=
      add_le_add_left hb_nonpos (-|a|)
    exact le_trans hstep (le_of_eq (add_zero (-|a|)))
  exact le_trans (le_of_eq hneg_sum) hsum_le

/-- Algebraic domination of the basic strip height by the product envelope. -/
theorem strip_basicHeight_algebraic_product_bound
    {S Y : ℝ}
    (hS_nonneg : 0 ≤ S)
    (hY_nonneg : 0 ≤ Y) :
    1 + (S + Y) ≤ (S + 2) * (1 + Y) := by
  have hleft_eq : 1 + (S + Y) = (S + 1) + Y := by
    calc
      1 + (S + Y) = (1 + S) + Y := by
        exact (add_assoc (1 : ℝ) S Y).symm
      _ = (S + 1) + Y := by
        exact congrArg (fun t : ℝ => t + Y) (add_comm (1 : ℝ) S)
  have hS_one_le_S_two : S + 1 ≤ S + 2 :=
    add_le_add_left one_le_two S
  have hbase_le : (S + 1) + Y ≤ (S + 2) + Y :=
    add_le_add_right hS_one_le_S_two Y
  have hone_le_S_two : (1 : ℝ) ≤ S + 2 := by
    exact le_trans one_le_two (le_add_of_nonneg_left hS_nonneg)
  have hY_le_scaled : Y ≤ (S + 2) * Y := by
    calc
      Y = (1 : ℝ) * Y := by
        exact (one_mul Y).symm
      _ ≤ (S + 2) * Y := mul_le_mul_of_nonneg_right hone_le_S_two hY_nonneg
  have hscaled_add :
      (S + 2) + Y ≤ (S + 2) + (S + 2) * Y :=
    add_le_add_left hY_le_scaled (S + 2)
  have hproduct_eq :
      (S + 2) + (S + 2) * Y = (S + 2) * (1 + Y) := by
    calc
      (S + 2) + (S + 2) * Y =
          (S + 2) * 1 + (S + 2) * Y := by
        exact congrArg (fun t : ℝ => t + (S + 2) * Y) (mul_one (S + 2)).symm
      _ = (S + 2) * (1 + Y) := by
        exact (mul_add (S + 2) 1 Y).symm
  exact le_trans (le_of_eq hleft_eq) (le_trans hbase_le (le_trans hscaled_add (le_of_eq hproduct_eq)))

/-- In a bounded vertical strip, the basic complex height is controlled by the vertical
height. -/
theorem strip_basicHeight_le_verticalHeight
    (a b : ℝ)
    {z : ℂ}
    (hza : a ≤ z.re)
    (hzb : z.re ≤ b) :
    1 + ‖z‖ ≤ (|a| + |b| + 2) * (1 + ‖z.im‖) := by
  let S : ℝ := |a| + |b|
  let Y : ℝ := |z.im|
  have hS_nonneg : 0 ≤ S := by
    exact add_nonneg (abs_nonneg a) (abs_nonneg b)
  have hY_nonneg : 0 ≤ Y := by
    exact abs_nonneg z.im
  have hre_abs_le_S : |z.re| ≤ S := by
    have hleft : -S ≤ z.re := by
      have hnegS_le_neg_abs_a : -S ≤ -|a| := by
        exact strip_negative_abs_sum_le_negative_left_abs a b S rfl
      have hneg_abs_a_le_a : -|a| ≤ a :=
        neg_abs_le a
      exact le_trans hnegS_le_neg_abs_a (le_trans hneg_abs_a_le_a hza)
    have hright : z.re ≤ S := by
      have hb_le_abs_b : b ≤ |b| :=
        le_abs_self b
      have habs_b_le_S : |b| ≤ S := by
        exact le_add_of_nonneg_left (abs_nonneg a)
      exact le_trans hzb (le_trans hb_le_abs_b habs_b_le_S)
    exact abs_le.mpr ⟨hleft, hright⟩
  have hnorm_le : ‖z‖ ≤ S + Y := by
    have hcomplex :
        ‖z‖ ≤ |z.re| + |z.im| :=
      Eq.subst
        (motive := fun x : ℝ => x ≤ |z.re| + |z.im|)
        (Complex.norm_eq_abs z).symm
        (Complex.abs_le_abs_re_add_abs_im z)
    exact le_trans hcomplex (add_le_add_right hre_abs_le_S Y)
  have hlinear :
      1 + ‖z‖ ≤ 1 + (S + Y) :=
    add_le_add_left hnorm_le 1
  have htarget :
      1 + (S + Y) ≤ (S + 2) * (1 + Y) := by
    exact strip_basicHeight_algebraic_product_bound hS_nonneg hY_nonneg
  have him_norm_eq : ‖z.im‖ = Y :=
    Real.norm_eq_abs z.im
  exact Eq.subst
    (motive := fun T : ℝ => 1 + ‖z‖ ≤ (S + 2) * (1 + T))
    him_norm_eq.symm
    (le_trans hlinear htarget)

/-- On a bounded vertical strip, a finite-order envelope in complex height is dominated by
one in vertical height. -/
theorem finiteOrder_norm_envelope_le_strip_vertical_envelope
    {A B a b : ℝ} {m : ℕ} {z : ℂ}
    (hA : 0 ≤ A)
    (hB : 0 ≤ B)
    (hza : a ≤ z.re)
    (hzb : z.re ≤ b) :
    A * Real.exp (B * (1 + ‖z‖) ^ m) ≤
      A * Real.exp ((B * (|a| + |b| + 2) ^ m) * (1 + ‖z.im‖) ^ m) := by
  let K : ℝ := |a| + |b| + 2
  let H : ℝ := 1 + ‖z‖
  let T : ℝ := 1 + ‖z.im‖
  have hH_nonneg : 0 ≤ H := by
    exact le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg z))
  have hT_nonneg : 0 ≤ T := by
    exact le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg z.im))
  have hheight : H ≤ K * T :=
    strip_basicHeight_le_verticalHeight a b hza hzb
  have hpow_le : H ^ m ≤ (K * T) ^ m :=
    pow_le_pow_left₀ hH_nonneg hheight m
  have hpow_eq : (K * T) ^ m = K ^ m * T ^ m :=
    mul_pow K T m
  have hexponent_le :
      B * H ^ m ≤ (B * K ^ m) * T ^ m := by
    have hfirst : B * H ^ m ≤ B * (K * T) ^ m :=
      mul_le_mul_of_nonneg_left hpow_le hB
    exact le_trans hfirst
      (le_of_eq
        (calc
          B * (K * T) ^ m = B * (K ^ m * T ^ m) := by
            exact congrArg (fun x : ℝ => B * x) hpow_eq
          _ = (B * K ^ m) * T ^ m := by
            exact (mul_assoc B (K ^ m) (T ^ m)).symm))
  have hexp_le :
      Real.exp (B * H ^ m) ≤ Real.exp ((B * K ^ m) * T ^ m) :=
    Real.exp_le_exp.mpr hexponent_le
  exact mul_le_mul_of_nonneg_left hexp_le hA

/-- The strip-height scale factor is at least `2`. -/
theorem two_le_abs_add_abs_add_two
    (a b : ℝ) :
    (2 : ℝ) ≤ |a| + |b| + 2 := by
  have hsum_nonneg : 0 ≤ |a| + |b| :=
    add_nonneg (abs_nonneg a) (abs_nonneg b)
  exact le_add_of_nonneg_left hsum_nonneg

/-- The common boundary envelope can be rewritten in terms of vertical height on a bounded
strip. -/
theorem strip_common_boundary_envelope_vertical_height_bound
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hab : a < b)
    (hboundary :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        (∀ z : ℂ,
          z.re = a →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) ∧
        (∀ z : ℂ,
          z.re = b →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m))) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      (∀ z : ℂ,
        z.re = a →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m)) ∧
      (∀ z : ℂ,
        z.re = b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m)) := by
  match hboundary with
  | ⟨A, B, m, hA, hB, hleft, hright⟩ =>
      let K : ℝ := |a| + |b| + 2
      have hK_pos : 0 < K := by
        have htwo_le : (2 : ℝ) ≤ K :=
          two_le_abs_add_abs_add_two a b
        exact lt_of_lt_of_le zero_lt_two htwo_le
      have hleft_vertical :
          ∀ z : ℂ,
            z.re = a →
            1 ≤ ‖z.im‖ →
            ‖f z‖ ≤ A * Real.exp ((B * K ^ m) * (1 + ‖z.im‖) ^ m) :=
        fun z hz_re hz_im =>
          by
            have hza : a ≤ z.re :=
              le_of_eq hz_re.symm
            have hzb : z.re ≤ b :=
              le_trans (le_of_eq hz_re) (le_of_lt hab)
            exact le_trans (hleft z hz_re hz_im)
              (finiteOrder_norm_envelope_le_strip_vertical_envelope
                (le_of_lt hA)
                (le_of_lt hB)
                hza
                hzb)
      have hright_vertical :
          ∀ z : ℂ,
            z.re = b →
            1 ≤ ‖z.im‖ →
            ‖f z‖ ≤ A * Real.exp ((B * K ^ m) * (1 + ‖z.im‖) ^ m) :=
        fun z hz_re hz_im =>
          by
            have hza : a ≤ z.re :=
              le_trans (le_of_lt hab) (le_of_eq hz_re.symm)
            have hzb : z.re ≤ b :=
              le_of_eq hz_re
            exact le_trans (hright z hz_re hz_im)
              (finiteOrder_norm_envelope_le_strip_vertical_envelope
                (le_of_lt hA)
                (le_of_lt hB)
                hza
                hzb)
      exact
        ⟨A, B * K ^ m, m, hA,
          mul_pos hB (pow_pos hK_pos m), hleft_vertical, hright_vertical⟩

/-- Exponential damping cancels its matching growth factor. -/
theorem exp_negative_growth_mul_growth_cancel
    (A X : ℝ) :
    Real.exp (-X) * (A * Real.exp X) = A := by
  have hcancel : (-X) + X = 0 :=
    neg_add_cancel X
  calc
    Real.exp (-X) * (A * Real.exp X) =
        (Real.exp (-X) * A) * Real.exp X := by
      exact (mul_assoc (Real.exp (-X)) A (Real.exp X)).symm
    _ = (A * Real.exp (-X)) * Real.exp X := by
      exact congrArg (fun t : ℝ => t * Real.exp X) (mul_comm (Real.exp (-X)) A)
    _ = A * (Real.exp (-X) * Real.exp X) := by
      exact mul_assoc A (Real.exp (-X)) (Real.exp X)
    _ = A * Real.exp ((-X) + X) := by
      exact congrArg (fun t : ℝ => A * t) (Real.exp_add (-X) X).symm
    _ = A * Real.exp 0 := by
      exact congrArg (fun t : ℝ => A * Real.exp t) hcancel
    _ = A * 1 := by
      exact congrArg (fun t : ℝ => A * t) Real.exp_zero
    _ = A := by
      exact mul_one A

/-- The vertical-height boundary envelope becomes uniformly bounded after multiplying by
the matching real exponential damping factor. -/
theorem strip_vertical_boundary_envelope_exp_damped_bound
    (f : ℂ → ℂ)
    (a b A B : ℝ)
    (m : ℕ)
    (hboundary :
      (∀ z : ℂ,
        z.re = a →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m)) ∧
      (∀ z : ℂ,
        z.re = b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m))) :
    (∀ z : ℂ,
      z.re = a →
      1 ≤ ‖z.im‖ →
      Real.exp (-(B * (1 + ‖z.im‖) ^ m)) * ‖f z‖ ≤ A) ∧
    (∀ z : ℂ,
      z.re = b →
      1 ≤ ‖z.im‖ →
      Real.exp (-(B * (1 + ‖z.im‖) ^ m)) * ‖f z‖ ≤ A) := by
  exact
    And.intro
      (fun z hz_re hz_im =>
        let X : ℝ := B * (1 + ‖z.im‖) ^ m
        have hbound :
            ‖f z‖ ≤ A * Real.exp X :=
          hboundary.1 z hz_re hz_im
        have hdamp_nonneg : 0 ≤ Real.exp (-X) :=
          le_of_lt (Real.exp_pos (-X))
        have hscaled :
            Real.exp (-X) * ‖f z‖ ≤ Real.exp (-X) * (A * Real.exp X) :=
          mul_le_mul_of_nonneg_left hbound hdamp_nonneg
        have hcollapse :
            Real.exp (-X) * (A * Real.exp X) = A := by
          exact exp_negative_growth_mul_growth_cancel A X
        hscaled.trans_eq hcollapse)
      (fun z hz_re hz_im =>
        let X : ℝ := B * (1 + ‖z.im‖) ^ m
        have hbound :
            ‖f z‖ ≤ A * Real.exp X :=
          hboundary.2 z hz_re hz_im
        have hdamp_nonneg : 0 ≤ Real.exp (-X) :=
          le_of_lt (Real.exp_pos (-X))
        have hscaled :
            Real.exp (-X) * ‖f z‖ ≤ Real.exp (-X) * (A * Real.exp X) :=
          mul_le_mul_of_nonneg_left hbound hdamp_nonneg
        have hcollapse :
            Real.exp (-X) * (A * Real.exp X) = A := by
          exact exp_negative_growth_mul_growth_cancel A X
        hscaled.trans_eq hcollapse)

/-- Tail and compact boundary bounds combine to a single uniform boundary bound.

This is the boundary bookkeeping step used after damping: the vertical tail is
bounded by one constant, and the remaining compact-height boundary segment is
bounded by another. -/
theorem strip_uniform_boundary_bound_of_tail_and_compact
    (g : ℂ → ℂ)
    (a b A C : ℝ)
    (hA : 0 < A)
    (hC : 0 < C)
    (htail :
      (∀ z : ℂ,
        z.re = a →
        1 ≤ ‖z.im‖ →
        ‖g z‖ ≤ A) ∧
      (∀ z : ℂ,
        z.re = b →
        1 ≤ ‖z.im‖ →
        ‖g z‖ ≤ A))
    (hcompact :
      (∀ z : ℂ,
        z.re = a →
        ¬ 1 ≤ ‖z.im‖ →
        ‖g z‖ ≤ C) ∧
      (∀ z : ℂ,
        z.re = b →
        ¬ 1 ≤ ‖z.im‖ →
        ‖g z‖ ≤ C)) :
    ∃ D : ℝ,
      0 < D ∧
      (∀ z : ℂ,
        z.re = a →
        ‖g z‖ ≤ D) ∧
      (∀ z : ℂ,
        z.re = b →
        ‖g z‖ ≤ D) := by
  let D : ℝ := A + C
  have hD : 0 < D :=
    add_pos hA hC
  have hA_le_D : A ≤ D :=
    le_add_of_nonneg_right (le_of_lt hC)
  have hC_le_D : C ≤ D :=
    le_add_of_nonneg_left (le_of_lt hA)
  have hleft :
      ∀ z : ℂ,
        z.re = a →
        ‖g z‖ ≤ D :=
    fun z hz_re =>
      match Decidable.em (1 ≤ ‖z.im‖) with
      | Or.inl hlarge =>
          le_trans (htail.1 z hz_re hlarge) hA_le_D
      | Or.inr hsmall =>
          le_trans (hcompact.1 z hz_re hsmall) hC_le_D
  have hright :
      ∀ z : ℂ,
        z.re = b →
        ‖g z‖ ≤ D :=
    fun z hz_re =>
      match Decidable.em (1 ≤ ‖z.im‖) with
      | Or.inl hlarge =>
          le_trans (htail.2 z hz_re hlarge) hA_le_D
      | Or.inr hsmall =>
          le_trans (hcompact.2 z hz_re hsmall) hC_le_D
  exact ⟨D, hD, hleft, hright⟩

/-- Existential form of the tail-plus-compact boundary assembly. -/
theorem strip_uniform_boundary_package_of_tail_and_compact
    (g : ℂ → ℂ)
    (a b : ℝ)
    (htail :
      ∃ A : ℝ,
        0 < A ∧
        (∀ z : ℂ,
          z.re = a →
          1 ≤ ‖z.im‖ →
          ‖g z‖ ≤ A) ∧
        (∀ z : ℂ,
          z.re = b →
          1 ≤ ‖z.im‖ →
          ‖g z‖ ≤ A))
    (hcompact :
      ∃ C : ℝ,
        0 < C ∧
        (∀ z : ℂ,
          z.re = a →
          ¬ 1 ≤ ‖z.im‖ →
          ‖g z‖ ≤ C) ∧
        (∀ z : ℂ,
          z.re = b →
          ¬ 1 ≤ ‖z.im‖ →
          ‖g z‖ ≤ C)) :
    ∃ D : ℝ,
      0 < D ∧
      (∀ z : ℂ,
        z.re = a →
        ‖g z‖ ≤ D) ∧
      (∀ z : ℂ,
        z.re = b →
        ‖g z‖ ≤ D) := by
  match htail, hcompact with
  | ⟨A, hA, htail_left, htail_right⟩,
    ⟨C, hC, hcompact_left, hcompact_right⟩ =>
      exact
        strip_uniform_boundary_bound_of_tail_and_compact
          g a b A C hA hC
          ⟨htail_left, htail_right⟩
          ⟨hcompact_left, hcompact_right⟩

/-- The vertical height is bounded by the ordinary complex height. -/
theorem vertical_basicHeight_le_complex_basicHeight
    (z : ℂ) :
    1 + ‖z.im‖ ≤ 1 + ‖z‖ := by
  have him_abs_le_norm : |z.im| ≤ ‖z‖ := by
    exact Complex.abs_im_le_abs z
  have him_le_norm : ‖z.im‖ ≤ ‖z‖ :=
    Eq.subst
      (motive := fun x : ℝ => x ≤ ‖z‖)
      (Real.norm_eq_abs z.im).symm
      him_abs_le_norm
  exact add_le_add_left him_le_norm 1

/-- A vertical-height finite-order boundary envelope is also a complex-height envelope. -/
theorem finiteOrder_vertical_envelope_le_complex_envelope
    {A B : ℝ} {m : ℕ} {z : ℂ}
    (hA : 0 ≤ A)
    (hB : 0 ≤ B) :
    A * Real.exp (B * (1 + ‖z.im‖) ^ m) ≤
      A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  have hvertical_nonneg : 0 ≤ 1 + ‖z.im‖ := by
    exact le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg z.im))
  have hheight_le :
      1 + ‖z.im‖ ≤ 1 + ‖z‖ :=
    vertical_basicHeight_le_complex_basicHeight z
  have hpow_le :
      (1 + ‖z.im‖) ^ m ≤ (1 + ‖z‖) ^ m :=
    pow_le_pow_left₀ hvertical_nonneg hheight_le m
  have hexponent_le :
      B * (1 + ‖z.im‖) ^ m ≤ B * (1 + ‖z‖) ^ m :=
    mul_le_mul_of_nonneg_left hpow_le hB
  have hexp_le :
      Real.exp (B * (1 + ‖z.im‖) ^ m) ≤
        Real.exp (B * (1 + ‖z‖) ^ m) :=
    Real.exp_le_exp.mpr hexponent_le
  exact mul_le_mul_of_nonneg_left hexp_le hA

/-- Vertical-height boundary data can be reused as ordinary complex-height boundary data. -/
theorem strip_vertical_boundary_envelope_complex_height_bound
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hboundary :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        (∀ z : ℂ,
          z.re = a →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m)) ∧
        (∀ z : ℂ,
          z.re = b →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m))) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      (∀ z : ℂ,
        z.re = a →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) ∧
      (∀ z : ℂ,
        z.re = b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) := by
  match hboundary with
  | ⟨A, B, m, hA, hB, hleft, hright⟩ =>
      have hleft_complex :
          ∀ z : ℂ,
            z.re = a →
            1 ≤ ‖z.im‖ →
            ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) :=
        fun z hz_re hz_im =>
          le_trans (hleft z hz_re hz_im)
            (finiteOrder_vertical_envelope_le_complex_envelope
              (le_of_lt hA)
              (le_of_lt hB))
      have hright_complex :
          ∀ z : ℂ,
            z.re = b →
            1 ≤ ‖z.im‖ →
            ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) :=
        fun z hz_re hz_im =>
          le_trans (hright z hz_re hz_im)
            (finiteOrder_vertical_envelope_le_complex_envelope
              (le_of_lt hA)
              (le_of_lt hB))
      exact ⟨A, B, m, hA, hB, hleft_complex, hright_complex⟩

end
end LFunctions
end Boundary
