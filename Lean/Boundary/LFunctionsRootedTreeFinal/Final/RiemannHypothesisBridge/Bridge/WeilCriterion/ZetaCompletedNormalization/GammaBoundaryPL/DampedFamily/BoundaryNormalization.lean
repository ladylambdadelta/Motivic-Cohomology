import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaBoundaryPL.DampedFamily.Undamping

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Filter Topology
local notation "π" => Real.pi

/-- On the upper vertical tail, ordinary positivity of the imaginary coordinate
implies the norm-height tail condition used by the boundary envelope lemmas. -/
theorem upperTail_im_norm_ge_one
    (z : ℂ)
    (hz : 1 ≤ z.im) :
    1 ≤ ‖z.im‖ := by
  have him_nonneg : 0 ≤ z.im :=
    le_trans zero_le_one hz
  have hnorm : ‖z.im‖ = z.im :=
    Real.norm_of_nonneg him_nonneg
  exact
    Eq.subst
      (motive := fun x : ℝ => 1 ≤ x)
      hnorm.symm
      hz

/-- Upper-tail vertical-boundary finite-order data can be read with the ordinary
complex height at the same constants. -/
theorem strip_upperTail_vertical_boundary_envelope_complex_height_bound
    (f : ℂ → ℂ)
    (a b A B : ℝ)
    (m : ℕ)
    (hA : 0 < A)
    (hB : 0 < B)
    (hleft :
      ∀ z : ℂ,
        z.re = a →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m))
    (hright :
      ∀ z : ℂ,
        z.re = b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m)) :
    (∀ z : ℂ,
      z.re = a →
      1 ≤ z.im →
      ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) ∧
    (∀ z : ℂ,
      z.re = b →
      1 ≤ z.im →
      ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) := by
  have hA_nonneg : 0 ≤ A :=
    le_of_lt hA
  have hB_nonneg : 0 ≤ B :=
    le_of_lt hB
  have hleft_complex :
      ∀ z : ℂ,
        z.re = a →
        1 ≤ z.im →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) :=
    fun z hz_re hz_im =>
      le_trans
        (hleft z hz_re (upperTail_im_norm_ge_one z hz_im))
        (finiteOrder_vertical_envelope_le_complex_envelope
          hA_nonneg
          hB_nonneg)
  have hright_complex :
      ∀ z : ℂ,
        z.re = b →
        1 ≤ z.im →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) :=
    fun z hz_re hz_im =>
      le_trans
        (hright z hz_re (upperTail_im_norm_ge_one z hz_im))
        (finiteOrder_vertical_envelope_le_complex_envelope
          hA_nonneg
          hB_nonneg)
  exact ⟨hleft_complex, hright_complex⟩

/-- Existential packaging of upper-tail vertical-boundary envelope transport to
ordinary complex height. -/
theorem strip_upperTail_vertical_boundary_package_complex_height_bound
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hvertical_boundary :
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
        1 ≤ z.im →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) ∧
      (∀ z : ℂ,
        z.re = b →
        1 ≤ z.im →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) := by
  match hvertical_boundary with
  | ⟨A, B, m, hA, hB, hleft, hright⟩ =>
      match
        strip_upperTail_vertical_boundary_envelope_complex_height_bound
          f a b A B m hA hB hleft hright
      with
      | ⟨hleft_complex, hright_complex⟩ =>
          exact ⟨A, B, m, hA, hB, hleft_complex, hright_complex⟩

/-- Upper-tail boundary finite-order envelopes are handled by matching real
boundary damping, independently of the subcritical interior exponent.

This is the boundary-side owner fact used in the finite-order strip argument:
the non-holomorphic real factor is only a boundary normalization device.  The
holomorphic PL function still uses a separate damping factor whose only
interior-growth role is norm control by one. -/
theorem strip_upperTail_vertical_boundary_real_damping_unit_bound
    (f : ℂ → ℂ)
    (a b A B : ℝ)
    (m : ℕ)
    (hA : 0 < A)
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
      1 ≤ z.im →
      A⁻¹ * Real.exp (-(B * (1 + ‖z.im‖) ^ m)) * ‖f z‖ ≤ 1) ∧
    (∀ z : ℂ,
      z.re = b →
      1 ≤ z.im →
      A⁻¹ * Real.exp (-(B * (1 + ‖z.im‖) ^ m)) * ‖f z‖ ≤ 1) := by
  let hunit :=
    strip_vertical_boundary_envelope_exp_damped_unit_bound
      f a b A B m hA hboundary
  exact
    ⟨fun z hz_re hz_im =>
        hunit.1 z hz_re (upperTail_im_norm_ge_one z hz_im),
      fun z hz_re hz_im =>
        hunit.2 z hz_re (upperTail_im_norm_ge_one z hz_im)⟩

/-- Upper-tail boundary real damping can be read with the ordinary complex
height in the exponential normalizer.

This is the algebraic height-transport step needed before the fixed-envelope
normalized construction: the boundary envelope is originally stated in
`‖z.im‖`, while the normalized upper-tail package below uses `‖z‖`. -/
theorem strip_upperTail_vertical_boundary_complex_height_real_damping_unit_bound
    (f : ℂ → ℂ)
    (a b A B : ℝ)
    (m : ℕ)
    (hA : 0 < A)
    (hB : 0 < B)
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
      1 ≤ z.im →
      A⁻¹ * Real.exp (-(B * (1 + ‖z‖) ^ m)) * ‖f z‖ ≤ 1) ∧
    (∀ z : ℂ,
      z.re = b →
      1 ≤ z.im →
      A⁻¹ * Real.exp (-(B * (1 + ‖z‖) ^ m)) * ‖f z‖ ≤ 1) := by
  have hunit_vertical :
      (∀ z : ℂ,
        z.re = a →
        1 ≤ z.im →
        A⁻¹ * Real.exp (-(B * (1 + ‖z.im‖) ^ m)) * ‖f z‖ ≤ 1) ∧
      (∀ z : ℂ,
        z.re = b →
        1 ≤ z.im →
        A⁻¹ * Real.exp (-(B * (1 + ‖z.im‖) ^ m)) * ‖f z‖ ≤ 1) :=
    strip_upperTail_vertical_boundary_real_damping_unit_bound
      f a b A B m hA hboundary
  have hAinv_nonneg : 0 ≤ A⁻¹ :=
    inv_nonneg.mpr (le_of_lt hA)
  have hB_nonneg : 0 ≤ B :=
    le_of_lt hB
  let transport :
      ∀ z : ℂ,
        A⁻¹ * Real.exp (-(B * (1 + ‖z‖) ^ m)) * ‖f z‖ ≤
          A⁻¹ * Real.exp (-(B * (1 + ‖z.im‖) ^ m)) * ‖f z‖ :=
    fun z =>
      have henv :
          Real.exp (B * (1 + ‖z.im‖) ^ m) ≤
            Real.exp (B * (1 + ‖z‖) ^ m) :=
        have henv_one :
            (1 : ℝ) * Real.exp (B * (1 + ‖z.im‖) ^ m) ≤
              (1 : ℝ) * Real.exp (B * (1 + ‖z‖) ^ m) :=
          finiteOrder_vertical_envelope_le_complex_envelope
            (show 0 ≤ (1 : ℝ) from zero_le_one)
            hB_nonneg
        have hleft_one :
            (1 : ℝ) * Real.exp (B * (1 + ‖z.im‖) ^ m) =
              Real.exp (B * (1 + ‖z.im‖) ^ m) :=
          one_mul (Real.exp (B * (1 + ‖z.im‖) ^ m))
        have hright_one :
            (1 : ℝ) * Real.exp (B * (1 + ‖z‖) ^ m) =
              Real.exp (B * (1 + ‖z‖) ^ m) :=
          one_mul (Real.exp (B * (1 + ‖z‖) ^ m))
        Eq.subst
          (motive := fun lhs : ℝ =>
            lhs ≤ Real.exp (B * (1 + ‖z‖) ^ m))
          hleft_one
          (Eq.subst
            (motive := fun rhs : ℝ =>
              (1 : ℝ) * Real.exp (B * (1 + ‖z.im‖) ^ m) ≤ rhs)
            hright_one
            henv_one)
      have hneg_exp :
          Real.exp (-(B * (1 + ‖z‖) ^ m)) ≤
            Real.exp (-(B * (1 + ‖z.im‖) ^ m)) := by
        have hpos_vertical :
            0 < Real.exp (B * (1 + ‖z.im‖) ^ m) :=
          Real.exp_pos (B * (1 + ‖z.im‖) ^ m)
        have hinv :
            (Real.exp (B * (1 + ‖z‖) ^ m))⁻¹ ≤
              (Real.exp (B * (1 + ‖z.im‖) ^ m))⁻¹ :=
          inv_anti₀ hpos_vertical henv
        have hcomplex_inv :
            Real.exp (-(B * (1 + ‖z‖) ^ m)) =
              (Real.exp (B * (1 + ‖z‖) ^ m))⁻¹ :=
          Real.exp_neg (B * (1 + ‖z‖) ^ m)
        have hvertical_inv :
            Real.exp (-(B * (1 + ‖z.im‖) ^ m)) =
              (Real.exp (B * (1 + ‖z.im‖) ^ m))⁻¹ :=
          Real.exp_neg (B * (1 + ‖z.im‖) ^ m)
        exact
          Eq.subst
            (motive := fun x : ℝ =>
              x ≤ Real.exp (-(B * (1 + ‖z.im‖) ^ m)))
            hcomplex_inv.symm
            (Eq.subst
              (motive := fun x : ℝ =>
                (Real.exp (B * (1 + ‖z‖) ^ m))⁻¹ ≤ x)
              hvertical_inv.symm
              hinv)
      have hscaled₁ :
          A⁻¹ * Real.exp (-(B * (1 + ‖z‖) ^ m)) ≤
            A⁻¹ * Real.exp (-(B * (1 + ‖z.im‖) ^ m)) :=
        mul_le_mul_of_nonneg_left hneg_exp hAinv_nonneg
      have hnorm_nonneg : 0 ≤ ‖f z‖ :=
        norm_nonneg (f z)
      mul_le_mul_of_nonneg_right hscaled₁ hnorm_nonneg
  exact
    ⟨fun z hz_re hz_im =>
        le_trans (transport z) (hunit_vertical.1 z hz_re hz_im),
      fun z hz_re hz_im =>
        le_trans (transport z) (hunit_vertical.2 z hz_re hz_im)⟩

/-- Existential upper-tail form of boundary finite-order real damping.

The resulting constants and degree come only from the boundary envelope.  No
condition comparing the strip subcritical exponent with a tilted holomorphic
damping scale is involved. -/
theorem strip_upperTail_vertical_boundary_package_real_damping_unit_bound
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hvertical_boundary :
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
        1 ≤ z.im →
        A⁻¹ * Real.exp (-(B * (1 + ‖z.im‖) ^ m)) * ‖f z‖ ≤ 1) ∧
      (∀ z : ℂ,
        z.re = b →
        1 ≤ z.im →
        A⁻¹ * Real.exp (-(B * (1 + ‖z.im‖) ^ m)) * ‖f z‖ ≤ 1) := by
  match hvertical_boundary with
  | ⟨A, B, m, hA, hB, hleft, hright⟩ =>
      match
        strip_upperTail_vertical_boundary_real_damping_unit_bound
          f a b A B m hA ⟨hleft, hright⟩
      with
      | ⟨hleft_unit, hright_unit⟩ =>
          exact ⟨A, B, m, hA, hB, hleft_unit, hright_unit⟩

/-- Existential upper-tail boundary real damping with ordinary complex height
in the normalizing exponential. -/
theorem strip_upperTail_vertical_boundary_package_complex_height_real_damping_unit_bound
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hvertical_boundary :
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
        1 ≤ z.im →
        A⁻¹ * Real.exp (-(B * (1 + ‖z‖) ^ m)) * ‖f z‖ ≤ 1) ∧
      (∀ z : ℂ,
        z.re = b →
        1 ≤ z.im →
        A⁻¹ * Real.exp (-(B * (1 + ‖z‖) ^ m)) * ‖f z‖ ≤ 1) := by
  match hvertical_boundary with
  | ⟨A, B, m, hA, hB, hleft, hright⟩ =>
      match
        strip_upperTail_vertical_boundary_complex_height_real_damping_unit_bound
          f a b A B m hA hB ⟨hleft, hright⟩
      with
      | ⟨hleft_unit, hright_unit⟩ =>
          exact ⟨A, B, m, hA, hB, hleft_unit, hright_unit⟩

/-- The complex-height boundary real-damping normalization is preserved,
uniformly in the positive parameter, by the holomorphic upper-tail damping
factor. -/
theorem verticalStripUpperTailDampedFamily_boundary_complex_height_real_damping_unit_bound
    (f : ℂ → ℂ)
    (a b A B ε : ℝ)
    (m : ℕ)
    (hab : a < b)
    (hε : 0 ≤ ε)
    (hA : 0 < A)
    (hB : 0 < B)
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
      1 ≤ z.im →
      A⁻¹ * Real.exp (-(B * (1 + ‖z‖) ^ m)) *
          ‖verticalStripUpperTailDampedFamily f a b ε z‖ ≤ 1) ∧
    (∀ z : ℂ,
      z.re = b →
      1 ≤ z.im →
      A⁻¹ * Real.exp (-(B * (1 + ‖z‖) ^ m)) *
          ‖verticalStripUpperTailDampedFamily f a b ε z‖ ≤ 1) := by
  have hunit :
      (∀ z : ℂ,
        z.re = a →
        1 ≤ z.im →
        A⁻¹ * Real.exp (-(B * (1 + ‖z‖) ^ m)) * ‖f z‖ ≤ 1) ∧
      (∀ z : ℂ,
        z.re = b →
        1 ≤ z.im →
        A⁻¹ * Real.exp (-(B * (1 + ‖z‖) ^ m)) * ‖f z‖ ≤ 1) :=
    strip_upperTail_vertical_boundary_complex_height_real_damping_unit_bound
      f a b A B m hA hB hboundary
  have hscale_nonneg :
      ∀ z : ℂ,
        0 ≤ A⁻¹ * Real.exp (-(B * (1 + ‖z‖) ^ m)) :=
    fun z =>
      mul_nonneg
        (inv_nonneg.mpr (le_of_lt hA))
        (le_of_lt (Real.exp_pos (-(B * (1 + ‖z‖) ^ m))))
  exact
    ⟨fun z hz_re hz_im =>
        have hza : a ≤ z.re :=
          le_of_eq hz_re.symm
        have hzb : z.re ≤ b :=
          le_trans (le_of_eq hz_re) (le_of_lt hab)
        have hdamped_le :
            ‖verticalStripUpperTailDampedFamily f a b ε z‖ ≤ ‖f z‖ :=
          verticalStripUpperTailDampedFamily_norm_le_original_on_closedStrip
            f a b ε hε z hza hzb
        have hscaled :
            A⁻¹ * Real.exp (-(B * (1 + ‖z‖) ^ m)) *
                ‖verticalStripUpperTailDampedFamily f a b ε z‖ ≤
              A⁻¹ * Real.exp (-(B * (1 + ‖z‖) ^ m)) * ‖f z‖ :=
          mul_le_mul_of_nonneg_left hdamped_le (hscale_nonneg z)
        le_trans hscaled (hunit.1 z hz_re hz_im),
      fun z hz_re hz_im =>
        have hza : a ≤ z.re :=
          le_trans (le_of_lt hab) (le_of_eq hz_re.symm)
        have hzb : z.re ≤ b :=
          le_of_eq hz_re
        have hdamped_le :
            ‖verticalStripUpperTailDampedFamily f a b ε z‖ ≤ ‖f z‖ :=
          verticalStripUpperTailDampedFamily_norm_le_original_on_closedStrip
            f a b ε hε z hza hzb
        have hscaled :
            A⁻¹ * Real.exp (-(B * (1 + ‖z‖) ^ m)) *
                ‖verticalStripUpperTailDampedFamily f a b ε z‖ ≤
              A⁻¹ * Real.exp (-(B * (1 + ‖z‖) ^ m)) * ‖f z‖ :=
          mul_le_mul_of_nonneg_left hdamped_le (hscale_nonneg z)
        le_trans hscaled (hunit.2 z hz_re hz_im)⟩

/-- Packaged form of the uniform boundary real-damping normalization for the
upper-tail holomorphic damped family. -/
theorem verticalStripUpperTailDampedFamily_boundary_package_complex_height_real_damping_unit_bound
    (f : ℂ → ℂ)
    (a b ε : ℝ)
    (hab : a < b)
    (hε : 0 ≤ ε)
    (hvertical_boundary :
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
        1 ≤ z.im →
        A⁻¹ * Real.exp (-(B * (1 + ‖z‖) ^ m)) *
            ‖verticalStripUpperTailDampedFamily f a b ε z‖ ≤ 1) ∧
      (∀ z : ℂ,
        z.re = b →
        1 ≤ z.im →
        A⁻¹ * Real.exp (-(B * (1 + ‖z‖) ^ m)) *
            ‖verticalStripUpperTailDampedFamily f a b ε z‖ ≤ 1) := by
  match hvertical_boundary with
  | ⟨A, B, m, hA, hB, hleft, hright⟩ =>
      match
        verticalStripUpperTailDampedFamily_boundary_complex_height_real_damping_unit_bound
          f a b A B ε m hab hε hA hB ⟨hleft, hright⟩
      with
      | ⟨hleft_unit, hright_unit⟩ =>
          exact ⟨A, B, m, hA, hB, hleft_unit, hright_unit⟩

/-- Uniform normalized Phragmen-Lindelöf inputs for the upper-tail holomorphic
damped family.

For every nonnegative damping parameter, the holomorphic upper-tail damped
family has the same complex-height boundary real-damping normalization constants
as the original boundary envelope, while retaining the strip holomorphy and
subcritical finite-order growth package. -/
theorem verticalStripUpperTailDampedFamily_uniform_normalized_PL_inputs
    (f : ℂ → ℂ)
    (a b A B : ℝ)
    (m : ℕ)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (hfinite :
      ∃ c : ℝ,
        c < Real.pi / (b - a) ∧
        ∃ D : ℝ,
          f =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)))
    (hab : a < b)
    (hA : 0 < A)
    (hB : 0 < B)
    (hboundary :
      (∀ z : ℂ,
        z.re = a →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m)) ∧
      (∀ z : ℂ,
        z.re = b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m))) :
    ∀ ε : ℝ,
      0 ≤ ε →
      DiffContOnCl ℂ (verticalStripUpperTailDampedFamily f a b ε)
          (Complex.re ⁻¹' Set.Ioo a b) ∧
        (∃ c : ℝ,
          c < Real.pi / (b - a) ∧
          ∃ D : ℝ,
            verticalStripUpperTailDampedFamily f a b ε =O[
                Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                  𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
              fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|))) ∧
        (∀ z : ℂ,
          z.re = a →
          1 ≤ z.im →
          A⁻¹ * Real.exp (-(B * (1 + ‖z‖) ^ m)) *
              ‖verticalStripUpperTailDampedFamily f a b ε z‖ ≤ 1) ∧
        (∀ z : ℂ,
          z.re = b →
          1 ≤ z.im →
          A⁻¹ * Real.exp (-(B * (1 + ‖z‖) ^ m)) *
              ‖verticalStripUpperTailDampedFamily f a b ε z‖ ≤ 1) := by
  intro ε hε
  have hanalytic :
      DiffContOnCl ℂ (verticalStripUpperTailDampedFamily f a b ε)
          (Complex.re ⁻¹' Set.Ioo a b) ∧
        ∃ c : ℝ,
          c < Real.pi / (b - a) ∧
          ∃ D : ℝ,
            verticalStripUpperTailDampedFamily f a b ε =O[
                Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                  𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
              fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) :=
    verticalStripUpperTailDampedFamily_analytic_growth_package
      f a b ε hhol hfinite hε
  have hunit :
      (∀ z : ℂ,
        z.re = a →
        1 ≤ z.im →
        A⁻¹ * Real.exp (-(B * (1 + ‖z‖) ^ m)) *
            ‖verticalStripUpperTailDampedFamily f a b ε z‖ ≤ 1) ∧
      (∀ z : ℂ,
        z.re = b →
        1 ≤ z.im →
        A⁻¹ * Real.exp (-(B * (1 + ‖z‖) ^ m)) *
            ‖verticalStripUpperTailDampedFamily f a b ε z‖ ≤ 1) :=
    verticalStripUpperTailDampedFamily_boundary_complex_height_real_damping_unit_bound
      f a b A B ε m hab hε hA hB hboundary
  exact ⟨hanalytic.1, hanalytic.2, hunit.1, hunit.2⟩

/-- Undo a positive fixed-envelope real normalization at one point. -/
theorem fixedEnvelope_bound_of_complex_height_real_damping_unit
    {A B x : ℝ}
    {m : ℕ}
    {z : ℂ}
    (hA : 0 < A)
    (hunit :
      A⁻¹ * Real.exp (-(B * (1 + ‖z‖) ^ m)) * x ≤ 1) :
    x ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  let X : ℝ := B * (1 + ‖z‖) ^ m
  let E : ℝ := Real.exp X
  let En : ℝ := Real.exp (-X)
  let S : ℝ := A * E
  let C : ℝ := A⁻¹ * En
  have hS_pos : 0 < S :=
    mul_pos hA (Real.exp_pos X)
  have hC_mul_S : C * S = 1 := by
    have hcollapse : En * S = A := by
      exact exp_negative_growth_mul_growth_cancel A X
    calc
      C * S = (A⁻¹ * En) * S := rfl
      _ = A⁻¹ * (En * S) := mul_assoc A⁻¹ En S
      _ = A⁻¹ * A := congrArg (fun y : ℝ => A⁻¹ * y) hcollapse
      _ = 1 := inv_mul_cancel₀ hA.ne'
  have hscaled :
      (C * x) * S ≤ 1 * S :=
    mul_le_mul_of_nonneg_right hunit (le_of_lt hS_pos)
  have hleft :
      (C * x) * S = x := by
    calc
      (C * x) * S = C * (x * S) := mul_assoc C x S
      _ = C * (S * x) := congrArg (fun y : ℝ => C * y) (mul_comm x S)
      _ = (C * S) * x := (mul_assoc C S x).symm
      _ = 1 * x := congrArg (fun y : ℝ => y * x) hC_mul_S
      _ = x := one_mul x
  have hright : 1 * S = S :=
    one_mul S
  exact
    Eq.subst
      (motive := fun lhs : ℝ => lhs ≤ S)
      hleft
      (Eq.subst
        (motive := fun rhs : ℝ => (C * x) * S ≤ rhs)
        hright
        hscaled)

/-- The uniform complex-height normalized boundary package gives the upper-tail
damped family the same fixed finite-order boundary envelope, independently of
the damping parameter. -/
theorem verticalStripUpperTailDampedFamily_uniform_boundary_fixedEnvelope
    (f : ℂ → ℂ)
    (a b A B ε : ℝ)
    (m : ℕ)
    (hab : a < b)
    (hε : 0 ≤ ε)
    (hA : 0 < A)
    (hB : 0 < B)
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
      1 ≤ z.im →
      ‖verticalStripUpperTailDampedFamily f a b ε z‖ ≤
        A * Real.exp (B * (1 + ‖z‖) ^ m)) ∧
    (∀ z : ℂ,
      z.re = b →
      1 ≤ z.im →
      ‖verticalStripUpperTailDampedFamily f a b ε z‖ ≤
        A * Real.exp (B * (1 + ‖z‖) ^ m)) := by
  have hunit :
      (∀ z : ℂ,
        z.re = a →
        1 ≤ z.im →
        A⁻¹ * Real.exp (-(B * (1 + ‖z‖) ^ m)) *
            ‖verticalStripUpperTailDampedFamily f a b ε z‖ ≤ 1) ∧
      (∀ z : ℂ,
        z.re = b →
        1 ≤ z.im →
        A⁻¹ * Real.exp (-(B * (1 + ‖z‖) ^ m)) *
            ‖verticalStripUpperTailDampedFamily f a b ε z‖ ≤ 1) :=
    verticalStripUpperTailDampedFamily_boundary_complex_height_real_damping_unit_bound
      f a b A B ε m hab hε hA hB hboundary
  exact
    ⟨fun z hz_re hz_im =>
        fixedEnvelope_bound_of_complex_height_real_damping_unit
          (z := z) hA (hunit.1 z hz_re hz_im),
      fun z hz_re hz_im =>
        fixedEnvelope_bound_of_complex_height_real_damping_unit
          (z := z) hA (hunit.2 z hz_re hz_im)⟩

/-- The subcritical cosine-damped family has the same upper-tail finite-order
vertical-boundary envelope as the original function, uniformly in the positive
damping parameter. -/
theorem verticalStripSubcriticalCosineDampedFamily_uniform_boundary_fixedEnvelope
    (f : ℂ → ℂ)
    (a b d A B ε : ℝ)
    (m : ℕ)
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    (hε : 0 ≤ ε)
    (hA : 0 < A)
    (hB : 0 < B)
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
      1 ≤ z.im →
      ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤
        A * Real.exp (B * (1 + ‖z‖) ^ m)) ∧
    (∀ z : ℂ,
      z.re = b →
      1 ≤ z.im →
      ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤
        A * Real.exp (B * (1 + ‖z‖) ^ m)) := by
  have hcomplex :
      (∀ z : ℂ,
        z.re = a →
        1 ≤ z.im →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) ∧
      (∀ z : ℂ,
        z.re = b →
        1 ≤ z.im →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) :=
    strip_upperTail_vertical_boundary_envelope_complex_height_bound
      f a b A B m hA hB hboundary.1 hboundary.2
  exact
    verticalStripSubcriticalCosineDampedFamily_upperTail_boundary_envelope
      f hab hd_pos hd_threshold hε hcomplex.1 hcomplex.2

/-- Uniform analytic and vertical-boundary finite-envelope package for the
subcritical cosine-damped family. -/
theorem verticalStripSubcriticalCosineDampedFamily_uniform_finiteEnvelope_inputs
    (f : ℂ → ℂ)
    (a b A B : ℝ)
    (m : ℕ)
    (hab : a < b)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))


    (hfinite :
      ∃ c : ℝ,
        c < Real.pi / (b - a) ∧
        ∃ D : ℝ,
          f =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)))
    (hA : 0 < A)
    (hB : 0 < B)
    (hboundary :
      (∀ z : ℂ,
        z.re = a →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m)) ∧
      (∀ z : ℂ,
        z.re = b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m))) :
    ∃ d : ℝ,
      0 < d ∧
      d < π / (b - a) ∧
      ∀ ε : ℝ,
        0 < ε →
        DiffContOnCl ℂ (verticalStripSubcriticalCosineDampedFamily f a b d ε)
            (Complex.re ⁻¹' Set.Ioo a b) ∧
          (∃ c : ℝ,
            c < Real.pi / (b - a) ∧
            ∃ D : ℝ,
              verticalStripSubcriticalCosineDampedFamily f a b d ε =O[
                  Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                    𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
                fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|))) ∧
          (∀ z : ℂ,
            z.re = a →
            1 ≤ z.im →
            ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤
              A * Real.exp (B * (1 + ‖z‖) ^ m)) ∧
          (∀ z : ℂ,
            z.re = b →
            1 ≤ z.im →
            ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤
              A * Real.exp (B * (1 + ‖z‖) ^ m)) := by
  match hfinite with
  | ⟨c, hc, D, hD⟩ =>
      match exists_verticalStrip_subcritical_cosineBarrier_rate hab hc with
      | ⟨d, _hcd, hd_pos, hd_threshold⟩ =>
          exact
            ⟨d, hd_pos, hd_threshold,
              fun ε hε_pos =>
                have hpackage :
                    DiffContOnCl ℂ
                        (verticalStripSubcriticalCosineDampedFamily f a b d ε)
                        (Complex.re ⁻¹' Set.Ioo a b) ∧
                      ∃ c : ℝ,
                        c < Real.pi / (b - a) ∧
                        ∃ D : ℝ,
                          verticalStripSubcriticalCosineDampedFamily f a b d ε =O[
                              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                                𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
                            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) :=
                  verticalStripSubcriticalCosineDampedFamily_analytic_growth_package
                    f hab hd_pos hd_threshold (le_of_lt hε_pos) hhol hfinite
                have hboundaryε :
                    (∀ z : ℂ,
                      z.re = a →
                      1 ≤ z.im →
                      ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤
                        A * Real.exp (B * (1 + ‖z‖) ^ m)) ∧
                    (∀ z : ℂ,
                      z.re = b →
                      1 ≤ z.im →
                      ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤
                        A * Real.exp (B * (1 + ‖z‖) ^ m)) :=
                  verticalStripSubcriticalCosineDampedFamily_uniform_boundary_fixedEnvelope
                    f a b d A B ε m hab hd_pos hd_threshold
                    (le_of_lt hε_pos) hA hB hboundary
                ⟨hpackage.1, hpackage.2, hboundaryε.1, hboundaryε.2⟩⟩


end
end LFunctions
end Boundary
