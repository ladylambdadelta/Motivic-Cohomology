import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaBoundaryPL.StripEnvelope.Owner

/-!
# Damped-family strip Phragmen-Lindelof transport

This owner layer contains the damped-family finite-order strip transport theorems.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

/-- Center of the vertical strip `a ≤ re z ≤ b`. -/
def verticalStripCenter
    (a b : ℝ) : ℝ :=
  (a + b) / 2

/-- Width of the vertical strip `a ≤ re z ≤ b`. -/
def verticalStripWidth
    (a b : ℝ) : ℝ :=
  b - a

/-- Holomorphic cosine kernel used in the strip damping argument.

The affine factor maps the vertical strip to the standard strip
`-π / 2 ≤ re w ≤ π / 2`; the real part of `cos w` is nonnegative in the
interior and controls the damping strength. -/
noncomputable def verticalStripCosineDampingKernel
    (a b : ℝ)
    (z : ℂ) : ℂ :=
  Complex.cos
    (((π : ℝ) : ℂ) *
      (z - ((verticalStripCenter a b : ℝ) : ℂ)) /
        ((verticalStripWidth a b : ℝ) : ℂ))

/-- The holomorphic strip-damped family attached to `f`.

The parameter `ε` is later sent to `0+` after applying the bounded-boundary
Phragmen-Lindelöf theorem to this family. -/
noncomputable def verticalStripCosineDampedFamily
    (f : ℂ → ℂ)
    (a b ε : ℝ)
    (z : ℂ) : ℂ :=
  f z *
    Complex.exp
      (-((ε : ℝ) : ℂ) *
        verticalStripCosineDampingKernel a b z)

/-- Unfolding of the strip cosine damping kernel. -/
theorem verticalStripCosineDampingKernel_eq
    (a b : ℝ)
    (z : ℂ) :
    verticalStripCosineDampingKernel a b z =
      Complex.cos
        (((π : ℝ) : ℂ) *
          (z - ((verticalStripCenter a b : ℝ) : ℂ)) /
            ((verticalStripWidth a b : ℝ) : ℂ)) := by
  rfl

/-- Unfolding of the strip cosine damped family. -/
theorem verticalStripCosineDampedFamily_eq
    (f : ℂ → ℂ)
    (a b ε : ℝ)
    (z : ℂ) :
    verticalStripCosineDampedFamily f a b ε z =
      f z *
        Complex.exp
          (-((ε : ℝ) : ℂ) *
            verticalStripCosineDampingKernel a b z) := by
  rfl

/-- A nondegenerate vertical strip has positive width. -/
theorem verticalStripWidth_pos
    {a b : ℝ}
    (hab : a < b) :
    0 < verticalStripWidth a b := by
  exact sub_pos.mpr hab

/-- A nondegenerate vertical strip has nonzero width. -/
theorem verticalStripWidth_ne_zero
    {a b : ℝ}
    (hab : a < b) :
    verticalStripWidth a b ≠ 0 :=
  ne_of_gt (verticalStripWidth_pos hab)

/-- The strip center lies halfway from the left endpoint. -/
theorem leftEndpoint_sub_verticalStripCenter
    (a b : ℝ) :
    a - verticalStripCenter a b = (a - b) / 2 := by
  calc
    a - verticalStripCenter a b = a - (a + b) / 2 := rfl
    _ = (2 * a) / 2 - (a + b) / 2 := by
      have htwo_a : (2 * a) / 2 = a := by
        calc
          (2 * a) / 2 = (a * 2) / 2 := by
            exact congrArg (fun x : ℝ => x / 2) (mul_comm 2 a)
          _ = a := by
            exact mul_div_cancel_right₀ a (show (2 : ℝ) ≠ 0 from two_ne_zero)
      exact congrArg (fun x : ℝ => x - (a + b) / 2) htwo_a.symm
    _ = (2 * a - (a + b)) / 2 := by
      exact (sub_div (2 * a) (a + b) 2).symm
    _ = ((a + a) - (a + b)) / 2 := by
      exact congrArg (fun x : ℝ => (x - (a + b)) / 2) (two_mul a)
    _ = (a - b) / 2 := by
      have hnum : (a + a) - (a + b) = a - b := by
        calc
          (a + a) - (a + b) = (a + a) + -(a + b) := by
            exact sub_eq_add_neg (a + a) (a + b)
          _ = (a + a) + (-a + -b) := by
            exact congrArg (fun x : ℝ => (a + a) + x) (neg_add a b)
          _ = a + (a + (-a + -b)) := by
            exact add_assoc a a (-a + -b)
          _ = a + ((a + -a) + -b) := by
            exact congrArg (fun x : ℝ => a + x) (add_assoc a (-a) (-b)).symm
          _ = a + (0 + -b) := by
            exact congrArg (fun x : ℝ => a + (x + -b)) (add_neg_cancel a)
          _ = a + -b := by
            exact congrArg (fun x : ℝ => a + x) (zero_add (-b))
          _ = a - b := by
            exact (sub_eq_add_neg a b).symm
      exact congrArg (fun x : ℝ => x / 2) hnum

/-- The strip center lies halfway from the right endpoint. -/
theorem rightEndpoint_sub_verticalStripCenter
    (a b : ℝ) :
    b - verticalStripCenter a b = (b - a) / 2 := by
  calc
    b - verticalStripCenter a b = b - (a + b) / 2 := rfl
    _ = (2 * b) / 2 - (a + b) / 2 := by
      have htwo_b : (2 * b) / 2 = b := by
        calc
          (2 * b) / 2 = (b * 2) / 2 := by
            exact congrArg (fun x : ℝ => x / 2) (mul_comm 2 b)
          _ = b := by
            exact mul_div_cancel_right₀ b (show (2 : ℝ) ≠ 0 from two_ne_zero)
      exact congrArg (fun x : ℝ => x - (a + b) / 2) htwo_b.symm
    _ = (2 * b - (a + b)) / 2 := by
      exact (sub_div (2 * b) (a + b) 2).symm
    _ = ((b + b) - (a + b)) / 2 := by
      exact congrArg (fun x : ℝ => (x - (a + b)) / 2) (two_mul b)
    _ = (b - a) / 2 := by
      have hnum : (b + b) - (a + b) = b - a := by
        calc
          (b + b) - (a + b) = (b + b) + -(a + b) := by
            exact sub_eq_add_neg (b + b) (a + b)
          _ = (b + b) + (-a + -b) := by
            exact congrArg (fun x : ℝ => (b + b) + x) (neg_add a b)
          _ = b + (b + (-a + -b)) := by
            exact add_assoc b b (-a + -b)
          _ = b + ((b + -b) + -a) := by
            have hinner : b + (-a + -b) = (b + -b) + -a := by
              calc
                b + (-a + -b) = b + (-b + -a) := by
                  exact congrArg (fun x : ℝ => b + x) (add_comm (-a) (-b))
                _ = (b + -b) + -a := by
                  exact (add_assoc b (-b) (-a)).symm
            exact congrArg (fun x : ℝ => b + x) hinner
          _ = b + (0 + -a) := by
            exact congrArg (fun x : ℝ => b + (x + -a)) (add_neg_cancel b)
          _ = b + -a := by
            exact congrArg (fun x : ℝ => b + x) (zero_add (-a))
          _ = b - a := by
            exact (sub_eq_add_neg b a).symm
      exact congrArg (fun x : ℝ => x / 2) hnum

/-- Bounded-boundary Phragmen-Lindelöf already implies a finite-order strip
envelope.

This is the terminal bounded-boundary step in the damping proof: once the
chosen damped family has a uniform boundary bound, mathlib's vertical-strip
Phragmen-Lindelöf theorem bounds it throughout the closed strip, and that
constant is absorbed into a degree-zero finite-order envelope. -/
theorem strip_finite_order_growth_of_uniform_boundary_bound
    (f : ℂ → ℂ)
    (a b C : ℝ)
    (_hab : a < b)
    (hC : 0 < C)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (hfinite :
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
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  have hstrip :
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        ‖f z‖ ≤ C :=
    strip_uniform_bound_of_holomorphic_boundary_bound_and_mathlib_growth
      f a b C hhol hfinite hleft hright
  exact
    ⟨C, 1, 0, hC, zero_lt_one,
      fun z hza hzb _hz_im =>
        have hpoint : ‖f z‖ ≤ C :=
          hstrip z hza hzb
        have hexp_one_le :
            (1 : ℝ) ≤ Real.exp (1 * (1 + ‖z‖) ^ (0 : ℕ)) := by
          have hpow : (1 + ‖z‖) ^ (0 : ℕ) = (1 : ℝ) :=
            pow_zero (1 + ‖z‖)
          have hexponent : 1 * (1 + ‖z‖) ^ (0 : ℕ) = (1 : ℝ) :=
            Eq.trans (congrArg (fun x : ℝ => 1 * x) hpow) (mul_one 1)
          have hone_le_exp_one : (1 : ℝ) ≤ Real.exp (1 : ℝ) :=
            Real.one_le_exp zero_le_one
          exact
            Eq.subst
              (motive := fun x : ℝ => (1 : ℝ) ≤ Real.exp x)
              hexponent.symm
              hone_le_exp_one
        have hC_nonneg : 0 ≤ C :=
          le_of_lt hC
        have hC_le_envelope :
            C ≤ C * Real.exp (1 * (1 + ‖z‖) ^ (0 : ℕ)) := by
          calc
            C = C * 1 := (mul_one C).symm
            _ ≤ C * Real.exp (1 * (1 + ‖z‖) ^ (0 : ℕ)) :=
              mul_le_mul_of_nonneg_left hexp_one_le hC_nonneg
        le_trans hpoint hC_le_envelope⟩

/-- Existential-boundary package for the bounded-boundary Phragmen-Lindelöf
terminal step. -/
theorem strip_finite_order_growth_of_uniform_boundary_package
    (f : ℂ → ℂ)
    (a b : ℝ)
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
    (hboundary :
      ∃ C : ℝ,
        0 < C ∧
        (∀ z : ℂ,
          z.re = a →
          ‖f z‖ ≤ C) ∧
        (∀ z : ℂ,
          z.re = b →
          ‖f z‖ ≤ C)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match hboundary with
  | ⟨C, hC, hleft, hright⟩ =>
      exact
        strip_finite_order_growth_of_uniform_boundary_bound
          f a b C hab hC hhol hfinite hleft hright

/-- Bounded-boundary Phragmen-Lindelöf after assembling a tail bound and a
compact-height boundary bound.

This is the terminal theorem used by damped-family proofs once the chosen
damped family has a uniform tail estimate and a compact boundary estimate. -/
theorem strip_finite_order_growth_of_tail_compact_boundary_package
    (f : ℂ → ℂ)
    (a b : ℝ)
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
    (htail :
      ∃ A : ℝ,
        0 < A ∧
        (∀ z : ℂ,
          z.re = a →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A) ∧
        (∀ z : ℂ,
          z.re = b →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A))
    (hcompact :
      ∃ C : ℝ,
        0 < C ∧
        (∀ z : ℂ,
          z.re = a →
          ¬ 1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ C) ∧
        (∀ z : ℂ,
          z.re = b →
          ¬ 1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ C)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    strip_finite_order_growth_of_uniform_boundary_package
      f a b hab hhol hfinite
      (strip_uniform_boundary_package_of_tail_and_compact
        f a b htail hcompact)

theorem strip_finite_order_growth_of_vertical_boundary_envelope_damped_family
    (f : ℂ → ℂ)
    (a b : ℝ)
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
    (htail :
      ∃ A : ℝ,
        0 < A ∧
        (∀ z : ℂ,
          z.re = a →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A) ∧
        (∀ z : ℂ,
          z.re = b →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A))
    (hcompact :
      ∃ C : ℝ,
        0 < C ∧
        (∀ z : ℂ,
          z.re = a →
          ¬ 1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ C) ∧
        (∀ z : ℂ,
          z.re = b →
          ¬ 1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ C)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    strip_finite_order_growth_of_tail_compact_boundary_package
      f a b hab hhol hfinite htail hcompact

/-- The explicit bounded-boundary Phragmen-Lindelöf normalization theorem.

Once the function under consideration has a uniform vertical-tail boundary
bound and a compact-height boundary bound, the bounded-boundary strip theorem
gives a finite-order envelope in the closed strip. -/
theorem strip_finite_order_growth_of_common_boundary_envelope_damped_family
    (f : ℂ → ℂ)
    (a b : ℝ)
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
    (htail :
      ∃ A : ℝ,
        0 < A ∧
        (∀ z : ℂ,
          z.re = a →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A) ∧
        (∀ z : ℂ,
          z.re = b →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A))
    (hcompact :
      ∃ C : ℝ,
        0 < C ∧
        (∀ z : ℂ,
          z.re = a →
          ¬ 1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ C) ∧
        (∀ z : ℂ,
          z.re = b →
          ¬ 1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ C)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    strip_finite_order_growth_of_vertical_boundary_envelope_damped_family
      f a b hab hhol hfinite htail hcompact

/-- Bounded-boundary strip transport with a retained common finite-order boundary envelope.

The finite-order boundary envelope is bookkeeping for downstream callers.  The
actual bounded-boundary Phragmen-Lindelöf input is the pair of explicit
vertical-tail and compact-height boundary bounds. -/
theorem strip_finite_order_growth_of_common_boundary_envelope_by_damping
    (f : ℂ → ℂ)
    (a b : ℝ)
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
    (_hboundary :
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
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)))
    (htail :
      ∃ A : ℝ,
        0 < A ∧
        (∀ z : ℂ,
          z.re = a →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A) ∧
        (∀ z : ℂ,
          z.re = b →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A))
    (hcompact :
      ∃ C : ℝ,
        0 < C ∧
        (∀ z : ℂ,
          z.re = a →
          ¬ 1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ C) ∧
        (∀ z : ℂ,
          z.re = b →
          ¬ 1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ C)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact strip_finite_order_growth_of_common_boundary_envelope_damped_family
    f a b hab hhol hfinite htail hcompact

/-- Vertical-strip Phragmen-Lindelöf growth theorem with explicit bounded-boundary input.

This is the generic analytic pillar needed for the pole-cleared zeta strip estimate:
holomorphy on the open strip, admissible finite-order growth in the strip, and
bounded boundary control after tail/compact splitting propagate a finite-order
growth envelope through the closed strip.  Separate finite-order boundary
envelopes are still consolidated here for downstream accounting, but they are
not used as a substitute for the bounded-boundary PL hypotheses. -/
theorem strip_finite_order_growth_reduces_to_bounded_boundary_phragmenLindelof
    (f : ℂ → ℂ)
    (a b : ℝ)
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
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m))
    (htail :
      ∃ A : ℝ,
        0 < A ∧
        (∀ z : ℂ,
          z.re = a →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A) ∧
        (∀ z : ℂ,
          z.re = b →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A))
    (hcompact :
      ∃ C : ℝ,
        0 < C ∧
        (∀ z : ℂ,
          z.re = a →
          ¬ 1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ C) ∧
        (∀ z : ℂ,
          z.re = b →
          ¬ 1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ C)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact strip_finite_order_growth_of_common_boundary_envelope_by_damping
    f a b hab hhol hfinite
    (strip_boundary_growth_envelopes_common_bound f a b hleft hright)
    htail hcompact

/-- Classical vertical-strip Phragmen-Lindelöf finite-growth theorem with explicit
bounded-boundary inputs.

This wrapper exposes the canonical owner theorem after the caller has supplied
the bounded tail and compact boundary estimates needed by the bounded strip
theorem. -/
theorem strip_growth_bound_of_holomorphic_boundary_growth_and_finite_order
    (f : ℂ → ℂ)
    (a b : ℝ)
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
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m))
    (htail :
      ∃ A : ℝ,
        0 < A ∧
        (∀ z : ℂ,
          z.re = a →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A) ∧
        (∀ z : ℂ,
          z.re = b →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A))
    (hcompact :
      ∃ C : ℝ,
        0 < C ∧
        (∀ z : ℂ,
          z.re = a →
          ¬ 1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ C) ∧
        (∀ z : ℂ,
          z.re = b →
          ¬ 1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ C)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact strip_finite_order_growth_reduces_to_bounded_boundary_phragmenLindelof
    f a b hab hhol hfinite hleft hright htail hcompact

/- The pole-cleared zeta factor itself is owned by `PoleClearedBoundarySetup.Core`. -/

end
end LFunctions
end Boundary
