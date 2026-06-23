import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaBoundaryPL.DampedFamily.Kernels

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Filter Topology
local notation "π" => Real.pi

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

/-- Separate finite-order boundary envelopes on the two strip sides have one common
vertical-height finite-order envelope.

This is the algebraic boundary normalization needed before introducing the genuine
damped family.  It combines the two side envelopes, then rewrites the common
complex-height envelope as a vertical-height envelope using the bounded-strip
height comparison. -/
theorem strip_boundary_envelopes_common_vertical_height_bound
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hab : a < b)
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
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m)) ∧
      (∀ z : ℂ,
        z.re = b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m)) := by
  have hcommon :
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
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) :=
    strip_boundary_growth_envelopes_common_bound f a b hleft hright
  exact
    strip_common_boundary_envelope_vertical_height_bound f a b hab hcommon


end
end LFunctions
end Boundary
