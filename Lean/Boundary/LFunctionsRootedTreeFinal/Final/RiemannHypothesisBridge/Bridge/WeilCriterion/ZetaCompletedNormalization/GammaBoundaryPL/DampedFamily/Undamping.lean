import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaBoundaryPL.DampedFamily.CompactHeight

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Filter Topology
local notation "π" => Real.pi

/-- Pointwise zero-damping limit for the cosine-damped family. -/
theorem verticalStripCosineDampedFamily_tendsto_zeroDamping
    (f : ℂ → ℂ)
    (a b : ℝ)
    (z : ℂ) :
    Filter.Tendsto
      (fun ε : ℝ => verticalStripCosineDampedFamily f a b ε z)
      (𝓝[>] (0 : ℝ))
      (𝓝 (f z)) := by
  let K : ℂ := verticalStripCosineDampingKernel a b z
  have hε_complex :
      Filter.Tendsto
        (fun ε : ℝ => ((ε : ℝ) : ℂ))
        (𝓝[>] (0 : ℝ))
        (𝓝 (0 : ℂ)) :=
    Filter.Tendsto.mono_left
      Complex.continuous_ofReal.continuousAt
      nhdsWithin_le_nhds
  have hraw_exponent :
      Filter.Tendsto
        (fun ε : ℝ => -((ε : ℝ) : ℂ) * K)
        (𝓝[>] (0 : ℝ))
        (𝓝 (-(0 : ℂ) * K)) :=
    hε_complex.neg.mul tendsto_const_nhds
  have hzero_exponent : -(0 : ℂ) * K = 0 := by
    calc
      -(0 : ℂ) * K = (0 : ℂ) * K := by
        exact congrArg (fun w : ℂ => w * K) (neg_zero : -(0 : ℂ) = 0)
      _ = 0 := zero_mul K
  have hexponent :
      Filter.Tendsto
        (fun ε : ℝ => -((ε : ℝ) : ℂ) * K)
        (𝓝[>] (0 : ℝ))
        (𝓝 (0 : ℂ)) :=
    Eq.subst
      (motive := fun w : ℂ =>
        Filter.Tendsto
          (fun ε : ℝ => -((ε : ℝ) : ℂ) * K)
          (𝓝[>] (0 : ℝ))
          (𝓝 w))
      hzero_exponent
      hraw_exponent
  have hraw_factor :
      Filter.Tendsto
        (fun ε : ℝ => Complex.exp (-((ε : ℝ) : ℂ) * K))
        (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.exp (0 : ℂ))) :=
    (Complex.continuous_exp.tendsto (0 : ℂ)).comp hexponent
  have hone_factor : Complex.exp (0 : ℂ) = 1 :=
    Complex.exp_zero
  have hfactor :
      Filter.Tendsto
        (fun ε : ℝ => Complex.exp (-((ε : ℝ) : ℂ) * K))
        (𝓝[>] (0 : ℝ))
        (𝓝 (1 : ℂ)) :=
    Eq.subst
      (motive := fun w : ℂ =>
        Filter.Tendsto
          (fun ε : ℝ => Complex.exp (-((ε : ℝ) : ℂ) * K))
          (𝓝[>] (0 : ℝ))
          (𝓝 w))
      hone_factor
      hraw_factor
  have hraw_product :
      Filter.Tendsto
        (fun ε : ℝ =>
          f z * Complex.exp (-((ε : ℝ) : ℂ) * K))
        (𝓝[>] (0 : ℝ))
        (𝓝 (f z * (1 : ℂ))) :=
    tendsto_const_nhds.mul hfactor
  have hproduct_one : f z * (1 : ℂ) = f z :=
    mul_one (f z)
  have hproduct :
      Filter.Tendsto
        (fun ε : ℝ =>
          f z * Complex.exp (-((ε : ℝ) : ℂ) * K))
        (𝓝[>] (0 : ℝ))
        (𝓝 (f z)) :=
    Eq.subst
      (motive := fun w : ℂ =>
        Filter.Tendsto
          (fun ε : ℝ =>
            f z * Complex.exp (-((ε : ℝ) : ℂ) * K))
          (𝓝[>] (0 : ℝ))
          (𝓝 w))
      hproduct_one
      hraw_product
  exact
    hproduct.congr'
      (Eventually.of_forall
        fun ε : ℝ =>
          (verticalStripCosineDampedFamily_eq f a b ε z).symm)

/-- Norm form of the zero-damping limit for the cosine-damped family. -/
theorem verticalStripCosineDampedFamily_norm_tendsto_zeroDamping
    (f : ℂ → ℂ)
    (a b : ℝ)
    (z : ℂ) :
    Filter.Tendsto
      (fun ε : ℝ => ‖verticalStripCosineDampedFamily f a b ε z‖)
      (𝓝[>] (0 : ℝ))
      (𝓝 ‖f z‖) :=
  (verticalStripCosineDampedFamily_tendsto_zeroDamping f a b z).norm

/-- A closed real upper half-line bound passes to a one-sided limit. -/
theorem real_norm_bound_of_tendsto_from_positive_side
    {g : ℝ → ℝ}
    {L C : ℝ}
    (hlim : Filter.Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 L))
    (hbound : ∀ ε : ℝ, 0 < ε → g ε ≤ C) :
    L ≤ C := by
  have heventual :
      ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), g ε ≤ C :=
    mem_of_superset
      (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))
      (fun ε hε => hbound ε hε)
  exact
    le_of_tendsto hlim heventual

/-- Pointwise undamping through the zero-damping limit under a fixed finite-order
envelope.

This is the local limit step: for a fixed point in the strip, the cosine-damped
family tends to `f z` as `ε → 0+`, and the closed half-line
`{w | ‖w‖ ≤ envelope z}` contains all positive dampings. -/
theorem verticalStripCosineDampedFamily_uniform_envelope_undamps
    (f : ℂ → ℂ)
    (a b A B : ℝ)
    (m : ℕ)
    (z : ℂ)
    (huniform :
      ∀ ε : ℝ,
        0 < ε →
        ‖verticalStripCosineDampedFamily f a b ε z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    real_norm_bound_of_tendsto_from_positive_side
      (verticalStripCosineDampedFamily_norm_tendsto_zeroDamping f a b z)
      huniform

/-- Pointwise zero-damping limit for the subcritical cosine-damped family. -/
theorem verticalStripSubcriticalCosineDampedFamily_tendsto_zeroDamping
    (f : ℂ → ℂ)
    (a b d : ℝ)
    (z : ℂ) :
    Filter.Tendsto
      (fun ε : ℝ => verticalStripSubcriticalCosineDampedFamily f a b d ε z)
      (𝓝[>] (0 : ℝ))
      (𝓝 (f z)) := by
  let K : ℂ := verticalStripSubcriticalCosineBarrierKernel a b d z
  have hε_complex :
      Filter.Tendsto
        (fun ε : ℝ => ((ε : ℝ) : ℂ))
        (𝓝[>] (0 : ℝ))
        (𝓝 (0 : ℂ)) :=
    Filter.Tendsto.mono_left
      Complex.continuous_ofReal.continuousAt
      nhdsWithin_le_nhds
  have hraw_exponent :
      Filter.Tendsto
        (fun ε : ℝ => -((ε : ℝ) : ℂ) * K)
        (𝓝[>] (0 : ℝ))
        (𝓝 (-(0 : ℂ) * K)) :=
    hε_complex.neg.mul tendsto_const_nhds
  have hzero_exponent : -(0 : ℂ) * K = 0 := by
    calc
      -(0 : ℂ) * K = (0 : ℂ) * K := by
        exact congrArg (fun w : ℂ => w * K) (neg_zero : -(0 : ℂ) = 0)
      _ = 0 := zero_mul K
  have hexponent :
      Filter.Tendsto
        (fun ε : ℝ => -((ε : ℝ) : ℂ) * K)
        (𝓝[>] (0 : ℝ))
        (𝓝 (0 : ℂ)) :=
    Eq.subst
      (motive := fun w : ℂ =>
        Filter.Tendsto
          (fun ε : ℝ => -((ε : ℝ) : ℂ) * K)
          (𝓝[>] (0 : ℝ))
          (𝓝 w))
      hzero_exponent
      hraw_exponent
  have hraw_factor :
      Filter.Tendsto
        (fun ε : ℝ => Complex.exp (-((ε : ℝ) : ℂ) * K))
        (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.exp (0 : ℂ))) :=
    (Complex.continuous_exp.tendsto (0 : ℂ)).comp hexponent
  have hone_factor : Complex.exp (0 : ℂ) = 1 :=
    Complex.exp_zero
  have hfactor :
      Filter.Tendsto
        (fun ε : ℝ => Complex.exp (-((ε : ℝ) : ℂ) * K))
        (𝓝[>] (0 : ℝ))
        (𝓝 (1 : ℂ)) :=
    Eq.subst
      (motive := fun w : ℂ =>
        Filter.Tendsto
          (fun ε : ℝ => Complex.exp (-((ε : ℝ) : ℂ) * K))
          (𝓝[>] (0 : ℝ))
          (𝓝 w))
      hone_factor
      hraw_factor
  have hraw_product :
      Filter.Tendsto
        (fun ε : ℝ =>
          f z * Complex.exp (-((ε : ℝ) : ℂ) * K))
        (𝓝[>] (0 : ℝ))
        (𝓝 (f z * (1 : ℂ))) :=
    tendsto_const_nhds.mul hfactor
  have hproduct_one : f z * (1 : ℂ) = f z :=
    mul_one (f z)
  have hproduct :
      Filter.Tendsto
        (fun ε : ℝ =>
          f z * Complex.exp (-((ε : ℝ) : ℂ) * K))
        (𝓝[>] (0 : ℝ))
        (𝓝 (f z)) :=
    Eq.subst
      (motive := fun w : ℂ =>
        Filter.Tendsto
          (fun ε : ℝ =>
            f z * Complex.exp (-((ε : ℝ) : ℂ) * K))
          (𝓝[>] (0 : ℝ))
          (𝓝 w))
      hproduct_one
      hraw_product
  exact
    hproduct.congr'
      (Eventually.of_forall
        fun ε : ℝ =>
          (verticalStripSubcriticalCosineDampedFamily_eq f a b d ε z).symm)

/-- Norm form of the zero-damping limit for the subcritical cosine-damped
family. -/
theorem verticalStripSubcriticalCosineDampedFamily_norm_tendsto_zeroDamping
    (f : ℂ → ℂ)
    (a b d : ℝ)
    (z : ℂ) :
    Filter.Tendsto
      (fun ε : ℝ => ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖)
      (𝓝[>] (0 : ℝ))
      (𝓝 ‖f z‖) :=
  (verticalStripSubcriticalCosineDampedFamily_tendsto_zeroDamping
    f a b d z).norm

/-- Pointwise undamping for the subcritical cosine-damped family under a fixed
finite-order envelope. -/
theorem verticalStripSubcriticalCosineDampedFamily_uniform_envelope_undamps
    (f : ℂ → ℂ)
    (a b d A B : ℝ)
    (m : ℕ)
    (z : ℂ)
    (huniform :
      ∀ ε : ℝ,
        0 < ε →
        ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    real_norm_bound_of_tendsto_from_positive_side
      (verticalStripSubcriticalCosineDampedFamily_norm_tendsto_zeroDamping
        f a b d z)
      huniform

/-- A uniform finite-order envelope for all positive subcritical cosine dampings
descends to the original function as the damping parameter tends to zero. -/
theorem strip_finite_order_growth_of_uniform_subcritical_cosine_damped_family_bounds
    (f : ℂ → ℂ)
    (a b d : ℝ)
    (hdamped :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ ε : ℝ,
          0 < ε →
          ∀ z : ℂ,
            a ≤ z.re →
            z.re ≤ b →
            1 ≤ z.im →
            ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤
              A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        1 ≤ z.im →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match hdamped with
  | ⟨A, B, m, hA, hB, huniform⟩ =>
      exact
        ⟨A, B, m, hA, hB,
          fun z hza hzb hzim =>
            verticalStripSubcriticalCosineDampedFamily_uniform_envelope_undamps
              f a b d A B m z
              (fun ε hε => huniform ε hε z hza hzb hzim)⟩

/-- A uniform finite-order envelope for all positive cosine dampings descends to
the original function as the damping parameter tends to zero.

The constants must be chosen before the damping parameter.  A family of
existential constants depending on `ε` is not enough to undamp on the whole
closed strip, because the inverse cosine damping has super-polynomial
vertical growth in the strip interior. -/
theorem strip_finite_order_growth_of_uniform_cosine_damped_family_bounds
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hab : a < b)
    (hdamped :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ ε : ℝ,
          0 < ε →
          ∀ z : ℂ,
            a ≤ z.re →
            z.re ≤ b →
            1 ≤ ‖z.im‖ →
            ‖verticalStripCosineDampedFamily f a b ε z‖ ≤
              A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match hdamped with
  | ⟨A, B, m, hA, hB, huniform⟩ =>
      exact
        ⟨A, B, m, hA, hB,
          fun z hza hzb hzim =>
            verticalStripCosineDampedFamily_uniform_envelope_undamps
              f a b A B m z
              (fun ε hε => huniform ε hε z hza hzb hzim)⟩

/-- Pointwise zero-damping limit for the upper-tail tilted damped family. -/
theorem verticalStripUpperTailDampedFamily_tendsto_zeroDamping
    (f : ℂ → ℂ)
    (a b : ℝ)
    (z : ℂ) :
    Filter.Tendsto
      (fun ε : ℝ => verticalStripUpperTailDampedFamily f a b ε z)
      (𝓝[>] (0 : ℝ))
      (𝓝 (f z)) := by
  let K : ℂ := verticalStripUpperTailDampingKernel a b z
  have hε_complex :
      Filter.Tendsto
        (fun ε : ℝ => ((ε : ℝ) : ℂ))
        (𝓝[>] (0 : ℝ))
        (𝓝 (0 : ℂ)) :=
    Filter.Tendsto.mono_left
      Complex.continuous_ofReal.continuousAt
      nhdsWithin_le_nhds
  have hraw_exponent :
      Filter.Tendsto
        (fun ε : ℝ => -((ε : ℝ) : ℂ) * K)
        (𝓝[>] (0 : ℝ))
        (𝓝 (-(0 : ℂ) * K)) :=
    hε_complex.neg.mul tendsto_const_nhds
  have hzero_exponent : -(0 : ℂ) * K = 0 := by
    calc
      -(0 : ℂ) * K = (0 : ℂ) * K := by
        exact congrArg (fun w : ℂ => w * K) (neg_zero : -(0 : ℂ) = 0)
      _ = 0 := zero_mul K
  have hexponent :
      Filter.Tendsto
        (fun ε : ℝ => -((ε : ℝ) : ℂ) * K)
        (𝓝[>] (0 : ℝ))
        (𝓝 (0 : ℂ)) :=
    Eq.subst
      (motive := fun w : ℂ =>
        Filter.Tendsto
          (fun ε : ℝ => -((ε : ℝ) : ℂ) * K)
          (𝓝[>] (0 : ℝ))
          (𝓝 w))
      hzero_exponent
      hraw_exponent
  have hraw_factor :
      Filter.Tendsto
        (fun ε : ℝ => Complex.exp (-((ε : ℝ) : ℂ) * K))
        (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.exp (0 : ℂ))) :=
    (Complex.continuous_exp.tendsto (0 : ℂ)).comp hexponent
  have hone_factor : Complex.exp (0 : ℂ) = 1 :=
    Complex.exp_zero
  have hfactor :
      Filter.Tendsto
        (fun ε : ℝ => Complex.exp (-((ε : ℝ) : ℂ) * K))
        (𝓝[>] (0 : ℝ))
        (𝓝 (1 : ℂ)) :=
    Eq.subst
      (motive := fun w : ℂ =>
        Filter.Tendsto
          (fun ε : ℝ => Complex.exp (-((ε : ℝ) : ℂ) * K))
          (𝓝[>] (0 : ℝ))
          (𝓝 w))
      hone_factor
      hraw_factor
  have hraw_product :
      Filter.Tendsto
        (fun ε : ℝ =>
          f z * Complex.exp (-((ε : ℝ) : ℂ) * K))
        (𝓝[>] (0 : ℝ))
        (𝓝 (f z * (1 : ℂ))) :=
    tendsto_const_nhds.mul hfactor
  have hproduct_one : f z * (1 : ℂ) = f z :=
    mul_one (f z)
  have hproduct :
      Filter.Tendsto
        (fun ε : ℝ =>
          f z * Complex.exp (-((ε : ℝ) : ℂ) * K))
        (𝓝[>] (0 : ℝ))
        (𝓝 (f z)) :=


    Eq.subst
      (motive := fun w : ℂ =>
        Filter.Tendsto
          (fun ε : ℝ =>
            f z * Complex.exp (-((ε : ℝ) : ℂ) * K))
          (𝓝[>] (0 : ℝ))
          (𝓝 w))
      hproduct_one
      hraw_product
  exact
    hproduct.congr'
      (Eventually.of_forall
        fun ε : ℝ =>
          (verticalStripUpperTailDampedFamily_eq f a b ε z).symm)

/-- Norm form of the zero-damping limit for the upper-tail tilted damped
family. -/
theorem verticalStripUpperTailDampedFamily_norm_tendsto_zeroDamping
    (f : ℂ → ℂ)
    (a b : ℝ)
    (z : ℂ) :
    Filter.Tendsto
      (fun ε : ℝ => ‖verticalStripUpperTailDampedFamily f a b ε z‖)
      (𝓝[>] (0 : ℝ))
      (𝓝 ‖f z‖) :=
  (verticalStripUpperTailDampedFamily_tendsto_zeroDamping f a b z).norm

/-- Pointwise undamping for the upper-tail tilted family under a fixed
finite-order envelope. -/
theorem verticalStripUpperTailDampedFamily_uniform_envelope_undamps
    (f : ℂ → ℂ)
    (a b A B : ℝ)
    (m : ℕ)
    (z : ℂ)
    (huniform :
      ∀ ε : ℝ,
        0 < ε →
        ‖verticalStripUpperTailDampedFamily f a b ε z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    real_norm_bound_of_tendsto_from_positive_side
      (verticalStripUpperTailDampedFamily_norm_tendsto_zeroDamping f a b z)
      huniform

/-- A uniform finite-order envelope for all positive upper-tail tilted dampings
descends to the original function as the damping parameter tends to zero. -/
theorem strip_finite_order_growth_of_uniform_upperTail_damped_family_bounds
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hdamped :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ ε : ℝ,
          0 < ε →
          ∀ z : ℂ,
            a ≤ z.re →
            z.re ≤ b →
            1 ≤ z.im →
            ‖verticalStripUpperTailDampedFamily f a b ε z‖ ≤
              A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        1 ≤ z.im →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match hdamped with
  | ⟨A, B, m, hA, hB, huniform⟩ =>
      exact
        ⟨A, B, m, hA, hB,
          fun z hza hzb hzim =>
            verticalStripUpperTailDampedFamily_uniform_envelope_undamps
              f a b A B m z
              (fun ε hε => huniform ε hε z hza hzb hzim)⟩


end
end LFunctions
end Boundary
