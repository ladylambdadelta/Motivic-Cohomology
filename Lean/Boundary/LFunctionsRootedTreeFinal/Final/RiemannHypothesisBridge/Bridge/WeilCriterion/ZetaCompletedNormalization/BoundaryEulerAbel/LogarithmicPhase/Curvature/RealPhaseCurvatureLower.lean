import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseCore

/-!
# Real-phase logarithmic curvature lower bound

This file owns the concrete lower bound for the second derivative of the real
logarithmic phase on a positive integer block.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Concrete second-derivative curvature lower bound for the real scalar
logarithmic phase on an integer block. -/
theorem Complex.logarithmicPhaseRealPhase_secondDerivative_curvature_lower
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    ∀ x : ℝ,
      x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        ‖t‖ *
            (((((b + 1 : ℕ) : ℝ) *
              ((b + 1 : ℕ) : ℝ)))⁻¹) ≤
          ‖deriv
            (deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t))
            x‖ := by
  intro x hx
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  let B : ℝ := ((b + 1 : ℕ) : ℝ)
  have ha_pos_nat : 0 < a :=
    Nat.lt_of_succ_le ha
  have ha_pos : (0 : ℝ) < (a : ℝ) :=
    Nat.cast_pos.mpr ha_pos_nat
  have hx_pos : (0 : ℝ) < x :=
    lt_of_lt_of_le ha_pos hx.1
  have hx_nonneg : 0 ≤ x :=
    le_of_lt hx_pos
  have hB_pos : (0 : ℝ) < B :=
    Nat.cast_pos.mpr (Nat.succ_pos b)
  have hB_nonneg : 0 ≤ B :=
    le_of_lt hB_pos
  have hBB_pos : 0 < B * B :=
    mul_pos hB_pos hB_pos
  have hx_le_B : x ≤ B :=
    hx.2
  have hxx_pos : 0 < x * x :=
    mul_pos hx_pos hx_pos
  have hxx_nonneg : 0 ≤ x * x :=
    le_of_lt hxx_pos
  have hxx_le_BB : x * x ≤ B * B :=
    mul_le_mul hx_le_B hx_le_B hx_nonneg hB_nonneg
  have hden_inv :
      (B * B)⁻¹ ≤ (x * x)⁻¹ :=
    (inv_le_inv₀ hBB_pos hxx_pos).mpr hxx_le_BB
  have hscale :
      ‖t‖ * (B * B)⁻¹ ≤ ‖t‖ * (x * x)⁻¹ :=
    mul_le_mul_of_nonneg_left hden_inv (norm_nonneg t)
  have hderiv_eq :
      deriv (deriv φ) x = t * (x * x)⁻¹ :=
    Complex.logarithmicPhaseRealPhase_secondDerivative_eq t hx_pos
  have hnorm_second :
      ‖deriv (deriv φ) x‖ = ‖t‖ * (x * x)⁻¹ := by
    calc
      ‖deriv (deriv φ) x‖ =
          ‖t * (x * x)⁻¹‖ := by
        exact congrArg norm hderiv_eq
      _ = ‖t‖ * ‖(x * x)⁻¹‖ :=
        norm_mul t ((x * x)⁻¹)
      _ = ‖t‖ * ‖x * x‖⁻¹ := by
        exact congrArg (fun r : ℝ => ‖t‖ * r) (norm_inv (x * x))
      _ = ‖t‖ * (x * x)⁻¹ := by
        exact congrArg (fun r : ℝ => ‖t‖ * r⁻¹)
          (Real.norm_of_nonneg hxx_nonneg)
  exact
    Eq.subst
      (motive := fun r : ℝ =>
        ‖t‖ * (B * B)⁻¹ ≤ r)
      hnorm_second.symm
      hscale

/-- Concrete second-derivative curvature upper bound for the real scalar
logarithmic phase on an integer block.  Together with the preceding lower
bound, this is the two-sided curvature datum used on dyadic blocks. -/
theorem Complex.logarithmicPhaseRealPhase_secondDerivative_curvature_upper
    (t : ℝ)
    {a b : ℕ}
    (ha : 1 ≤ a) :
    ∀ x : ℝ,
      x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        ‖deriv
            (deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t))
            x‖ ≤
          ‖t‖ * ((((a : ℝ) * (a : ℝ)))⁻¹) := by
  intro x hx
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  let A : ℝ := (a : ℝ)
  have hA_pos : 0 < A :=
    Nat.cast_pos.mpr (Nat.lt_of_succ_le ha)
  have hA_nonneg : 0 ≤ A :=
    le_of_lt hA_pos
  have hx_pos : 0 < x :=
    lt_of_lt_of_le hA_pos hx.1
  have hx_nonneg : 0 ≤ x :=
    le_of_lt hx_pos
  have hAA_pos : 0 < A * A :=
    mul_pos hA_pos hA_pos
  have hxx_pos : 0 < x * x :=
    mul_pos hx_pos hx_pos
  have hAA_le_hxx : A * A ≤ x * x :=
    mul_le_mul hx.1 hx.1 hA_nonneg hx_nonneg
  have hinverse :
      (x * x)⁻¹ ≤ (A * A)⁻¹ :=
    (inv_le_inv₀ hxx_pos hAA_pos).mpr hAA_le_hxx
  have hscale :
      ‖t‖ * (x * x)⁻¹ ≤ ‖t‖ * (A * A)⁻¹ :=
    mul_le_mul_of_nonneg_left hinverse (norm_nonneg t)
  have hderiv_eq :
      deriv (deriv φ) x = t * (x * x)⁻¹ :=
    Complex.logarithmicPhaseRealPhase_secondDerivative_eq t hx_pos
  have hnorm_second :
      ‖deriv (deriv φ) x‖ = ‖t‖ * (x * x)⁻¹ := by
    have hxx_nonneg : 0 ≤ x * x :=
      le_of_lt hxx_pos
    calc
      ‖deriv (deriv φ) x‖ =
          ‖t * (x * x)⁻¹‖ := by
        exact congrArg norm hderiv_eq
      _ = ‖t‖ * ‖(x * x)⁻¹‖ :=
        norm_mul t ((x * x)⁻¹)
      _ = ‖t‖ * ‖x * x‖⁻¹ := by
        exact congrArg (fun r : ℝ => ‖t‖ * r) (norm_inv (x * x))
      _ = ‖t‖ * (x * x)⁻¹ := by
        exact congrArg (fun r : ℝ => ‖t‖ * r⁻¹)
          (Real.norm_of_nonneg hxx_nonneg)
  exact
    Eq.subst
      (motive := fun left : ℝ =>
        left ≤ ‖t‖ * (A * A)⁻¹)
      hnorm_second.symm
      hscale

/-- Concrete first-derivative growth on a positive logarithmic real-phase
block, obtained from the owner curvature lower bound. -/
theorem Complex.logarithmicPhaseRealPhase_deriv_growth_on_integer_block
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    ∀ x y : ℝ,
      x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
          x ≤ y →
            (‖t‖ *
                ((((b + 1 : ℕ) : ℝ) *
                  (((b + 1 : ℕ) : ℝ)))⁻¹) *
                (y - x) ≤
              deriv
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y -
              deriv
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x) := by
  intro x y hx hy hxy
  exact
    Complex.logarithmicPhaseRealPhase_deriv_growth_of_nonneg_curvature_integer_block
      t ht_nonneg ha
      (Complex.logarithmicPhaseRealPhase_secondDerivative_curvature_lower
        t ht ha hab)
      hx hy hxy

end

end LFunctions
end Boundary
