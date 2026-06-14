import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.SectorialLogNorm

/-!
# Fixed-vertical-line Gamma bounds

This file owns fixed-real-part vertical upper and reciprocal bounds for Gamma.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Large-vertical polynomial upper bound on a fixed positive real-part line,
obtained from the sectorial Binet/Stirling estimate. -/
theorem Complex.Gamma_fixedRealPart_vertical_upper_bound_large_from_openSector
    (σ : ℝ)
    (hσ : 0 < σ) :
    ∃ T : ℝ, ∃ C : ℝ, ∃ m : ℕ,
      0 < T ∧ 0 < C ∧
      ∀ t : ℝ,
        T ≤ ‖t‖ →
          ‖Complex.Gamma (σ + t * Complex.I)‖ ≤
            C * (1 + ‖t‖) ^ m := by
  sorry

/-- Compact-interval upper bound on a fixed positive real-part vertical line. -/
theorem Complex.Gamma_fixedRealPart_vertical_upper_bound_compact
    (σ : ℝ)
    (hσ : 0 < σ)
    (T : ℝ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ t : ℝ,
        ‖t‖ ≤ T →
          ‖Complex.Gamma (σ + t * Complex.I)‖ ≤ C := by
  sorry

/-- Compact and large-vertical upper estimates assemble to a global polynomial
upper bound on a fixed positive real-part vertical line. -/
theorem Complex.Gamma_fixedRealPart_vertical_upper_bound_assemble
    (σ : ℝ)
    (hσ : 0 < σ) :
    ∃ C : ℝ, ∃ m : ℕ,
      0 < C ∧
      ∀ t : ℝ,
        ‖Complex.Gamma (σ + t * Complex.I)‖ ≤
          C * (1 + ‖t‖) ^ m := by
  rcases
    Complex.Gamma_fixedRealPart_vertical_upper_bound_large_from_openSector
      σ hσ with
    ⟨T, Ctail, m, hT_pos, hCtail_pos, htail⟩
  rcases
    Complex.Gamma_fixedRealPart_vertical_upper_bound_compact
      σ hσ T with
    ⟨Ccompact, hCcompact_pos, hcompact⟩
  refine ⟨max Ctail Ccompact, m, ?_, ?_⟩
  · exact lt_of_lt_of_le hCtail_pos (le_max_left Ctail Ccompact)
  · intro t
    by_cases ht_tail : T ≤ ‖t‖
    · have htail_bound :
          ‖Complex.Gamma (σ + t * Complex.I)‖ ≤
            Ctail * (1 + ‖t‖) ^ m :=
        htail t ht_tail
      have hpow_nonneg : 0 ≤ (1 + ‖t‖) ^ m :=
        pow_nonneg (by positivity) m
      have hC_le : Ctail ≤ max Ctail Ccompact :=
        le_max_left Ctail Ccompact
      exact
        le_trans htail_bound
          (mul_le_mul_of_nonneg_right hC_le hpow_nonneg)
    · have ht_compact : ‖t‖ ≤ T :=
        le_of_not_ge ht_tail
      have hcompact_bound :
          ‖Complex.Gamma (σ + t * Complex.I)‖ ≤ Ccompact :=
        hcompact t ht_compact
      have hC_le : Ccompact ≤ max Ctail Ccompact :=
        le_max_right Ctail Ccompact
      have hbase_one : 1 ≤ 1 + ‖t‖ := by
        linarith [norm_nonneg t]
      have hpow_one : 1 ≤ (1 + ‖t‖) ^ m :=
        one_le_pow₀ hbase_one
      have hmax_nonneg : 0 ≤ max Ctail Ccompact :=
        le_of_lt (lt_of_lt_of_le hCtail_pos (le_max_left Ctail Ccompact))
      exact
        le_trans hcompact_bound
          (le_trans hC_le
            (le_mul_of_one_le_right hmax_nonneg hpow_one))

/-- Fixed-real-part vertical upper bound obtained by combining open-sector
Binet estimates for large `|t|` with compact-interval boundedness. -/
theorem Complex.Gamma_fixedRealPart_vertical_upper_bound_from_openSector_and_compact
    (σ : ℝ)
    (hσ : 0 < σ) :
    ∃ C : ℝ, ∃ m : ℕ,
      0 < C ∧
      ∀ t : ℝ,
        ‖Complex.Gamma (σ + t * Complex.I)‖ ≤
          C * (1 + ‖t‖) ^ m := by
  exact
    Complex.Gamma_fixedRealPart_vertical_upper_bound_assemble σ hσ

/-- Fixed-real-part vertical upper bound for Gamma. -/
theorem Complex.Gamma_fixedRealPart_vertical_upper_bound_classical
    (σ : ℝ)
    (hσ : 0 < σ) :
    ∃ C : ℝ, ∃ m : ℕ,
      0 < C ∧
      ∀ t : ℝ,
        ‖Complex.Gamma (σ + t * Complex.I)‖ ≤
          C * (1 + ‖t‖) ^ m := by
  exact
    Complex.Gamma_fixedRealPart_vertical_upper_bound_from_openSector_and_compact
      σ hσ

/-- Large-vertical reciprocal Gamma bound on a fixed positive real-part line,
with the correct exponential scale. -/
theorem Complex.Gamma_fixedRealPart_vertical_reciprocal_bound_large_from_stirling
    (σ : ℝ)
    (hσ : 0 < σ) :
    ∃ T : ℝ, ∃ C : ℝ, ∃ A : ℝ,
      0 < T ∧ 0 < C ∧ 0 < A ∧
      ∀ t : ℝ,
        T ≤ ‖t‖ →
          ‖(Complex.Gamma (σ + t * Complex.I))⁻¹‖ ≤
            C * Real.exp (A * ‖t‖) := by
  sorry

/-- Compact-interval reciprocal bound on a fixed positive real-part vertical
line, using nonvanishing of Gamma on the open right half-plane. -/
theorem Complex.Gamma_fixedRealPart_vertical_reciprocal_bound_compact
    (σ : ℝ)
    (hσ : 0 < σ)
    (T : ℝ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ t : ℝ,
        ‖t‖ ≤ T →
          ‖(Complex.Gamma (σ + t * Complex.I))⁻¹‖ ≤ C := by
  sorry

/-- Compact and large-vertical reciprocal estimates assemble to the global
fixed-line exponential reciprocal bound. -/
theorem Complex.Gamma_fixedRealPart_vertical_reciprocal_bound_assemble
    (σ : ℝ)
    (hσ : 0 < σ) :
    ∃ C : ℝ, ∃ A : ℝ,
      0 < C ∧ 0 < A ∧
      ∀ t : ℝ,
        ‖(Complex.Gamma (σ + t * Complex.I))⁻¹‖ ≤
          C * Real.exp (A * ‖t‖) := by
  rcases
    Complex.Gamma_fixedRealPart_vertical_reciprocal_bound_large_from_stirling
      σ hσ with
    ⟨T, Ctail, A, hT_pos, hCtail_pos, hA_pos, htail⟩
  rcases
    Complex.Gamma_fixedRealPart_vertical_reciprocal_bound_compact
      σ hσ T with
    ⟨Ccompact, hCcompact_pos, hcompact⟩
  refine ⟨max Ctail Ccompact, A, ?_, hA_pos, ?_⟩
  · exact lt_of_lt_of_le hCtail_pos (le_max_left Ctail Ccompact)
  · intro t
    by_cases ht_tail : T ≤ ‖t‖
    · have htail_bound :
          ‖(Complex.Gamma (σ + t * Complex.I))⁻¹‖ ≤
            Ctail * Real.exp (A * ‖t‖) :=
        htail t ht_tail
      have hexp_nonneg : 0 ≤ Real.exp (A * ‖t‖) :=
        le_of_lt (Real.exp_pos (A * ‖t‖))
      have hC_le : Ctail ≤ max Ctail Ccompact :=
        le_max_left Ctail Ccompact
      exact
        le_trans htail_bound
          (mul_le_mul_of_nonneg_right hC_le hexp_nonneg)
    · have ht_compact : ‖t‖ ≤ T :=
        le_of_not_ge ht_tail
      have hcompact_bound :
          ‖(Complex.Gamma (σ + t * Complex.I))⁻¹‖ ≤ Ccompact :=
        hcompact t ht_compact
      have hC_le : Ccompact ≤ max Ctail Ccompact :=
        le_max_right Ctail Ccompact
      have hA_norm_nonneg : 0 ≤ A * ‖t‖ :=
        mul_nonneg (le_of_lt hA_pos) (norm_nonneg t)
      have hexp_one : 1 ≤ Real.exp (A * ‖t‖) := by
        calc
          1 = Real.exp 0 := by
            exact Real.exp_zero.symm
          _ ≤ Real.exp (A * ‖t‖) :=
            Real.exp_le_exp.mpr hA_norm_nonneg
      have hmax_nonneg : 0 ≤ max Ctail Ccompact :=
        le_of_lt (lt_of_lt_of_le hCtail_pos (le_max_left Ctail Ccompact))
      exact
        le_trans hcompact_bound
          (le_trans hC_le
            (le_mul_of_one_le_right hmax_nonneg hexp_one))

/-- Fixed-real-part reciprocal bound from nonvanishing, compact-interval
control, and the large-vertical Stirling/Binet estimate. -/
theorem Complex.Gamma_fixedRealPart_vertical_reciprocal_bound_from_nonvanishing_and_stirling
    (σ : ℝ)
    (hσ : 0 < σ) :
    ∃ C : ℝ, ∃ A : ℝ,
      0 < C ∧ 0 < A ∧
      ∀ t : ℝ,
        ‖(Complex.Gamma (σ + t * Complex.I))⁻¹‖ ≤
          C * Real.exp (A * ‖t‖) := by
  exact
    Complex.Gamma_fixedRealPart_vertical_reciprocal_bound_assemble σ hσ

/-- Fixed-real-part vertical reciprocal bound for Gamma.

The reciprocal has exponential, not polynomial, vertical growth:
`1 / Γ(σ + it)` grows like `exp (π |t| / 2)` up to powers of `|t|`.
This owner statement records the correct classical growth scale. -/
theorem Complex.Gamma_fixedRealPart_vertical_lower_bound_classical
    (σ : ℝ)
    (hσ : 0 < σ) :
    ∃ C : ℝ, ∃ A : ℝ,
      0 < C ∧ 0 < A ∧
      ∀ t : ℝ,
        ‖(Complex.Gamma (σ + t * Complex.I))⁻¹‖ ≤
          C * Real.exp (A * ‖t‖) := by
  exact
    Complex.Gamma_fixedRealPart_vertical_reciprocal_bound_from_nonvanishing_and_stirling
      σ hσ

end

end LFunctions
end Boundary
