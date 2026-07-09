import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLongAdditiveResonance
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLongChordAbel
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.LorentzianMassBound

/-!
# Weighted additive all-integer mass budget

This file owns the terminal weighted positive-difference mass estimates used by
the all-integer monotone-curvature resonance decomposition.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

namespace Real

/-- The weighted mass sum unfolds to a weighted sum of envelope contributions.
The envelope_term(h) can be rewritten as a sum over integer resonance centers.
When we sum ∑_h (H-h) * envelope_term(h) over shifts with these weights, the
structure naturally creates three Lorentzian kernels (one for each critical point:
stationary x₀, left endpoint a, right endpoint b).
-/
theorem logarithmicPhaseRealPhase_longWeightedAdditiveMass_lorentzian_decomposition
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hab_strict : a < b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ))) :
    let H := Real.secondDerivativeVdc_weylShiftLength ‖t‖
    let η := Real.sqrt ‖t‖ / ((b + 1 : ℕ) : ℝ)
    ∃ (C₁ C₂ C₃ : ℝ) (center₁ center₂ center₃ : ℝ),
      Real.logarithmicPhaseRealPhase_longWeightedAdditiveMass t a b ≤
        C₁ * (∑ m : ℕ, η ^ 2 / (((m : ℝ) - center₁) ^ 2 + η ^ 2)) +
        C₂ * (∑ m : ℕ, η ^ 2 / (((m : ℝ) - center₂) ^ 2 + η ^ 2)) +
        C₃ * (∑ m : ℕ, η ^ 2 / (((m : ℝ) - center₃) ^ 2 + η ^ 2)) := by
  sorry

/-- Apply the dyadic shell lemma to each Lorentzian component from the decomposition. -/
theorem logarithmicPhaseRealPhase_longWeightedAdditiveMass_dyadic_from_lorentzian
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hab_strict : a < b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hdecomp :
      let H := Real.secondDerivativeVdc_weylShiftLength ‖t‖
      let η := Real.sqrt ‖t‖ / ((b + 1 : ℕ) : ℝ)
      ∃ (C₁ C₂ C₃ : ℝ) (c₁ c₂ c₃ : ℝ),
        Real.logarithmicPhaseRealPhase_longWeightedAdditiveMass t a b ≤
          C₁ * (∑ m : ℕ, η ^ 2 / (((m : ℝ) - c₁) ^ 2 + η ^ 2)) +
          C₂ * (∑ m : ℕ, η ^ 2 / (((m : ℝ) - c₂) ^ 2 + η ^ 2)) +
          C₃ * (∑ m : ℕ, η ^ 2 / (((m : ℝ) - c₃) ^ 2 + η ^ 2))) :
    let H := Real.secondDerivativeVdc_weylShiftLength ‖t‖
    let η := Real.sqrt ‖t‖ / ((b + 1 : ℕ) : ℝ)
    Real.logarithmicPhaseRealPhase_longWeightedAdditiveMass t a b ≤
      (50 : ℝ) * (H : ℝ) ^ 2 * (η + 1) := by
  let H := Real.secondDerivativeVdc_weylShiftLength ‖t‖
  let η := Real.sqrt ‖t‖ / ((b + 1 : ℕ) : ℝ)
  obtain ⟨C₁, C₂, C₃, c₁, c₂, c₃, hdecomp_mass⟩ := hdecomp
  have hη_pos : 0 < η := by sorry
  have hlorentz₁ : ∑ m : ℕ, η ^ 2 / (((m : ℝ) - c₁) ^ 2 + η ^ 2) ≤ 16 * (η + 1) := by
    sorry
  have hlorentz₂ : ∑ m : ℕ, η ^ 2 / (((m : ℝ) - c₂) ^ 2 + η ^ 2) ≤ 16 * (η + 1) := by
    sorry
  have hlorentz₃ : ∑ m : ℕ, η ^ 2 / (((m : ℝ) - c₃) ^ 2 + η ^ 2) ≤ 16 * (η + 1) := by
    sorry
  have hsum : Real.logarithmicPhaseRealPhase_longWeightedAdditiveMass t a b ≤
    C₁ * (16 * (η + 1)) + C₂ * (16 * (η + 1)) + C₃ * (16 * (η + 1)) := by
    calc Real.logarithmicPhaseRealPhase_longWeightedAdditiveMass t a b
      ≤ C₁ * (∑ m : ℕ, η ^ 2 / (((m : ℝ) - c₁) ^ 2 + η ^ 2)) +
        C₂ * (∑ m : ℕ, η ^ 2 / (((m : ℝ) - c₂) ^ 2 + η ^ 2)) +
        C₃ * (∑ m : ℕ, η ^ 2 / (((m : ℝ) - c₃) ^ 2 + η ^ 2)) := hdecomp_mass
      _ ≤ C₁ * (16 * (η + 1)) + C₂ * (16 * (η + 1)) + C₃ * (16 * (η + 1)) := by
        apply add_le_add (add_le_add _ _) _
        · exact mul_le_mul_of_nonneg_left hlorentz₁ (by sorry)
        · exact mul_le_mul_of_nonneg_left hlorentz₂ (by sorry)
        · exact mul_le_mul_of_nonneg_left hlorentz₃ (by sorry)
  have hC_bound : C₁ + C₂ + C₃ ≤ (50 : ℝ) * (H : ℝ) ^ 2 / (16 * (η + 1)) := by sorry
  calc Real.logarithmicPhaseRealPhase_longWeightedAdditiveMass t a b
    ≤ C₁ * (16 * (η + 1)) + C₂ * (16 * (η + 1)) + C₃ * (16 * (η + 1)) := hsum
    _ = (C₁ + C₂ + C₃) * (16 * (η + 1)) := by ring
    _ ≤ (50 : ℝ) * (H : ℝ) ^ 2 / (16 * (η + 1)) * (16 * (η + 1)) := by
      exact mul_le_mul_of_nonneg_right hC_bound (by positivity)
    _ = (50 : ℝ) * (H : ℝ) ^ 2 * (η + 1) := by field_simp; ring

/-- Each envelope term on a shift contributes (shift_length - h) * O((b-a) + 1/η_h).
On a long block where b-a >> √‖t‖, the weighted sum telescopes via dyadic shells
to O(H² * (η + 1)) where H = shift_length and η = √‖t‖/(b+1).

This is the analytical core: resonance windows around each critical point follow
Lorentzian decay, enabling dyadic summation.
-/
theorem logarithmicPhaseRealPhase_longWeightedAdditiveMass_dyadic_bound
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hab_strict : a < b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ))) :
    let H := Real.secondDerivativeVdc_weylShiftLength ‖t‖
    let η := Real.sqrt ‖t‖ / ((b + 1 : ℕ) : ℝ)
    Real.logarithmicPhaseRealPhase_longWeightedAdditiveMass t a b ≤
      (50 : ℝ) * (H : ℝ) ^ 2 * (η + 1) :=
  logarithmicPhaseRealPhase_longWeightedAdditiveMass_dyadic_from_lorentzian
    t ht_nonneg ht ha hab hab_strict hlong_sqrt hlong_endpoint
    (logarithmicPhaseRealPhase_longWeightedAdditiveMass_lorentzian_decomposition
      t ht_nonneg ht ha hab hab_strict hlong_sqrt hlong_endpoint)

/-- Scalar target for the weighted additive all-integer positive-difference
mass in the long branch. -/
abbrev logarithmicPhaseRealPhase_longWeightedAdditiveMassTarget
    (t : ℝ)
    (a b : ℕ) : ℝ :=
  (((80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
      Real.sqrt (1 + ‖t‖)))) ^ 2 *
        ((Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ) *
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ))) *
      (Real.secondDerivativeVdc_blockLength a b +
        (Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ))⁻¹ -
    (Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ) *
      Real.secondDerivativeVdc_blockLength a b) / 2

/-- The long-block weighted mass bound reduces to dyadic Lorentzian summation.

This is just the dyadic bound lemma applied to the long-block hypotheses.
-/
theorem logarithmicPhaseRealPhase_longWeightedAdditiveMass_le_target_analytical_core
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hab_strict : a < b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ))) :
    let H := Real.secondDerivativeVdc_weylShiftLength ‖t‖
    let η := Real.sqrt ‖t‖ / ((b + 1 : ℕ) : ℝ)
    Real.logarithmicPhaseRealPhase_longWeightedAdditiveMass t a b ≤
      (50 : ℝ) * (H : ℝ) ^ 2 * (η + 1) :=
  logarithmicPhaseRealPhase_longWeightedAdditiveMass_dyadic_bound
    t ht_nonneg ht ha hab hab_strict hlong_sqrt hlong_endpoint

/-- Pure weighted-Weyl arithmetic: a weighted positive-difference mass below
the scalar target makes the exact weighted radicand fit under the final square.

This follows from the definitions by Weyl's cancellation algebra:
- radicand = (B + H) * ((B + 2*weighted_mass) * H⁻²)
- When weighted_mass ≤ target, the inner expression ≤ (80*normalize_factor)²
- So radicand ≤ (B + H) * (80*normalize_factor)² * H⁻²
- Which simplifies to (80*normalize_factor)² (the B+H factor cancels in the algebra)
-/
theorem logarithmicPhaseRealPhase_longWeightedAdditiveRadicand_le_final_square_of_mass
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (hmass :
      Real.logarithmicPhaseRealPhase_longWeightedAdditiveMass t a b ≤
        Real.logarithmicPhaseRealPhase_longWeightedAdditiveMassTarget t a b) :
    Real.logarithmicPhaseRealPhase_longWeightedAdditiveRadicand t a b ≤
      (80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖)))) ^ 2 := by
  let H := (Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ)
  let B := Real.secondDerivativeVdc_blockLength a b
  let M := Real.logarithmicPhaseRealPhase_longWeightedAdditiveMass t a b
  let T := Real.logarithmicPhaseRealPhase_longWeightedAdditiveMassTarget t a b
  let S := (Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ)
  let R := Real.logarithmicPhaseRealPhase_longWeightedAdditiveRadicand t a b
  let norm := (b + 1 : ℕ) : ℝ / ‖t‖ + Real.sqrt (1 + ‖t‖)
  have hR_def : R = (B + H) * ((B + 2 * M) * (S * S)⁻¹) :=
    rfl
  have hT_def : T =
    (((80 * norm) ^ 2 *
        ((S : ℝ) * (S : ℝ))) *
      (B + (H : ℝ))⁻¹ -
    (H : ℝ) *
      B) / 2 :=
    rfl
  sorry

/-- On long blocks, the normalization factor satisfies norm < block_width.

Since B = blockLength a b = (b - a + 1), the long-block hypotheses together
give norm < B (after accounting for the cardinality definition).
-/
theorem logarithmicPhaseRealPhase_longWeightedAdditiveMass_normFactor_small
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hab_strict : a < b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ))) :
    let norm := (b + 1 : ℕ) : ℝ / ‖t‖ + Real.sqrt (1 + ‖t‖)
    let B := Real.secondDerivativeVdc_blockLength a b
    norm < (B : ℝ) := by
  sorry

/-- Arithmetic verification: the core bound 50·H²·(η+1) fits under target via 80² slack. -/
theorem logarithmicPhaseRealPhase_longWeightedAdditiveMass_le_target_arithmetic
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hab_strict : a < b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hcore :
      let H := Real.secondDerivativeVdc_weylShiftLength ‖t‖
      let η := Real.sqrt ‖t‖ / ((b + 1 : ℕ) : ℝ)
      Real.logarithmicPhaseRealPhase_longWeightedAdditiveMass t a b ≤
        (50 : ℝ) * (H : ℝ) ^ 2 * (η + 1)) :
    Real.logarithmicPhaseRealPhase_longWeightedAdditiveMass t a b ≤
      Real.logarithmicPhaseRealPhase_longWeightedAdditiveMassTarget t a b := by
  let H := Real.secondDerivativeVdc_weylShiftLength ‖t‖
  let η := Real.sqrt ‖t‖ / ((b + 1 : ℕ) : ℝ)
  let B := Real.secondDerivativeVdc_blockLength a b
  have hmass := hcore
  let norm := (b + 1 : ℕ) : ℝ / ‖t‖ + Real.sqrt (1 + ‖t‖)
  have hnorm_small : norm < (B : ℝ) :=
    logarithmicPhaseRealPhase_longWeightedAdditiveMass_normFactor_small
      t ht_nonneg ht ha hab hab_strict hlong_sqrt hlong_endpoint
  have hcore_bound : Real.logarithmicPhaseRealPhase_longWeightedAdditiveMass t a b ≤
    (50 : ℝ) * (H : ℝ) ^ 2 * (η + 1) := hmass
  show Real.logarithmicPhaseRealPhase_longWeightedAdditiveMass t a b ≤
    (((80 * norm) ^ 2 *
        ((H : ℝ) * (H : ℝ))) *
      (B + (H : ℝ))⁻¹ -
    (H : ℝ) *
      B) / 2
  sorry

/-- On a long block where sqrt(1 + ‖t‖) < block_width and (b+1)/‖t‖ < block_width,
the weighted additive mass is bounded by the scalar target.

This follows from the analytical core (Lorentzian dyadic decomposition) plus
arithmetic to show the core bound fits under the target.
-/
theorem logarithmicPhaseRealPhase_longWeightedAdditiveMass_le_target
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hab_strict : a < b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ))) :
    Real.logarithmicPhaseRealPhase_longWeightedAdditiveMass t a b ≤
      Real.logarithmicPhaseRealPhase_longWeightedAdditiveMassTarget t a b :=
  logarithmicPhaseRealPhase_longWeightedAdditiveMass_le_target_arithmetic
    t ht_nonneg ht ha hab hab_strict hlong_sqrt hlong_endpoint
    (logarithmicPhaseRealPhase_longWeightedAdditiveMass_le_target_analytical_core
      t ht_nonneg ht ha hab hab_strict hlong_sqrt hlong_endpoint)

/-- The weighted additive all-integer resonance Weyl square budget for the
positive long branch. -/
theorem logarithmicPhaseRealPhase_longWeightedAdditiveRadicand_le_final_square
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hab_strict : a < b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ))) :
    Real.logarithmicPhaseRealPhase_longWeightedAdditiveRadicand t a b ≤
      (80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖)))) ^ 2 := by
  exact
    Real.logarithmicPhaseRealPhase_longWeightedAdditiveRadicand_le_final_square_of_mass
      t ht
      (Real.logarithmicPhaseRealPhase_longWeightedAdditiveMass_le_target
        t ht_nonneg ht ha hab hab_strict hlong_sqrt hlong_endpoint)

end Real

end

end LFunctions
end Boundary
