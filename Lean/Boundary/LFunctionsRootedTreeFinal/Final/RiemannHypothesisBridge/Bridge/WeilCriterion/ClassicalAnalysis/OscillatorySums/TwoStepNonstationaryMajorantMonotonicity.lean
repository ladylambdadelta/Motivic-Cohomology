import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedIntegratedMajorant

/-!
# Monotonicity of the canonical two-step majorant

The four-term majorant is increasing in the three amplitude masses and two
phase-curvature parameters, and decreasing in a positive derivative gap.
Every quotient comparison is exposed separately for downstream specialization.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Real.mul_three_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ 3 * x := mul_nonneg (by exact OfNat.zero_le 3) hx

theorem Real.mul_six_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ 6 * x := mul_nonneg (by exact OfNat.zero_le 6) hx

theorem Real.div_le_div_of_numerator_le_pow_two
    {u₁ u₂ g₁ g₂ : ℝ}
    (hu₁ : 0 ≤ u₁) (hu : u₁ ≤ u₂)
    (hg₁ : 0 < g₁) (hg : g₁ ≤ g₂) :
    u₁ / g₂ ^ 2 ≤ u₂ / g₁ ^ 2 := by
  have hgap := Real.div_pow_antitone_two hu₁ hg₁ hg
  have hdenominator : 0 ≤ g₁ ^ 2 := sq_nonneg g₁
  have hnumerator := div_le_div_of_nonneg_right hu hdenominator
  exact le_trans hgap hnumerator

theorem Real.div_le_div_of_numerator_le_pow_three
    {u₁ u₂ g₁ g₂ : ℝ}
    (hu₁ : 0 ≤ u₁) (hu : u₁ ≤ u₂)
    (hg₁ : 0 < g₁) (hg : g₁ ≤ g₂) :
    u₁ / g₂ ^ 3 ≤ u₂ / g₁ ^ 3 := by
  have hgap := Real.div_pow_antitone_three hu₁ hg₁ hg
  have hdenominator : 0 ≤ g₁ ^ 3 := pow_nonneg hg₁.le 3
  have hnumerator := div_le_div_of_nonneg_right hu hdenominator
  exact le_trans hgap hnumerator

theorem Real.div_le_div_of_numerator_le_pow_four
    {u₁ u₂ g₁ g₂ : ℝ}
    (hu₁ : 0 ≤ u₁) (hu : u₁ ≤ u₂)
    (hg₁ : 0 < g₁) (hg : g₁ ≤ g₂) :
    u₁ / g₂ ^ 4 ≤ u₂ / g₁ ^ 4 := by
  have hgap := Real.div_pow_antitone_four hu₁ hg₁ hg
  have hdenominator : 0 ≤ g₁ ^ 4 := pow_nonneg hg₁.le 4
  have hnumerator := div_le_div_of_nonneg_right hu hdenominator
  exact le_trans hgap hnumerator

theorem Real.three_mul_mul_mono
    {x₁ x₂ y₁ y₂ : ℝ}
    (hx₁ : 0 ≤ x₁) (hy₁ : 0 ≤ y₁)
    (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂) :
    3 * x₁ * y₁ ≤ 3 * x₂ * y₂ := by
  have hthreeX₁ : 0 ≤ 3 * x₁ := Real.mul_three_nonneg hx₁
  have hthreeX := mul_le_mul_of_nonneg_left hx (by exact OfNat.zero_le 3)
  exact mul_le_mul hthreeX hy hy₁ hthreeX₁

theorem Real.mul_mul_mono
    {x₁ x₂ y₁ y₂ : ℝ}
    (hx₁ : 0 ≤ x₁) (hy₁ : 0 ≤ y₁)
    (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂) :
    x₁ * y₁ ≤ x₂ * y₂ := by
  exact mul_le_mul hx hy hy₁ hx₁

theorem Real.three_mul_mul_sq_mono
    {x₁ x₂ y₁ y₂ : ℝ}
    (hx₁ : 0 ≤ x₁) (hy₁ : 0 ≤ y₁)
    (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂) :
    3 * x₁ * y₁ ^ 2 ≤ 3 * x₂ * y₂ ^ 2 := by
  have hySquare : y₁ ^ 2 ≤ y₂ ^ 2 :=
    mul_self_le_mul_self hy₁ hy
  have hySquareNonneg : 0 ≤ y₁ ^ 2 := sq_nonneg y₁
  exact Real.three_mul_mul_mono hx₁ hySquareNonneg hx hySquare

theorem Complex.nonstationarySecondTransformMajorant_mono
    {A₀ A₀' A₀'' v₀ w₀ g₀ : ℝ}
    {A₁ A₁' A₁'' v₁ w₁ g₁ : ℝ}
    (hA₀ : 0 ≤ A₀) (hA₀' : 0 ≤ A₀') (hA₀'' : 0 ≤ A₀'')
    (hv₀ : 0 ≤ v₀) (hw₀ : 0 ≤ w₀)
    (hg₀ : 0 < g₀)
    (hA : A₀ ≤ A₁) (hA' : A₀' ≤ A₁')
    (hA'' : A₀'' ≤ A₁'')
    (hv : v₀ ≤ v₁) (hw : w₀ ≤ w₁)
    (hg : g₀ ≤ g₁) :
    Complex.nonstationarySecondTransformMajorant
        A₀ A₀' A₀'' v₀ w₀ g₁ ≤
      Complex.nonstationarySecondTransformMajorant
        A₁ A₁' A₁'' v₁ w₁ g₀ := by
  unfold Complex.nonstationarySecondTransformMajorant
  have hfirst := Real.div_le_div_of_numerator_le_pow_two
    hA₀'' hA'' hg₀ hg
  have hsecondNumerator :=
    Real.three_mul_mul_mono hA₀' hv₀ hA' hv
  have hsecondNumeratorNonneg : 0 ≤ 3 * A₀' * v₀ :=
    mul_nonneg (Real.mul_three_nonneg hA₀') hv₀
  have hsecond := Real.div_le_div_of_numerator_le_pow_three
    hsecondNumeratorNonneg hsecondNumerator hg₀ hg
  have hthirdNumerator := Real.mul_mul_mono hA₀ hw₀ hA hw
  have hthirdNumeratorNonneg : 0 ≤ A₀ * w₀ :=
    mul_nonneg hA₀ hw₀
  have hthird := Real.div_le_div_of_numerator_le_pow_three
    hthirdNumeratorNonneg hthirdNumerator hg₀ hg
  have hfourthNumerator :=
    Real.three_mul_mul_sq_mono hA₀ hv₀ hA hv
  have hfourthNumeratorNonneg : 0 ≤ 3 * A₀ * v₀ ^ 2 :=
    mul_nonneg (Real.mul_three_nonneg hA₀) (sq_nonneg v₀)
  have hfourth := Real.div_le_div_of_numerator_le_pow_four
    hfourthNumeratorNonneg hfourthNumerator hg₀ hg
  exact add_le_add (add_le_add (add_le_add hfirst hsecond) hthird) hfourth

theorem Complex.nonstationarySecondTransformMajorant_gap_lower
    {A A' A'' v w g G : ℝ}
    (hA : 0 ≤ A) (hA' : 0 ≤ A') (hA'' : 0 ≤ A'')
    (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hG : 0 < G) (hgap : G ≤ g) :
    Complex.nonstationarySecondTransformMajorant A A' A'' v w g ≤
      Complex.nonstationarySecondTransformMajorant A A' A'' v w G := by
  exact Complex.nonstationarySecondTransformMajorant_mono
    hA hA' hA'' hv hw hG
    (le_refl A) (le_refl A') (le_refl A'')
    (le_refl v) (le_refl w) hgap

end
end LFunctions
end Boundary
