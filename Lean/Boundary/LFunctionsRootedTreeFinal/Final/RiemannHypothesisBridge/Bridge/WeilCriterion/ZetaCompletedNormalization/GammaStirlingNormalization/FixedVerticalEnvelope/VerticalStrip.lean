import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.FixedVerticalEnvelope.RecurrenceTransport

/-!
# Fixed vertical strip Gamma bounds

This subowner assembles the vertical-strip Gamma/Stirling estimates from recurrence transport.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

theorem Complex.sectorialLogGammaAsymptotic_verticalStrip_largeHeight_bounds_of_recurrenceProduct
    (hStirling : ∃ R : ℝ, ∃ K : ℝ,
      0 < R ∧
      0 < K ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R ≤ ‖w‖ →
        ‖Complex.Gamma w * Complex.exp w *
            w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
          K / ‖w‖)
    (A B : ℝ) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint x y)‖ ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope x y ∧
          c * Complex.fixedRealPartVerticalStirlingEnvelope x y ≤
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint x y)‖ := by
  let N : ℕ := Complex.verticalStripTransportShift A
  have hshifted_transport :
      ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
        0 < H ∧
        0 < C ∧
        0 < c ∧
        ∀ x y : ℝ,
          A ≤ x →
          x ≤ B →
          H ≤ ‖y‖ →
            ‖Complex.Gamma
                (Complex.fixedRealPartVerticalPoint (x + N) y)‖ ≤
              C * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y ∧
            c * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y ≤
              ‖Complex.Gamma
                (Complex.fixedRealPartVerticalPoint (x + N) y)‖ := by
    exact
      Complex.sectorialStirling_shiftedRawGammaEnvelope_of_normalizedStirling
        hStirling A B
  exact
    Complex.verticalStripGammaBounds_of_shiftedRawBounds_and_recurrenceProduct
      A B N rfl
      hshifted_transport
      (Complex.gammaRecurrenceProduct_verticalStrip_twoSided_bounds A B N)
      (Complex.gammaRecurrenceProduct_factors_ne_zero_on_verticalStrip_largeHeight
        A B N)

/-- Deterministic finite-recurrence transport from closed-right-half-plane
sectorial Stirling to a vertical strip.

The shift is `Complex.verticalStripRightShift A`.  Applying sectorial Stirling
to `z + N` is justified by
`fixedRealPartVerticalPoint_verticalStripRightShift_closedRightHalfPlaneSector`
and the height/radius comparison.  The finite product
`gammaRecurrenceProduct z N` is controlled uniformly on the strip because `N`
is fixed and the strip real part is bounded; Gamma recurrence gives
`Γ z = Γ (z + N) / gammaRecurrenceProduct z N`. -/
theorem Complex.sectorialLogGammaAsymptotic_verticalStrip_largeHeight_bounds_of_deterministicShift
    (hStirling : ∃ R : ℝ, ∃ K : ℝ,
      0 < R ∧
      0 < K ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R ≤ ‖w‖ →
        ‖Complex.Gamma w * Complex.exp w *
            w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
          K / ‖w‖)
    (A B : ℝ) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint x y)‖ ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope x y ∧
          c * Complex.fixedRealPartVerticalStirlingEnvelope x y ≤
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint x y)‖ := by
  exact
    Complex.sectorialLogGammaAsymptotic_verticalStrip_largeHeight_bounds_of_recurrenceProduct
      hStirling A B

/-- Vertical-strip two-sided Stirling bounds as a consequence of sectorial
log-Gamma Stirling.

For a strip that crosses the left half-plane, choose a natural shift `N` with
`-A ≤ N`.  The shifted points `z + N` lie in the closed right half-plane and
the sectorial logarithmic Stirling theorem applies there; the finite Gamma
recurrence product transports the estimate back to `z`.  The coordinate and
radius facts above supply the non-Stirling geometry of this reduction. -/
theorem Complex.sectorialLogGammaAsymptotic_verticalStrip_largeHeight_bounds
    (hStirling : ∃ R : ℝ, ∃ K : ℝ,
      0 < R ∧
      0 < K ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R ≤ ‖w‖ →
        ‖Complex.Gamma w * Complex.exp w *
            w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
          K / ‖w‖)
    (A B : ℝ) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint x y)‖ ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope x y ∧
          c * Complex.fixedRealPartVerticalStirlingEnvelope x y ≤
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint x y)‖ := by
  exact
    Complex.sectorialLogGammaAsymptotic_verticalStrip_largeHeight_bounds_of_deterministicShift
      hStirling A B

/-- Standard vertical-strip specialization of sectorial Stirling.

On every compact real strip `A ≤ Re z ≤ B`, the vertical tails lie in closed
sectors avoiding the negative real axis.  Sectorial Stirling therefore gives
uniform two-sided Gamma bounds with the classical
`exp (-π |y| / 2) (1 + |y|)^(x - 1/2)` profile.  This is the upstream
fixed-line owner theorem; cf. Whittaker-Watson, Ch. XII and DLMF §5.11. -/
theorem Complex.sectorialStirling_verticalStrip_largeHeight_classical
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (A B : ℝ) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint x y)‖ ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope x y ∧
          c * Complex.fixedRealPartVerticalStirlingEnvelope x y ≤
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint x y)‖ := by
  let N : ℕ := Complex.verticalStripTransportShift A
  have hshifted_transport :
      ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
        0 < H ∧
        0 < C ∧
        0 < c ∧
        ∀ x y : ℝ,
          A ≤ x →
          x ≤ B →
          H ≤ ‖y‖ →
            ‖Complex.Gamma
                (Complex.fixedRealPartVerticalPoint (x + N) y)‖ ≤
              C * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y ∧
            c * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y ≤
              ‖Complex.Gamma
                (Complex.fixedRealPartVerticalPoint (x + N) y)‖ := by
    exact
      Complex.sectorialStirling_shiftedRawGammaEnvelope_of_branchPackage
        hbranch A B
  exact
    Complex.verticalStripGammaBounds_of_shiftedRawBounds_and_recurrenceProduct
      A B N rfl
      hshifted_transport
      (Complex.gammaRecurrenceProduct_verticalStrip_twoSided_bounds A B N)
      (Complex.gammaRecurrenceProduct_factors_ne_zero_on_verticalStrip_largeHeight
        A B N)

/-- Classical large-height fixed-real-part vertical Stirling theorem.

For arbitrary real part `a`, the vertical line `a + i b` is not contained in
the closed right half-plane when `a < 0`.  The correct owner input is therefore
the fixed-line specialization of sectorial Stirling in sectors avoiding the
negative real axis, with constants depending on `a`; cf. DLMF §5.11. -/
theorem Complex.fixedRealPartVerticalStirling_largeHeight_classical
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (a : ℝ) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ b : ℝ,
        H ≤ ‖b‖ →
          ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope a b ∧
          c * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ := by
  match Complex.sectorialStirling_verticalStrip_largeHeight_classical hbranch a a with
  | ⟨H, C, c, hH_pos, hC_pos, hc_pos, hstrip⟩ =>
  exact
    ⟨H, C, c, hH_pos, hC_pos, hc_pos,
      fun b hb =>
        hstrip a b (le_refl a) (le_refl a) hb⟩

/-- Large-height fixed-real-part vertical Stirling bounds for `Complex.Gamma`.

For an arbitrary fixed real part `a`, the vertical line `a + ib` eventually
lies in a closed sector avoiding the negative real axis, with sector aperture
depending on `a`.  Sectorial Stirling there gives the two-sided
`exp (-π |b| / 2) (1 + |b|)^(a - 1/2)` envelope. -/
theorem Complex.Gamma_fixedRealPart_vertical_twoSided_norm_stirling_bounds_largeHeight_classical
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (a : ℝ) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ b : ℝ,
        H ≤ ‖b‖ →
          ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope a b ∧
          c * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ := by
  exact Complex.fixedRealPartVerticalStirling_largeHeight_classical hbranch a

/-- The compact-height part of a fixed vertical line. -/

end
end LFunctions
end Boundary
