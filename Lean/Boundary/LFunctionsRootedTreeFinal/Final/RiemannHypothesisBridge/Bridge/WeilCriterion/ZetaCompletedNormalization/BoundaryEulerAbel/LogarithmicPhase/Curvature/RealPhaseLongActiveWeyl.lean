import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLongWeylTarget
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseResonanceActiveCover

/-!
# Active-resonance long Weyl estimates

This file owns the active all-integer resonance decomposition estimates used by
the long Weyl target.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- A disjoint half-open gap cover whose every gap is assigned an integer
lattice shift gives the standard finite-gap complement estimate.  This is the
summation step for the monotone-curvature resonance decomposition after each
gap has been placed in its own principal branch. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_sum_norm_le_gapCount_mul_curvatureMajorant_of_integerLatticeShift_gaps
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b h : ℕ}
    {lam : ℝ}
    (gaps : Finset (ℕ × ℕ))
    (center : ℕ × ℕ → ℤ)
    (ha : 1 ≤ a)
    (hpos : 1 ≤ h)
    (hlam :
      lam =
        ‖t‖ *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          (h : ℝ))
    (hcover :
      Complex.realPhase_IcoFamilyUnion gaps =
        Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
          t a b h lam)
    (hdisjoint :
      ∀ p₁ ∈ gaps,
        ∀ p₂ ∈ gaps,
          p₁ ≠ p₂ →
            Disjoint (Finset.Ico p₁.1 p₁.2) (Finset.Ico p₂.1 p₂.2))
    (hgap_bounds :
      ∀ p : ℕ × ℕ,
        p ∈ gaps →
          a ≤ p.1 ∧ p.2 ≤ b - h)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h))
    (havoid :
      ∀ p : ℕ × ℕ,
        p ∈ gaps →
          ∀ n : ℕ,
            n ∈ Finset.Ico p.1 p.2 →
              n ∉ Complex.realPhase_integerIncrementResonanceWindow
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                a (b - h) (2 * Real.pi * (center p : ℝ)) lam)
    (hprincipal :
      ∀ p : ℕ × ℕ,
        p ∈ gaps →
          ∀ n : ℕ,
            n ∈ Finset.Ico p.1 p.2 →
              Complex.realPhase_integerIncrement
                  (Complex.realPhase_integerLatticeShift
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    (center p))
                  n ∈
                Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi))) :
    ‖∑ n ∈
      Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
        t a b h lam,
      Complex.exp
        (Complex.I *
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h n : ℂ))‖ ≤
      ((gaps.card : ℝ) *
        Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) := by
  let ψ : ℝ → ℝ :=
    Complex.realPhase_secondDerivative_vdc_shiftedDifference
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      h
  let F : ℕ → ℂ :=
    fun n : ℕ => Complex.exp (Complex.I * (ψ n : ℂ))
  have hgap :
      ∀ p : ℕ × ℕ,
        p ∈ gaps →
          ‖∑ n ∈ Finset.Ico p.1 p.2, F n‖ ≤
            Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h := by
    intro p hp
    have hp_bounds : a ≤ p.1 ∧ p.2 ≤ b - h :=
      hgap_bounds p hp
    have hsub : Finset.Ico p.1 p.2 ⊆ Finset.Ico a (b - h) :=
      Finset.Ico_subset_Ico hp_bounds.1 hp_bounds.2
    exact
      Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_curvatureMajorant_of_integerLatticeShift_gap
        (t := t) (ht := ht) (a := a) (b := b) (c := p.1) (d := p.2)
        (h := h) (lam := lam)
        (center p)
        (le_trans ha hp_bounds.1)
        hpos hlam hinc_mono hsub
        (havoid p hp)
        (hprincipal p hp)
  exact
    Complex.realPhase_sum_norm_le_card_mul_of_IcoFamily_cover
      (Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
        t a b h lam)
      gaps F hcover hdisjoint hgap

/-- A shifted-logarithmic gap assigned to one integer lattice branch has the
Kusmin-Landau bound at the resonance thickness of that branch. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_firstDerivativeMajorant_of_integerLatticeShift_gap
    (t : ℝ)
    {a b c d h : ℕ}
    {eta : ℝ}
    (k : ℤ)
    (hc : 1 ≤ c)
    (heta_pos : 0 < eta)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h))
    (hsub : Finset.Ico c d ⊆ Finset.Ico a (b - h))
    (havoid :
      ∀ n : ℕ,
        n ∈ Finset.Ico c d →
          n ∉ Complex.realPhase_integerIncrementResonanceWindow
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h) (2 * Real.pi * (k : ℝ)) eta)
    (hprincipal :
      ∀ n : ℕ,
        n ∈ Finset.Ico c d →
          Complex.realPhase_integerIncrement
              (Complex.realPhase_integerLatticeShift
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                k)
              n ∈
            Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi))) :
    ‖∑ n ∈ Finset.Ico c d,
      Complex.exp
        (Complex.I *
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h n : ℂ))‖ ≤
      4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹ := by
  let ψ : ℝ → ℝ :=
    Complex.realPhase_secondDerivative_vdc_shiftedDifference
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      h
  let ψk : ℝ → ℝ :=
    Complex.realPhase_integerLatticeShift ψ k
  have hinputs :
      Complex.realPhase_integerIncrementMonotoneOn ψk c d ∧
        Complex.realPhase_reducedIntegerIncrementMonotoneOn ψk c d ∧
        Complex.realPhase_integerIncrementSeparatedOn ψk c d eta :=
    Complex.realPhase_integerLatticeShift_gap_finiteDifference_inputs
      ψ k hinc_mono hsub havoid hprincipal
  have hmajor_nonneg :
      0 ≤ 4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹ := by
    have heta_inv_nonneg : 0 ≤ eta⁻¹ :=
      inv_nonneg.mpr (le_of_lt heta_pos)
    have hinner_nonneg : 0 ≤ eta⁻¹ + 1 :=
      add_nonneg heta_inv_nonneg zero_le_one
    have hleft_nonneg : 0 ≤ 4 * (eta⁻¹ + 1) :=
      mul_nonneg zero_le_four hinner_nonneg
    have hfour_pi_nonneg : 0 ≤ 4 * Real.pi :=
      mul_nonneg zero_le_four Real.pi_nonneg
    have hright_nonneg : 0 ≤ 4 * Real.pi * eta⁻¹ :=
      mul_nonneg hfour_pi_nonneg heta_inv_nonneg
    exact add_nonneg hleft_nonneg hright_nonneg
  have hIcc :
      ∀ {r : ℕ},
        c ≤ r →
          r + 1 = d →
            ‖∑ n ∈ Finset.Icc c r,
              Complex.exp (Complex.I * (ψ n : ℂ))‖ ≤
              4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹ := by
    intro r hcr hrd
    have hrd_le : r ≤ d :=
      Eq.subst
        (motive := fun right : ℕ => r ≤ right)
        hrd
        (Nat.le_succ r)
    have hsubset_terminal : Finset.Ico c r ⊆ Finset.Ico c d :=
      Finset.Ico_subset_Ico (le_refl c) hrd_le
    have hmono_terminal :
        Complex.realPhase_integerIncrementMonotoneOn ψk c r :=
      Complex.realPhase_integerIncrementMonotoneOn.mono_Ico
        ψk hinputs.1 hsubset_terminal
    have hred_terminal :
        Complex.realPhase_reducedIntegerIncrementMonotoneOn ψk c r :=
      Complex.realPhase_reducedIntegerIncrementMonotoneOn.mono_Ico
        ψk hinputs.2.1 hsubset_terminal
    have hsep_terminal :
        Complex.realPhase_integerIncrementSeparatedOn ψk c r eta :=
      Complex.realPhase_integerIncrementSeparatedOn.mono_Ico
        ψk hinputs.2.2 hsubset_terminal
    have hshift :
        ‖∑ n ∈ Finset.Icc c r,
          Complex.exp (Complex.I * (ψk n : ℂ))‖ ≤
          4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹ :=
      Complex.realPhase_separatedIncrement_integer_block_bound
        ψk hc hcr heta_pos hmono_terminal hred_terminal hsep_terminal
    exact
      Complex.realPhase_sum_norm_le_of_integerLatticeShift_sum_norm_le
        ψ k (Finset.Icc c r) hshift
  exact
    Complex.realPhase_Ico_sum_norm_le_of_terminal_Icc_bounds
      ψ hmajor_nonneg hIcc

/-- A disjoint active-complement gap cover whose every gap is assigned an
integer lattice branch gives the first-derivative complement estimate at the
chosen resonance thickness. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_sum_norm_le_gapCount_mul_firstDerivativeMajorant_of_integerLatticeShift_gaps
    (t : ℝ)
    {a b h : ℕ}
    {eta : ℝ}
    (gaps : Finset (ℕ × ℕ))
    (center : ℕ × ℕ → ℤ)
    (ha : 1 ≤ a)
    (heta_pos : 0 < eta)
    (hcover :
      Complex.realPhase_IcoFamilyUnion gaps =
        Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
          t a b h eta)
    (hdisjoint :
      ∀ p₁ ∈ gaps,
        ∀ p₂ ∈ gaps,
          p₁ ≠ p₂ →
            Disjoint (Finset.Ico p₁.1 p₁.2) (Finset.Ico p₂.1 p₂.2))
    (hgap_bounds :
      ∀ p : ℕ × ℕ,
        p ∈ gaps →
          a ≤ p.1 ∧ p.2 ≤ b - h)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h))
    (havoid :
      ∀ p : ℕ × ℕ,
        p ∈ gaps →
          ∀ n : ℕ,
            n ∈ Finset.Ico p.1 p.2 →
              n ∉ Complex.realPhase_integerIncrementResonanceWindow
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                a (b - h) (2 * Real.pi * (center p : ℝ)) eta)
    (hprincipal :
      ∀ p : ℕ × ℕ,
        p ∈ gaps →
          ∀ n : ℕ,
            n ∈ Finset.Ico p.1 p.2 →
              Complex.realPhase_integerIncrement
                  (Complex.realPhase_integerLatticeShift
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    (center p))
                  n ∈
                Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi))) :
    ‖∑ n ∈
      Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
        t a b h eta,
      Complex.exp
        (Complex.I *
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h n : ℂ))‖ ≤
      ((gaps.card : ℝ) *
        (4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹)) := by
  let ψ : ℝ → ℝ :=
    Complex.realPhase_secondDerivative_vdc_shiftedDifference
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      h
  let F : ℕ → ℂ :=
    fun n : ℕ => Complex.exp (Complex.I * (ψ n : ℂ))
  have hgap :
      ∀ p : ℕ × ℕ,
        p ∈ gaps →
          ‖∑ n ∈ Finset.Ico p.1 p.2, F n‖ ≤
            4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹ := by
    intro p hp
    have hp_bounds : a ≤ p.1 ∧ p.2 ≤ b - h :=
      hgap_bounds p hp
    have hsub : Finset.Ico p.1 p.2 ⊆ Finset.Ico a (b - h) :=
      Finset.Ico_subset_Ico hp_bounds.1 hp_bounds.2
    exact
      Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_firstDerivativeMajorant_of_integerLatticeShift_gap
        (t := t) (a := a) (b := b) (c := p.1) (d := p.2)
        (h := h) (eta := eta)
        (center p)
        (le_trans ha hp_bounds.1)
        heta_pos hinc_mono hsub
        (havoid p hp)
        (hprincipal p hp)
  exact
    Complex.realPhase_sum_norm_le_card_mul_of_IcoFamily_cover
      (Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
        t a b h eta)
      gaps F hcover hdisjoint hgap

/-- Active-complement membership discharges the branch-window avoidance in
the first-derivative complement estimate. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_sum_norm_le_gapCount_mul_firstDerivativeMajorant_of_principal_integerLatticeShift_gaps
    (t : ℝ)
    {a b h : ℕ}
    {eta : ℝ}
    (gaps : Finset (ℕ × ℕ))
    (center : ℕ × ℕ → ℤ)
    (ha : 1 ≤ a)
    (heta_pos : 0 < eta)
    (hcover :
      Complex.realPhase_IcoFamilyUnion gaps =
        Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
          t a b h eta)
    (hdisjoint :
      ∀ p₁ ∈ gaps,
        ∀ p₂ ∈ gaps,
          p₁ ≠ p₂ →
            Disjoint (Finset.Ico p₁.1 p₁.2) (Finset.Ico p₂.1 p₂.2))
    (hgap_bounds :
      ∀ p : ℕ × ℕ,
        p ∈ gaps →
          a ≤ p.1 ∧ p.2 ≤ b - h)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h))
    (hprincipal :
      ∀ p : ℕ × ℕ,
        p ∈ gaps →
          ∀ n : ℕ,
            n ∈ Finset.Ico p.1 p.2 →
              Complex.realPhase_integerIncrement
                  (Complex.realPhase_integerLatticeShift
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    (center p))
                  n ∈
                Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi))) :
    ‖∑ n ∈
      Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
        t a b h eta,
      Complex.exp
        (Complex.I *
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h n : ℂ))‖ ≤
      ((gaps.card : ℝ) *
        (4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹)) := by
  have havoid :
      ∀ p : ℕ × ℕ,
        p ∈ gaps →
          ∀ n : ℕ,
            n ∈ Finset.Ico p.1 p.2 →
              n ∉ Complex.realPhase_integerIncrementResonanceWindow
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                a (b - h) (2 * Real.pi * (center p : ℝ)) eta := by
    intro p hp n hn hn_window
    have hn_union :
        n ∈ Complex.realPhase_IcoFamilyUnion gaps :=
      Finset.mem_biUnion.mpr
        (Exists.intro p (And.intro hp hn))
    have hn_complement :
        n ∈
          Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
            t a b h eta :=
      Eq.subst
        (motive := fun S : Finset ℕ => n ∈ S)
        hcover
        hn_union
    have hsep :
        eta ≤
          ‖Complex.realPhase_integerIncrement
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                h)
              n -
            (2 * Real.pi * (center p : ℝ))‖ :=
      Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_separated
        t hn_complement (center p)
    have hwindow_data :=
      (Complex.mem_realPhase_integerIncrementResonanceWindow_iff
        (φ :=
          Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h)
        (a := a)
        (b := b - h)
        (n := n)
        (resonance := 2 * Real.pi * (center p : ℝ))
        (lam := eta)).mp hn_window
    have hlt :
        ‖Complex.realPhase_integerIncrement
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            n -
          (2 * Real.pi * (center p : ℝ))‖ < eta :=
      hwindow_data.2
    exact not_lt_of_ge hsep hlt
  exact
    Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_sum_norm_le_gapCount_mul_firstDerivativeMajorant_of_integerLatticeShift_gaps
      t gaps center ha heta_pos hcover hdisjoint hgap_bounds
      hinc_mono havoid hprincipal

/-- Active-complement membership discharges the avoidance of the resonance
window for the integer lattice shift assigned to each gap.  The only remaining
geometric input is principal-branch control for that assigned shift. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_sum_norm_le_gapCount_mul_curvatureMajorant_of_principal_integerLatticeShift_gaps
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b h : ℕ}
    {lam : ℝ}
    (gaps : Finset (ℕ × ℕ))
    (center : ℕ × ℕ → ℤ)
    (ha : 1 ≤ a)
    (hpos : 1 ≤ h)
    (hlam :
      lam =
        ‖t‖ *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          (h : ℝ))
    (hcover :
      Complex.realPhase_IcoFamilyUnion gaps =
        Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
          t a b h lam)
    (hdisjoint :
      ∀ p₁ ∈ gaps,
        ∀ p₂ ∈ gaps,
          p₁ ≠ p₂ →
            Disjoint (Finset.Ico p₁.1 p₁.2) (Finset.Ico p₂.1 p₂.2))
    (hgap_bounds :
      ∀ p : ℕ × ℕ,
        p ∈ gaps →
          a ≤ p.1 ∧ p.2 ≤ b - h)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h))
    (hprincipal :
      ∀ p : ℕ × ℕ,
        p ∈ gaps →
          ∀ n : ℕ,
            n ∈ Finset.Ico p.1 p.2 →
              Complex.realPhase_integerIncrement
                  (Complex.realPhase_integerLatticeShift
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    (center p))
                  n ∈
                Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi))) :
    ‖∑ n ∈
      Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
        t a b h lam,
      Complex.exp
        (Complex.I *
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h n : ℂ))‖ ≤
      ((gaps.card : ℝ) *
        Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) := by
  have havoid :
      ∀ p : ℕ × ℕ,
        p ∈ gaps →
          ∀ n : ℕ,
            n ∈ Finset.Ico p.1 p.2 →
              n ∉ Complex.realPhase_integerIncrementResonanceWindow
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                a (b - h) (2 * Real.pi * (center p : ℝ)) lam := by
    intro p hp n hn hn_window
    have hn_union :
        n ∈ Complex.realPhase_IcoFamilyUnion gaps :=
      Finset.mem_biUnion.mpr
        (Exists.intro p (And.intro hp hn))
    have hn_complement :
        n ∈
          Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
            t a b h lam :=
      Eq.subst
        (motive := fun S : Finset ℕ => n ∈ S)
        hcover
        hn_union
    have hsep :
        lam ≤
          ‖Complex.realPhase_integerIncrement
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                h)
              n -
            (2 * Real.pi * (center p : ℝ))‖ :=
      Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_separated
        t hn_complement (center p)
    have hwindow_data :=
      (Complex.mem_realPhase_integerIncrementResonanceWindow_iff
        (φ :=
          Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h)
        (a := a)
        (b := b - h)
        (n := n)
        (resonance := 2 * Real.pi * (center p : ℝ))
        (lam := lam)).mp hn_window
    have hlt :
        ‖Complex.realPhase_integerIncrement
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            n -
          (2 * Real.pi * (center p : ℝ))‖ < lam :=
      hwindow_data.2
    exact not_lt_of_ge hsep hlt
  exact
    Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_sum_norm_le_gapCount_mul_curvatureMajorant_of_integerLatticeShift_gaps
      t ht gaps center ha hpos hlam hcover hdisjoint hgap_bounds
      hinc_mono havoid hprincipal

/-- A canonical active-complement gap cover, once each gap has been assigned
its principal lattice branch, gives the usual active-center-count complement
bound.  This is the counted summation form of the all-integer resonance
decomposition; the branch assignment is the only input not supplied by the
active-center cover itself. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_sum_norm_le_activeCenterCount_mul_curvatureMajorant_of_principal_gap_cover
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b h : ℕ}
    {lam : ℝ}
    (ha : 1 ≤ a)
    (habh : a ≤ b - h)
    (hpos : 1 ≤ h)
    (hlam :
      lam =
        ‖t‖ *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          (h : ℝ))
    (hlam_pi : lam ≤ Real.pi)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h))
    (hprincipal_cover :
      ∀ gaps : Finset (ℕ × ℕ),
        Complex.realPhase_IcoFamilyUnion gaps =
            Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
              t a b h lam →
          (∀ p₁ : ℕ × ℕ,
            p₁ ∈ gaps →
              ∀ p₂ : ℕ × ℕ,
                p₂ ∈ gaps →
                  p₁ ≠ p₂ →
                    Disjoint (Finset.Ico p₁.1 p₁.2)
                      (Finset.Ico p₂.1 p₂.2)) →
            Complex.realPhase_IcoFamilyBounded a (b - h) gaps →
              ∃ center : ℕ × ℕ → ℤ,
                ∀ p : ℕ × ℕ,
                  p ∈ gaps →
                    ∀ n : ℕ,
                      n ∈ Finset.Ico p.1 p.2 →
                        Complex.realPhase_integerIncrement
                            (Complex.realPhase_integerLatticeShift
                              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                                h)
                              (center p))
                            n ∈
                          Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi))) :
    ‖∑ n ∈
      Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
        t a b h lam,
      Complex.exp
        (Complex.I *
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h n : ℂ))‖ ≤
      ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
        t a b h lam).card + 1 : ℕ) : ℝ) *
        Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) := by
  have hcover_exists :
      ∃ gaps : Finset (ℕ × ℕ),
        Complex.realPhase_IcoFamilyUnion gaps =
            Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
              t a b h lam ∧
          (∀ p₁ : ℕ × ℕ,
            p₁ ∈ gaps →
              ∀ p₂ : ℕ × ℕ,
                p₂ ∈ gaps →
                  p₁ ≠ p₂ →
                    Disjoint (Finset.Ico p₁.1 p₁.2)
                      (Finset.Ico p₂.1 p₂.2)) ∧
          Complex.realPhase_IcoFamilyIntervalConnected gaps ∧
          Complex.realPhase_IcoFamilyBounded a (b - h) gaps ∧
          gaps.card ≤
            (Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h lam).card + 1 :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_exists_bounded_IcoFamily_cover_of_mono_of_le_pi
      t habh hinc_mono hlam_pi
  match hcover_exists with
  | ⟨gaps, hcover, hdisjoint, _hconnected, hbounded, hcard⟩ =>
      match hprincipal_cover gaps hcover hdisjoint hbounded with
      | ⟨center, hprincipal⟩ =>
          have hgap_bound :
              ‖∑ n ∈
                Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
                  t a b h lam,
                Complex.exp
                  (Complex.I *
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h n : ℂ))‖ ≤
                ((gaps.card : ℝ) *
                  Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) :=
            Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_sum_norm_le_gapCount_mul_curvatureMajorant_of_principal_integerLatticeShift_gaps
              t ht gaps center ha hpos hlam hcover hdisjoint hbounded
              hinc_mono hprincipal
          have hmajorant_nonneg :
              0 ≤ Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h :=
            Real.secondDerivativeVdc_shiftedCorrelationMajorant_nonneg ht hpos
          have hcard_real :
              (gaps.card : ℝ) ≤
                (((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
                  t a b h lam).card + 1 : ℕ) : ℝ) :=
            Nat.cast_le.mpr hcard
          have hmul :
              ((gaps.card : ℝ) *
                  Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) ≤
                ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
                  t a b h lam).card + 1 : ℕ) : ℝ) *
                  Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) :=
            mul_le_mul_of_nonneg_right hcard_real hmajorant_nonneg
          exact le_trans hgap_bound hmul

/-- A canonical active-complement gap cover, once each gap has been assigned
its principal lattice branch, gives the active-center-count complement bound
with the first-derivative majorant. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_sum_norm_le_activeCenterCount_mul_firstDerivativeMajorant_of_principal_gap_cover
    (t : ℝ)
    {a b h : ℕ}
    {eta : ℝ}
    (ha : 1 ≤ a)
    (habh : a ≤ b - h)
    (heta_pos : 0 < eta)
    (heta_pi : eta ≤ Real.pi)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h))
    (hprincipal_cover :
      ∀ gaps : Finset (ℕ × ℕ),
        Complex.realPhase_IcoFamilyUnion gaps =
            Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
              t a b h eta →
          (∀ p₁ : ℕ × ℕ,
            p₁ ∈ gaps →
              ∀ p₂ : ℕ × ℕ,
                p₂ ∈ gaps →
                  p₁ ≠ p₂ →
                    Disjoint (Finset.Ico p₁.1 p₁.2)
                      (Finset.Ico p₂.1 p₂.2)) →
            Complex.realPhase_IcoFamilyBounded a (b - h) gaps →
              ∃ center : ℕ × ℕ → ℤ,
                ∀ p : ℕ × ℕ,
                  p ∈ gaps →
                    ∀ n : ℕ,
                      n ∈ Finset.Ico p.1 p.2 →
                        Complex.realPhase_integerIncrement
                            (Complex.realPhase_integerLatticeShift
                              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                                h)
                              (center p))
                            n ∈
                          Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi))) :
    ‖∑ n ∈
      Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
        t a b h eta,
      Complex.exp
        (Complex.I *
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h n : ℂ))‖ ≤
      ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
        t a b h eta).card + 1 : ℕ) : ℝ) *
        (4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹)) := by
  have hcover_exists :
      ∃ gaps : Finset (ℕ × ℕ),
        Complex.realPhase_IcoFamilyUnion gaps =
            Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
              t a b h eta ∧
          (∀ p₁ : ℕ × ℕ,
            p₁ ∈ gaps →
              ∀ p₂ : ℕ × ℕ,
                p₂ ∈ gaps →
                  p₁ ≠ p₂ →
                    Disjoint (Finset.Ico p₁.1 p₁.2)
                      (Finset.Ico p₂.1 p₂.2)) ∧
          Complex.realPhase_IcoFamilyIntervalConnected gaps ∧
          Complex.realPhase_IcoFamilyBounded a (b - h) gaps ∧
          gaps.card ≤
            (Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h eta).card + 1 :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_exists_bounded_IcoFamily_cover_of_mono_of_le_pi
      t habh hinc_mono heta_pi
  match hcover_exists with
  | ⟨gaps, hcover, hdisjoint, _hconnected, hbounded, hcard⟩ =>
      match hprincipal_cover gaps hcover hdisjoint hbounded with
      | ⟨center, hprincipal⟩ =>
          have hgap_bound :
              ‖∑ n ∈
                Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
                  t a b h eta,
                Complex.exp
                  (Complex.I *
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h n : ℂ))‖ ≤
                ((gaps.card : ℝ) *
                  (4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹)) :=
            Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_sum_norm_le_gapCount_mul_firstDerivativeMajorant_of_principal_integerLatticeShift_gaps
              t gaps center ha heta_pos hcover hdisjoint hbounded
              hinc_mono hprincipal
          have hmajorant_nonneg :
              0 ≤ 4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹ := by
            have heta_inv_nonneg : 0 ≤ eta⁻¹ :=
              inv_nonneg.mpr (le_of_lt heta_pos)
            have hinner_nonneg : 0 ≤ eta⁻¹ + 1 :=
              add_nonneg heta_inv_nonneg zero_le_one
            have hleft_nonneg : 0 ≤ 4 * (eta⁻¹ + 1) :=
              mul_nonneg zero_le_four hinner_nonneg
            have hfour_pi_nonneg : 0 ≤ 4 * Real.pi :=
              mul_nonneg zero_le_four Real.pi_nonneg
            have hright_nonneg : 0 ≤ 4 * Real.pi * eta⁻¹ :=
              mul_nonneg hfour_pi_nonneg heta_inv_nonneg
            exact add_nonneg hleft_nonneg hright_nonneg
          have hcard_real :
              (gaps.card : ℝ) ≤
                (((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
                  t a b h eta).card + 1 : ℕ) : ℝ) :=
            Nat.cast_le.mpr hcard
          have hmul :
              ((gaps.card : ℝ) *
                  (4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹)) ≤
                ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
                  t a b h eta).card + 1 : ℕ) : ℝ) *
                  (4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹)) :=
            mul_le_mul_of_nonneg_right hcard_real hmajorant_nonneg
          exact le_trans hgap_bound hmul

/-- The active-family complement is controlled by refining its canonical gap
cover against every integer principal strip in the increment range. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_sum_norm_le_refinedPrincipalCount_mul_curvatureMajorant
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b h : ℕ}
    {lam lo hi : ℝ}
    (ha : 1 ≤ a)
    (habh : a ≤ b - h)
    (hpos : 1 ≤ h)
    (hlam :
      lam =
        ‖t‖ *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          (h : ℝ))
    (hlam_pi : lam ≤ Real.pi)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h))
    (hrange :
      ∀ n : ℕ,
        n ∈ Finset.Ico a (b - h) →
          lo ≤
              Complex.realPhase_integerIncrement
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                n ∧
            Complex.realPhase_integerIncrement
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                n ≤ hi) :
    ‖∑ n ∈
      Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
        t a b h lam,
      Complex.exp
        (Complex.I *
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h n : ℂ))‖ ≤
      ((Finset.Ico a (b - h)).card : ℝ) *
        Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h := by
  let ψ : ℝ → ℝ :=
    Complex.realPhase_secondDerivative_vdc_shiftedDifference
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      h
  let K : Finset ℤ :=
    Complex.realPhase_integerIncrementRangeActiveCenters lo hi Real.pi
  have hcover_exists :
      ∃ gaps : Finset (ℕ × ℕ),
        Complex.realPhase_IcoFamilyUnion gaps =
            Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
              t a b h lam ∧
          (∀ p₁ : ℕ × ℕ,
            p₁ ∈ gaps →
              ∀ p₂ : ℕ × ℕ,
                p₂ ∈ gaps →
                  p₁ ≠ p₂ →
                    Disjoint (Finset.Ico p₁.1 p₁.2)
                      (Finset.Ico p₂.1 p₂.2)) ∧
          Complex.realPhase_IcoFamilyIntervalConnected gaps ∧
          Complex.realPhase_IcoFamilyBounded a (b - h) gaps ∧
          gaps.card ≤
            (Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h lam).card + 1 :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_exists_bounded_IcoFamily_cover_of_mono_of_le_pi
      t habh hinc_mono hlam_pi
  match hcover_exists with
  | ⟨gaps, hcover, hdisjoint, _hconnected, hbounded, hgap_card⟩ =>
      have hrefine_exists :
          ∃ refined : Finset (ℕ × ℕ),
            refined.card ≤ (Finset.Ico a (b - h)).card ∧
              Complex.realPhase_IcoFamilyUnion refined =
                (Complex.realPhase_IcoFamilyUnion gaps).filter
                  (fun n : ℕ =>
                    n ∈
                      Complex.realPhase_integerIncrementPrincipalStripFamilyUnion
                        ψ a (b - h) K) ∧
              (∀ q₁ : ℕ × ℕ,
                q₁ ∈ refined →
                  ∀ q₂ : ℕ × ℕ,
                    q₂ ∈ refined →
                      q₁ ≠ q₂ →
                        Disjoint (Finset.Ico q₁.1 q₁.2)
                          (Finset.Ico q₂.1 q₂.2)) ∧
              (∀ q : ℕ × ℕ,
                q ∈ refined →
                  a ≤ q.1 ∧ q.2 ≤ b - h) ∧
              ∀ q : ℕ × ℕ,
                q ∈ refined →
                  ∃ p : ℕ × ℕ,
                    p ∈ gaps ∧
                      ∃ k : ℤ,
                        k ∈ K ∧
                          Finset.Ico q.1 q.2 =
                            (Finset.Ico p.1 p.2).filter
                              (fun n : ℕ =>
                                n ∈
                                  Complex.realPhase_integerIncrementPrincipalStrip
                                    ψ a (b - h) k) ∧
                          Finset.Ico q.1 q.2 ⊆
                            Complex.realPhase_integerIncrementPrincipalStrip
                              ψ a (b - h) k :=
        Complex.realPhase_principalStrip_nonempty_refinement_card_le_block
          ψ habh gaps K hbounded hdisjoint hinc_mono
      match hrefine_exists with
      | ⟨refined, hrefined_card, hrefined_cover_filter,
          hrefined_disjoint, hrefined_bounded, hrefined_principal⟩ =>
          have hcomplement_subset :
              Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
                  t a b h lam ⊆
                Complex.realPhase_integerIncrementPrincipalStripFamilyUnion
                  ψ a (b - h) K :=
            by
              have hblock_subset :
                  Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
                      t a b h lam ⊆
                    Finset.Ico a (b - h) := by
                intro n hn
                have hcomplement_data :=
                  (Complex.mem_realPhase_integerIncrementResonanceFamilyComplement_iff
                    ψ).mp hn
                exact hcomplement_data.1
              exact
                Complex.finset_subset_integerIncrementPrincipalStripFamilyUnion_rangeActiveCenters
                  ψ hblock_subset hrange
          have hrefined_cover :
              Complex.realPhase_IcoFamilyUnion refined =
                Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
                  t a b h lam := by
            exact Finset.ext
              (fun n =>
                Iff.intro
                  (fun hn =>
                    have hn_filter :
                        n ∈
                          (Complex.realPhase_IcoFamilyUnion gaps).filter
                            (fun m : ℕ =>
                              m ∈
                                Complex.realPhase_integerIncrementPrincipalStripFamilyUnion
                                  ψ a (b - h) K) :=
                      Eq.subst
                        (motive := fun S : Finset ℕ => n ∈ S)
                        hrefined_cover_filter
                        hn
                    have hn_gap :
                        n ∈ Complex.realPhase_IcoFamilyUnion gaps :=
                      (Finset.mem_filter.mp hn_filter).1
                    Eq.subst
                      (motive := fun S : Finset ℕ => n ∈ S)
                      hcover
                      hn_gap)
                  (fun hn =>
                    have hn_gap :
                        n ∈ Complex.realPhase_IcoFamilyUnion gaps :=
                      Eq.subst
                        (motive := fun S : Finset ℕ => n ∈ S)
                        hcover.symm
                        hn
                    have hn_family :
                        n ∈
                          Complex.realPhase_integerIncrementPrincipalStripFamilyUnion
                            ψ a (b - h) K :=
                      hcomplement_subset hn
                    have hn_filter :
                        n ∈
                          (Complex.realPhase_IcoFamilyUnion gaps).filter
                            (fun m : ℕ =>
                              m ∈
                                Complex.realPhase_integerIncrementPrincipalStripFamilyUnion
                                  ψ a (b - h) K) :=
                      Finset.mem_filter.mpr (And.intro hn_gap hn_family)
                    Eq.subst
                      (motive := fun S : Finset ℕ => n ∈ S)
                      hrefined_cover_filter.symm
                      hn_filter))
          have hgap_principal :
              ∀ q : ℕ × ℕ,
                q ∈ refined →
                  ∃ k : ℤ,
                    Finset.Ico q.1 q.2 ⊆
                      Complex.realPhase_integerIncrementPrincipalStrip
                        ψ a (b - h) k := by
            intro q hq
            match hrefined_principal q hq with
            | ⟨_p, _hp, k, _hk, _hfilter, hsubset⟩ =>
                exact Exists.intro k hsubset
          have hcenter_exists :
              ∃ center : ℕ × ℕ → ℤ,
                ∀ q : ℕ × ℕ,
                  q ∈ refined →
                    ∀ n : ℕ,
                      n ∈ Finset.Ico q.1 q.2 →
                        Complex.realPhase_integerIncrement
                            (Complex.realPhase_integerLatticeShift
                              ψ (center q))
                            n ∈
                          Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)) :=
            by
              have hq_exists :
                  ∀ q : ℕ × ℕ,
                    q ∈ refined →
                      ∃ k : ℤ,
                        ∀ n : ℕ,
                          n ∈ Finset.Ico q.1 q.2 →
                            Complex.realPhase_integerIncrement
                                (Complex.realPhase_integerLatticeShift ψ k) n ∈
                              Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)) := by
                intro q hq
                match hgap_principal q hq with
                | ⟨k, hk⟩ =>
                    exact Exists.intro k (fun n hn =>
                      ((Complex.mem_realPhase_integerIncrementPrincipalStrip_iff ψ).mp
                        (hk hn)).2)
              choose center hcenter using hq_exists
              exact Exists.intro center hcenter
          match hcenter_exists with
          | ⟨center, hprincipal⟩ =>
              have hrefined_sum :
                  ‖∑ n ∈
                    Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
                      t a b h lam,
                    Complex.exp
                      (Complex.I * (ψ n : ℂ))‖ ≤
                    ((refined.card : ℝ) *
                      Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) :=
                Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_sum_norm_le_gapCount_mul_curvatureMajorant_of_principal_integerLatticeShift_gaps
                  t ht refined center ha hpos hlam hrefined_cover
                  hrefined_disjoint hrefined_bounded hinc_mono hprincipal
              have hmajorant_nonneg :
                  0 ≤ Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h :=
                Real.secondDerivativeVdc_shiftedCorrelationMajorant_nonneg ht hpos
              have hrefined_card_real :
                  (refined.card : ℝ) ≤
                    ((Finset.Ico a (b - h)).card : ℝ) :=
                Nat.cast_le.mpr hrefined_card
              have hmul :
                  ((refined.card : ℝ) *
                      Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) ≤
                    ((Finset.Ico a (b - h)).card : ℝ) *
                      Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) :=
                mul_le_mul_of_nonneg_right hrefined_card_real hmajorant_nonneg
              exact le_trans hrefined_sum hmul

/-- The active-family complement is controlled by refining its canonical gap
cover against every integer principal strip in the increment range, with the
Kusmin-Landau scale set by the resonance thickness `eta`. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_sum_norm_le_refinedPrincipalCount_mul_firstDerivativeMajorant
    (t : ℝ)
    {a b h : ℕ}
    {eta lo hi : ℝ}
    (ha : 1 ≤ a)
    (habh : a ≤ b - h)
    (heta_pos : 0 < eta)
    (heta_pi : eta ≤ Real.pi)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h))
    (hrange :
      ∀ n : ℕ,
        n ∈ Finset.Ico a (b - h) →
          lo ≤
              Complex.realPhase_integerIncrement
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                n ∧
            Complex.realPhase_integerIncrement
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                n ≤ hi) :
    ‖∑ n ∈
      Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
        t a b h eta,
      Complex.exp
        (Complex.I *
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h n : ℂ))‖ ≤
      ((Finset.Ico a (b - h)).card : ℝ) *
        (4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹) := by
  let ψ : ℝ → ℝ :=
    Complex.realPhase_secondDerivative_vdc_shiftedDifference
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      h
  let K : Finset ℤ :=
    Complex.realPhase_integerIncrementRangeActiveCenters lo hi Real.pi
  have hcover_exists :
      ∃ gaps : Finset (ℕ × ℕ),
        Complex.realPhase_IcoFamilyUnion gaps =
            Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
              t a b h eta ∧
          (∀ p₁ : ℕ × ℕ,
            p₁ ∈ gaps →
              ∀ p₂ : ℕ × ℕ,
                p₂ ∈ gaps →
                  p₁ ≠ p₂ →
                    Disjoint (Finset.Ico p₁.1 p₁.2)
                      (Finset.Ico p₂.1 p₂.2)) ∧
          Complex.realPhase_IcoFamilyIntervalConnected gaps ∧
          Complex.realPhase_IcoFamilyBounded a (b - h) gaps ∧
          gaps.card ≤
            (Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h eta).card + 1 :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_exists_bounded_IcoFamily_cover_of_mono_of_le_pi
      t habh hinc_mono heta_pi
  match hcover_exists with
  | ⟨gaps, hcover, hdisjoint, _hconnected, hbounded, hgap_card⟩ =>
      have hrefine_exists :
          ∃ refined : Finset (ℕ × ℕ),
            refined.card ≤ (Finset.Ico a (b - h)).card ∧
              Complex.realPhase_IcoFamilyUnion refined =
                (Complex.realPhase_IcoFamilyUnion gaps).filter
                  (fun n : ℕ =>
                    n ∈
                      Complex.realPhase_integerIncrementPrincipalStripFamilyUnion
                        ψ a (b - h) K) ∧
              (∀ q₁ : ℕ × ℕ,
                q₁ ∈ refined →
                  ∀ q₂ : ℕ × ℕ,
                    q₂ ∈ refined →
                      q₁ ≠ q₂ →
                        Disjoint (Finset.Ico q₁.1 q₁.2)
                          (Finset.Ico q₂.1 q₂.2)) ∧
              (∀ q : ℕ × ℕ,
                q ∈ refined →
                  a ≤ q.1 ∧ q.2 ≤ b - h) ∧
              ∀ q : ℕ × ℕ,
                q ∈ refined →
                  ∃ p : ℕ × ℕ,
                    p ∈ gaps ∧
                      ∃ k : ℤ,
                        k ∈ K ∧
                          Finset.Ico q.1 q.2 =
                            (Finset.Ico p.1 p.2).filter
                              (fun n : ℕ =>
                                n ∈
                                  Complex.realPhase_integerIncrementPrincipalStrip
                                    ψ a (b - h) k) ∧
                          Finset.Ico q.1 q.2 ⊆
                            Complex.realPhase_integerIncrementPrincipalStrip
                              ψ a (b - h) k :=
        Complex.realPhase_principalStrip_nonempty_refinement_card_le_block
          ψ habh gaps K hbounded hdisjoint hinc_mono
      match hrefine_exists with
      | ⟨refined, hrefined_card, hrefined_cover_filter,
          hrefined_disjoint, hrefined_bounded, hrefined_principal⟩ =>
          have hcomplement_subset :
              Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
                  t a b h eta ⊆
                Complex.realPhase_integerIncrementPrincipalStripFamilyUnion
                  ψ a (b - h) K := by
            have hblock_subset :
                Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
                    t a b h eta ⊆
                  Finset.Ico a (b - h) := by
              intro n hn
              have hcomplement_data :=
                (Complex.mem_realPhase_integerIncrementResonanceFamilyComplement_iff
                  ψ).mp hn
              exact hcomplement_data.1
            exact
              Complex.finset_subset_integerIncrementPrincipalStripFamilyUnion_rangeActiveCenters
                ψ hblock_subset hrange
          have hrefined_cover :
              Complex.realPhase_IcoFamilyUnion refined =
                Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
                  t a b h eta := by
            exact Finset.ext
              (fun n =>
                Iff.intro
                  (fun hn =>
                    have hn_filter :
                        n ∈
                          (Complex.realPhase_IcoFamilyUnion gaps).filter
                            (fun m : ℕ =>
                              m ∈
                                Complex.realPhase_integerIncrementPrincipalStripFamilyUnion
                                  ψ a (b - h) K) :=
                      Eq.subst
                        (motive := fun S : Finset ℕ => n ∈ S)
                        hrefined_cover_filter
                        hn
                    have hn_gap :
                        n ∈ Complex.realPhase_IcoFamilyUnion gaps :=
                      (Finset.mem_filter.mp hn_filter).1
                    Eq.subst
                      (motive := fun S : Finset ℕ => n ∈ S)
                      hcover
                      hn_gap)
                  (fun hn =>
                    have hn_gap :
                        n ∈ Complex.realPhase_IcoFamilyUnion gaps :=
                      Eq.subst
                        (motive := fun S : Finset ℕ => n ∈ S)
                        hcover.symm
                        hn
                    have hn_family :
                        n ∈
                          Complex.realPhase_integerIncrementPrincipalStripFamilyUnion
                            ψ a (b - h) K :=
                      hcomplement_subset hn
                    have hn_filter :
                        n ∈
                          (Complex.realPhase_IcoFamilyUnion gaps).filter
                            (fun m : ℕ =>
                              m ∈
                                Complex.realPhase_integerIncrementPrincipalStripFamilyUnion
                                  ψ a (b - h) K) :=
                      Finset.mem_filter.mpr (And.intro hn_gap hn_family)
                    Eq.subst
                      (motive := fun S : Finset ℕ => n ∈ S)
                      hrefined_cover_filter.symm
                      hn_filter))
          have hgap_principal :
              ∀ q : ℕ × ℕ,
                q ∈ refined →
                  ∃ k : ℤ,
                    Finset.Ico q.1 q.2 ⊆
                      Complex.realPhase_integerIncrementPrincipalStrip
                        ψ a (b - h) k := by
            intro q hq
            match hrefined_principal q hq with
            | ⟨_p, _hp, k, _hk, _hfilter, hsubset⟩ =>
                exact Exists.intro k hsubset
          have hcenter_exists :
              ∃ center : ℕ × ℕ → ℤ,
                ∀ q : ℕ × ℕ,
                  q ∈ refined →
                    ∀ n : ℕ,
                      n ∈ Finset.Ico q.1 q.2 →
                        Complex.realPhase_integerIncrement
                            (Complex.realPhase_integerLatticeShift
                              ψ (center q))
                            n ∈
                          Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)) :=
            by
              have hq_exists :
                  ∀ q : ℕ × ℕ,
                    q ∈ refined →
                      ∃ k : ℤ,
                        ∀ n : ℕ,
                          n ∈ Finset.Ico q.1 q.2 →
                            Complex.realPhase_integerIncrement
                                (Complex.realPhase_integerLatticeShift ψ k) n ∈
                              Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)) := by
                intro q hq
                match hgap_principal q hq with
                | ⟨k, hk⟩ =>
                    exact Exists.intro k (fun n hn =>
                      ((Complex.mem_realPhase_integerIncrementPrincipalStrip_iff ψ).mp
                        (hk hn)).2)
              choose center hcenter using hq_exists
              exact Exists.intro center hcenter
          match hcenter_exists with
          | ⟨center, hprincipal⟩ =>
              have hrefined_sum :
                  ‖∑ n ∈
                    Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
                      t a b h eta,
                    Complex.exp
                      (Complex.I * (ψ n : ℂ))‖ ≤
                    ((refined.card : ℝ) *
                      (4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹)) :=
                Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_sum_norm_le_gapCount_mul_firstDerivativeMajorant_of_principal_integerLatticeShift_gaps
                  t refined center ha heta_pos hrefined_cover
                  hrefined_disjoint hrefined_bounded hinc_mono hprincipal
              have hmajorant_nonneg :
                  0 ≤ 4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹ := by
                have heta_inv_nonneg : 0 ≤ eta⁻¹ :=
                  inv_nonneg.mpr (le_of_lt heta_pos)
                have hinner_nonneg : 0 ≤ eta⁻¹ + 1 :=
                  add_nonneg heta_inv_nonneg zero_le_one
                have hleft_nonneg : 0 ≤ 4 * (eta⁻¹ + 1) :=
                  mul_nonneg zero_le_four hinner_nonneg
                have hfour_pi_nonneg : 0 ≤ 4 * Real.pi :=
                  mul_nonneg zero_le_four Real.pi_nonneg
                have hright_nonneg : 0 ≤ 4 * Real.pi * eta⁻¹ :=
                  mul_nonneg hfour_pi_nonneg heta_inv_nonneg
                exact add_nonneg hleft_nonneg hright_nonneg
              have hrefined_card_real :
                  (refined.card : ℝ) ≤
                    ((Finset.Ico a (b - h)).card : ℝ) :=
                Nat.cast_le.mpr hrefined_card
              have hmul :
                  ((refined.card : ℝ) *
                      (4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹)) ≤
                    ((Finset.Ico a (b - h)).card : ℝ) *
                      (4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹)) :=
                mul_le_mul_of_nonneg_right hrefined_card_real hmajorant_nonneg
              exact le_trans hrefined_sum hmul

/-- A shifted-logarithmic interval contained in the active resonance-family
complement has the first-derivative majorant at the chosen resonance
thickness.  The active-family complement supplies separation from every
integer lattice frequency; the ambient monotonicity data restrict to the
subinterval. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_firstDerivativeMajorant_of_activeComplement
    (t : ℝ)
    {a b c d h : ℕ}
    {eta : ℝ}
    (hc : 1 ≤ c)
    (hac : a ≤ c)
    (hdb : d ≤ b - h)
    (heta_pos : 0 < eta)
    (hgap_subset :
      Finset.Ico c d ⊆
        Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
          t a b h eta)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h))
    (hred_mono :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h)) :
    ‖∑ n ∈ Finset.Ico c d,
      Complex.exp
        (Complex.I *
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h n : ℂ))‖ ≤
      4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹ := by
  let ψ : ℝ → ℝ :=
    Complex.realPhase_secondDerivative_vdc_shiftedDifference
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      h
  have hsub : Finset.Ico c d ⊆ Finset.Ico a (b - h) :=
    Finset.Ico_subset_Ico hac hdb
  have hinc_local :
      Complex.realPhase_integerIncrementMonotoneOn ψ c d :=
    Complex.realPhase_integerIncrementMonotoneOn.mono_Ico
      ψ hinc_mono hsub
  have hred_local :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn ψ c d :=
    Complex.realPhase_reducedIntegerIncrementMonotoneOn.mono_Ico
      ψ hred_mono hsub
  have hsep_local :
      Complex.realPhase_integerIncrementSeparatedOn ψ c d eta :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_Ico_separated
      t hgap_subset
  have hmajor_nonneg :
      0 ≤ 4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹ := by
    have heta_inv_nonneg : 0 ≤ eta⁻¹ :=
      inv_nonneg.mpr (le_of_lt heta_pos)
    have hinner_nonneg : 0 ≤ eta⁻¹ + 1 :=
      add_nonneg heta_inv_nonneg zero_le_one
    have hleft_nonneg : 0 ≤ 4 * (eta⁻¹ + 1) :=
      mul_nonneg zero_le_four hinner_nonneg
    have hfour_pi_nonneg : 0 ≤ 4 * Real.pi :=
      mul_nonneg zero_le_four Real.pi_nonneg
    have hright_nonneg : 0 ≤ 4 * Real.pi * eta⁻¹ :=
      mul_nonneg hfour_pi_nonneg heta_inv_nonneg
    exact add_nonneg hleft_nonneg hright_nonneg
  have hIcc :
      ∀ {r : ℕ},
        c ≤ r →
          r + 1 = d →
            ‖∑ n ∈ Finset.Icc c r,
              Complex.exp (Complex.I * (ψ n : ℂ))‖ ≤
              4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹ := by
    intro r hcr hrd
    have hrd_le : r ≤ d :=
      Eq.subst
        (motive := fun right : ℕ => r ≤ right)
        hrd
        (Nat.le_succ r)
    have hsubset_terminal : Finset.Ico c r ⊆ Finset.Ico c d :=
      Finset.Ico_subset_Ico (le_refl c) hrd_le
    have hmono_terminal :
        Complex.realPhase_integerIncrementMonotoneOn ψ c r :=
      Complex.realPhase_integerIncrementMonotoneOn.mono_Ico
        ψ hinc_local hsubset_terminal
    have hred_terminal :
        Complex.realPhase_reducedIntegerIncrementMonotoneOn ψ c r :=
      Complex.realPhase_reducedIntegerIncrementMonotoneOn.mono_Ico
        ψ hred_local hsubset_terminal
    have hsep_terminal :
        Complex.realPhase_integerIncrementSeparatedOn ψ c r eta :=
      Complex.realPhase_integerIncrementSeparatedOn.mono_Ico
        ψ hsep_local hsubset_terminal
    exact
      Complex.realPhase_separatedIncrement_integer_block_bound
        ψ hc hcr heta_pos hmono_terminal hred_terminal hsep_terminal
  exact
    Complex.realPhase_Ico_sum_norm_le_of_terminal_Icc_bounds
      ψ hmajor_nonneg hIcc

/-- A disjoint half-open gap cover of the active-family complement gives the
first-derivative complement estimate with no principal-strip refinement. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_sum_norm_le_gapCount_mul_firstDerivativeMajorant
    (t : ℝ)
    {a b h : ℕ}
    {eta : ℝ}
    (gaps : Finset (ℕ × ℕ))
    (ha : 1 ≤ a)
    (heta_pos : 0 < eta)
    (hcover :
      Complex.realPhase_IcoFamilyUnion gaps =
        Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
          t a b h eta)
    (hdisjoint :
      ∀ p₁ ∈ gaps,
        ∀ p₂ ∈ gaps,
          p₁ ≠ p₂ →
            Disjoint (Finset.Ico p₁.1 p₁.2) (Finset.Ico p₂.1 p₂.2))
    (hgap_bounds :
      ∀ p : ℕ × ℕ,
        p ∈ gaps →
          a ≤ p.1 ∧ p.2 ≤ b - h)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h))
    (hred_mono :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h)) :
    ‖∑ n ∈
      Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
        t a b h eta,
      Complex.exp
        (Complex.I *
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h n : ℂ))‖ ≤
      ((gaps.card : ℝ) *
        (4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹)) := by
  let ψ : ℝ → ℝ :=
    Complex.realPhase_secondDerivative_vdc_shiftedDifference
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      h
  let F : ℕ → ℂ :=
    fun n : ℕ => Complex.exp (Complex.I * (ψ n : ℂ))
  have hgap :
      ∀ p : ℕ × ℕ,
        p ∈ gaps →
          ‖∑ n ∈ Finset.Ico p.1 p.2, F n‖ ≤
            4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹ := by
    intro p hp
    have hp_bounds : a ≤ p.1 ∧ p.2 ≤ b - h :=
      hgap_bounds p hp
    have hp_subset :
        Finset.Ico p.1 p.2 ⊆
          Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
            t a b h eta := by
      intro n hn
      have hn_union :
          n ∈ Complex.realPhase_IcoFamilyUnion gaps :=
        Finset.mem_biUnion.mpr
          (Exists.intro p (And.intro hp hn))
      exact
        Eq.subst
          (motive := fun S : Finset ℕ => n ∈ S)
          hcover
          hn_union
    exact
      Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_firstDerivativeMajorant_of_activeComplement
        (t := t) (a := a) (b := b) (c := p.1) (d := p.2)
        (h := h) (eta := eta)
        (le_trans ha hp_bounds.1) hp_bounds.1 hp_bounds.2
        heta_pos hp_subset hinc_mono hred_mono
  exact
    Complex.realPhase_sum_norm_le_card_mul_of_IcoFamily_cover
      (Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
        t a b h eta)
      gaps F hcover hdisjoint hgap

/-- The active-family complement is bounded by the active-center gap count at
an arbitrary first-derivative resonance thickness. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_sum_norm_le_activeCenterCount_mul_firstDerivativeMajorant
    (t : ℝ)
    {a b h : ℕ}
    {eta : ℝ}
    (ha : 1 ≤ a)
    (habh : a ≤ b - h)
    (heta_pos : 0 < eta)
    (heta_pi : eta ≤ Real.pi)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h))
    (hred_mono :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h)) :
    ‖∑ n ∈
      Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
        t a b h eta,
      Complex.exp
        (Complex.I *
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h n : ℂ))‖ ≤
      ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
        t a b h eta).card + 1 : ℕ) : ℝ) *
        (4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹)) := by
  have hcover_exists :
      ∃ gaps : Finset (ℕ × ℕ),
        Complex.realPhase_IcoFamilyUnion gaps =
            Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
              t a b h eta ∧
          (∀ p₁ : ℕ × ℕ,
            p₁ ∈ gaps →
              ∀ p₂ : ℕ × ℕ,
                p₂ ∈ gaps →
                  p₁ ≠ p₂ →
                    Disjoint (Finset.Ico p₁.1 p₁.2)
                      (Finset.Ico p₂.1 p₂.2)) ∧
          Complex.realPhase_IcoFamilyIntervalConnected gaps ∧
          Complex.realPhase_IcoFamilyBounded a (b - h) gaps ∧
          gaps.card ≤
            (Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h eta).card + 1 :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_exists_bounded_IcoFamily_cover_of_mono_of_le_pi
      t habh hinc_mono heta_pi
  match hcover_exists with
  | ⟨gaps, hcover, hdisjoint, _hconnected, hbounded, hcard⟩ =>
      have hgap_bound :
          ‖∑ n ∈
            Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
              t a b h eta,
            Complex.exp
              (Complex.I *
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h n : ℂ))‖ ≤
            ((gaps.card : ℝ) *
              (4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹)) :=
        Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_sum_norm_le_gapCount_mul_firstDerivativeMajorant
          t gaps ha heta_pos hcover hdisjoint hbounded hinc_mono hred_mono
      have hmajorant_nonneg :
          0 ≤ 4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹ := by
        have heta_inv_nonneg : 0 ≤ eta⁻¹ :=
          inv_nonneg.mpr (le_of_lt heta_pos)
        have hinner_nonneg : 0 ≤ eta⁻¹ + 1 :=
          add_nonneg heta_inv_nonneg zero_le_one
        have hleft_nonneg : 0 ≤ 4 * (eta⁻¹ + 1) :=
          mul_nonneg zero_le_four hinner_nonneg
        have hfour_pi_nonneg : 0 ≤ 4 * Real.pi :=
          mul_nonneg zero_le_four Real.pi_nonneg
        have hright_nonneg : 0 ≤ 4 * Real.pi * eta⁻¹ :=
          mul_nonneg hfour_pi_nonneg heta_inv_nonneg
        exact add_nonneg hleft_nonneg hright_nonneg
      have hcard_real :
          (gaps.card : ℝ) ≤
            (((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h eta).card + 1 : ℕ) : ℝ) :=
        Nat.cast_le.mpr hcard
      have hmul :
          ((gaps.card : ℝ) *
              (4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹)) ≤
            ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h eta).card + 1 : ℕ) : ℝ) *
              (4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹)) :=
        mul_le_mul_of_nonneg_right hcard_real hmajorant_nonneg
      exact le_trans hgap_bound hmul

/-- The active-family complement is bounded by the active-center gap count at
an arbitrary first-derivative resonance thickness, using the all-integer
monotone-curvature resonance decomposition.

This compatibility surface still carries the reduced-monotonicity hypothesis
required by the current finite-difference Kusmin-Landau primitive.  The
all-integer monotone gap owner below is the place where that dependency is
peeled. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_sum_norm_le_activeCenterCount_mul_allIntegerFirstDerivativeMajorant
    (t : ℝ)
    {a b h : ℕ}
    {eta : ℝ}
    (ha : 1 ≤ a)
    (habh : a ≤ b - h)
    (heta_pos : 0 < eta)
    (heta_pi : eta ≤ Real.pi)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h))
    (hred_mono :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h)) :
    ‖∑ n ∈
      Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
        t a b h eta,
      Complex.exp
        (Complex.I *
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h n : ℂ))‖ ≤
      ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
        t a b h eta).card + 1 : ℕ) : ℝ) *
          (4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹)) := by
  exact
    Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_sum_norm_le_activeCenterCount_mul_firstDerivativeMajorant
      t ha habh heta_pos heta_pi hinc_mono hred_mono

/-- Compatibility wrapper for older callers that already carry reduced
monotonicity. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_sum_norm_le_activeCenterCount_mul_allIntegerFirstDerivativeMajorant_of_reduced
    (t : ℝ)
    {a b h : ℕ}
    {eta : ℝ}
    (ha : 1 ≤ a)
    (habh : a ≤ b - h)
    (heta_pos : 0 < eta)
    (heta_pi : eta ≤ Real.pi)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h))
    (hred_mono :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h)) :
    ‖∑ n ∈
      Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
        t a b h eta,
      Complex.exp
        (Complex.I *
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h n : ℂ))‖ ≤
      ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
        t a b h eta).card + 1 : ℕ) : ℝ) *
          (4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹)) := by
  exact
    Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_sum_norm_le_activeCenterCount_mul_firstDerivativeMajorant
      t ha habh heta_pos heta_pi hinc_mono hred_mono

/-- Range control puts the active-resonance complement inside the finite
family of integer principal strips for the shifted logarithmic phase. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_subset_principalStripFamilyUnion_rangeActiveCenters
    (t : ℝ)
    {a b h : ℕ}
    {lam lo hi : ℝ}
    (hrange :
      ∀ n : ℕ,
        n ∈ Finset.Ico a (b - h) →
          lo ≤
              Complex.realPhase_integerIncrement
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                n ∧
            Complex.realPhase_integerIncrement
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                n ≤ hi) :
    Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
        t a b h lam ⊆
      Complex.realPhase_integerIncrementPrincipalStripFamilyUnion
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h)
        (Complex.realPhase_integerIncrementRangeActiveCenters
          lo hi Real.pi) := by
  have hblock_subset :
      Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
          t a b h lam ⊆
        Finset.Ico a (b - h) := by
    intro n hn
    have hcomplement_data :=
      (Complex.mem_realPhase_integerIncrementResonanceFamilyComplement_iff
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)).mp hn
    exact hcomplement_data.1
  exact
    Complex.finset_subset_integerIncrementPrincipalStripFamilyUnion_rangeActiveCenters
      (Complex.realPhase_secondDerivative_vdc_shiftedDifference
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        h)
      hblock_subset
      hrange

/-- Every active-complement sample has a concrete integer principal branch in
the finite range-active family.  This is the pointwise form of the all-integer
resonance decomposition: the branch is selected from the raw increment range,
not from a global no-winding assumption. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_exists_rangeActive_principalStrip
    (t : ℝ)
    {a b h n : ℕ}
    {lam lo hi : ℝ}
    (hrange :
      ∀ m : ℕ,
        m ∈ Finset.Ico a (b - h) →
          lo ≤
              Complex.realPhase_integerIncrement
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                m ∧
            Complex.realPhase_integerIncrement
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                m ≤ hi)
    (hn :
      n ∈
        Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
          t a b h lam) :
    ∃ k : ℤ,
      k ∈ Complex.realPhase_integerIncrementRangeActiveCenters lo hi Real.pi ∧
        n ∈
          Complex.realPhase_integerIncrementPrincipalStrip
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h) k := by
  have hsubset :
      Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
          t a b h lam ⊆
        Complex.realPhase_integerIncrementPrincipalStripFamilyUnion
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h)
          a (b - h)
          (Complex.realPhase_integerIncrementRangeActiveCenters
            lo hi Real.pi) :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_subset_principalStripFamilyUnion_rangeActiveCenters
      t hrange
  exact
    (Complex.mem_realPhase_integerIncrementPrincipalStripFamilyUnion_iff
      (Complex.realPhase_secondDerivative_vdc_shiftedDifference
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        h)).mp
      (hsubset hn)

/-- The active-complement sample count is bounded by the finite
range-active principal-strip family.  This is the counting side of the
all-integer principal-branch covering. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_card_le_principalStripFamilyUnion_rangeActiveCenters
    (t : ℝ)
    {a b h : ℕ}
    {lam lo hi : ℝ}
    (hrange :
      ∀ n : ℕ,
        n ∈ Finset.Ico a (b - h) →
          lo ≤
              Complex.realPhase_integerIncrement
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                n ∧
            Complex.realPhase_integerIncrement
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                n ≤ hi) :
    (Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
      t a b h lam).card ≤
      (Complex.realPhase_integerIncrementPrincipalStripFamilyUnion
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h)
        (Complex.realPhase_integerIncrementRangeActiveCenters
          lo hi Real.pi)).card := by
  exact
    Finset.card_le_card
      (Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_subset_principalStripFamilyUnion_rangeActiveCenters
        t hrange)

/-- Real-valued form of the finite all-integer principal-strip count for the
active complement. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_card_real_le_principalStripFamilyUnion_rangeActiveCenters
    (t : ℝ)
    {a b h : ℕ}
    {lam lo hi : ℝ}
    (hrange :
      ∀ n : ℕ,
        n ∈ Finset.Ico a (b - h) →
          lo ≤
              Complex.realPhase_integerIncrement
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                n ∧
            Complex.realPhase_integerIncrement
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                n ≤ hi) :
    ((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
      t a b h lam).card : ℝ) ≤
      ((Complex.realPhase_integerIncrementPrincipalStripFamilyUnion
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h)
        (Complex.realPhase_integerIncrementRangeActiveCenters
          lo hi Real.pi)).card : ℝ) := by
  exact
    Nat.cast_le.mpr
      (Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_card_le_principalStripFamilyUnion_rangeActiveCenters
        t hrange)

/-- The active-complement count is bounded by the sum of the cardinalities of
the range-active principal strips. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_card_real_le_sum_rangeActive_principalStrip_cards
    (t : ℝ)
    {a b h : ℕ}
    {lam lo hi : ℝ}
    (hrange :
      ∀ n : ℕ,
        n ∈ Finset.Ico a (b - h) →
          lo ≤
              Complex.realPhase_integerIncrement
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                n ∧
            Complex.realPhase_integerIncrement
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                n ≤ hi) :
    ((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
      t a b h lam).card : ℝ) ≤
      ∑ k ∈ Complex.realPhase_integerIncrementRangeActiveCenters lo hi Real.pi,
        ((Complex.realPhase_integerIncrementPrincipalStrip
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h)
          a (b - h) k).card : ℝ) := by
  have hle_family :
      ((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
        t a b h lam).card : ℝ) ≤
        ((Complex.realPhase_integerIncrementPrincipalStripFamilyUnion
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h)
          a (b - h)
          (Complex.realPhase_integerIncrementRangeActiveCenters
            lo hi Real.pi)).card : ℝ) :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_card_real_le_principalStripFamilyUnion_rangeActiveCenters
      t hrange
  have hfamily_eq :
      ((Complex.realPhase_integerIncrementPrincipalStripFamilyUnion
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h)
          a (b - h)
          (Complex.realPhase_integerIncrementRangeActiveCenters
            lo hi Real.pi)).card : ℝ) =
        ∑ k ∈ Complex.realPhase_integerIncrementRangeActiveCenters lo hi Real.pi,
          ((Complex.realPhase_integerIncrementPrincipalStrip
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h) k).card : ℝ) :=
    Complex.realPhase_integerIncrementPrincipalStripFamilyUnion_card_real_eq_sum_cards
      (Complex.realPhase_secondDerivative_vdc_shiftedDifference
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        h)
      (Complex.realPhase_integerIncrementRangeActiveCenters lo hi Real.pi)
  exact
    Eq.subst
      (motive := fun right : ℝ =>
        ((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
          t a b h lam).card : ℝ) ≤ right)
      hfamily_eq
      hle_family

/-- A disjoint half-open gap cover of the active-family complement gives the
standard finite-gap complement estimate.  The active-family complement supplies
the lattice separation on each gap; the supplied cover supplies only the
finite interval decomposition. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_sum_norm_le_gapCount_mul_curvatureMajorant
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b h : ℕ}
    {lam : ℝ}
    (gaps : Finset (ℕ × ℕ))
    (ha : 1 ≤ a)
    (hpos : 1 ≤ h)
    (hlam :
      lam =
        ‖t‖ *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          (h : ℝ))
    (hcover :
      Complex.realPhase_IcoFamilyUnion gaps =
        Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
          t a b h lam)
    (hdisjoint :
      ∀ p₁ ∈ gaps,
        ∀ p₂ ∈ gaps,
          p₁ ≠ p₂ →
            Disjoint (Finset.Ico p₁.1 p₁.2) (Finset.Ico p₂.1 p₂.2))
    (hgap_bounds :
      ∀ p : ℕ × ℕ,
        p ∈ gaps →
          a ≤ p.1 ∧ p.2 ≤ b - h)
    (hderiv_antitone :
      AntitoneOn
        (fun x : ℝ =>
          ‖deriv
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h) x‖)
        (Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)))
    (hderiv_lower :
      ∀ x : ℝ,
        x ∈ Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ) →
          ‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (h : ℝ) ≤
            ‖deriv
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                h) x‖)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h))
    (hred_mono :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h)) :
    ‖∑ n ∈
      Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
        t a b h lam,
      Complex.exp
        (Complex.I *
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h n : ℂ))‖ ≤
      ((gaps.card : ℝ) *
        Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) := by
  let ψ : ℝ → ℝ :=
    Complex.realPhase_secondDerivative_vdc_shiftedDifference
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      h
  let F : ℕ → ℂ :=
    fun n : ℕ => Complex.exp (Complex.I * (ψ n : ℂ))
  have hgap :
      ∀ p : ℕ × ℕ,
        p ∈ gaps →
          ‖∑ n ∈ Finset.Ico p.1 p.2, F n‖ ≤
            Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h := by
    intro p hp
    have hp_bounds : a ≤ p.1 ∧ p.2 ≤ b - h :=
      hgap_bounds p hp
    have hp_subset :
        Finset.Ico p.1 p.2 ⊆
          Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
            t a b h lam := by
      intro n hn
      have hn_union :
          n ∈ Complex.realPhase_IcoFamilyUnion gaps :=
        Finset.mem_biUnion.mpr
          (Exists.intro p (And.intro hp hn))
      exact
        Eq.subst
          (motive := fun S : Finset ℕ => n ∈ S)
          hcover
          hn_union
    exact
      Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_curvatureMajorant_of_activeComplement
        (t := t) (ht := ht) (a := a) (b := b) (c := p.1) (d := p.2)
        (h := h) (lam := lam)
        (le_trans ha hp_bounds.1) hp_bounds.1 hp_bounds.2 hpos hlam hp_subset
        hderiv_antitone hderiv_lower hinc_mono hred_mono
  exact
    Complex.realPhase_sum_norm_le_card_mul_of_IcoFamily_cover
      (Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
        t a b h lam)
      gaps F hcover hdisjoint hgap

/-- The active-family complement is bounded by the finite integer-center gap
count once monotonicity supplies the canonical bounded gap cover. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_sum_norm_le_activeCenterCount_mul_curvatureMajorant
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b h : ℕ}
    {lam : ℝ}
    (ha : 1 ≤ a)
    (habh : a ≤ b - h)
    (hpos : 1 ≤ h)
    (hlam :
      lam =
        ‖t‖ *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          (h : ℝ))
    (hlam_pi : lam ≤ Real.pi)
    (hderiv_antitone :
      AntitoneOn
        (fun x : ℝ =>
          ‖deriv
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h) x‖)
        (Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)))
    (hderiv_lower :
      ∀ x : ℝ,
        x ∈ Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ) →
          ‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (h : ℝ) ≤
            ‖deriv
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                h) x‖)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h))
    (hred_mono :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h)) :
    ‖∑ n ∈
      Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
        t a b h lam,
      Complex.exp
        (Complex.I *
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h n : ℂ))‖ ≤
      ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
        t a b h lam).card + 1 : ℕ) : ℝ) *
        Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) := by
  have hcover_exists :
      ∃ gaps : Finset (ℕ × ℕ),
        Complex.realPhase_IcoFamilyUnion gaps =
            Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
              t a b h lam ∧
          (∀ p₁ : ℕ × ℕ,
            p₁ ∈ gaps →
              ∀ p₂ : ℕ × ℕ,
                p₂ ∈ gaps →
                  p₁ ≠ p₂ →
                    Disjoint (Finset.Ico p₁.1 p₁.2)
                      (Finset.Ico p₂.1 p₂.2)) ∧
          Complex.realPhase_IcoFamilyIntervalConnected gaps ∧
          Complex.realPhase_IcoFamilyBounded a (b - h) gaps ∧
          gaps.card ≤
            (Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h lam).card + 1 :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_exists_bounded_IcoFamily_cover_of_mono_of_le_pi
      t habh hinc_mono hlam_pi
  match hcover_exists with
  | ⟨gaps, hcover, hdisjoint, _hconnected, hbounded, hcard⟩ =>
      have hgap_bound :
          ‖∑ n ∈
            Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
              t a b h lam,
            Complex.exp
              (Complex.I *
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h n : ℂ))‖ ≤
            ((gaps.card : ℝ) *
              Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) :=
        Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_sum_norm_le_gapCount_mul_curvatureMajorant
          t ht gaps ha hpos hlam hcover hdisjoint hbounded
          hderiv_antitone hderiv_lower hinc_mono hred_mono
      have hmajorant_nonneg :
          0 ≤ Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h :=
        Real.secondDerivativeVdc_shiftedCorrelationMajorant_nonneg ht hpos
      have hcard_real :
          (gaps.card : ℝ) ≤
            (((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h lam).card + 1 : ℕ) : ℝ) :=
        Nat.cast_le.mpr hcard
      have hmul :
          ((gaps.card : ℝ) *
              Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) ≤
            ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h lam).card + 1 : ℕ) : ℝ) *
              Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) :=
        mul_le_mul_of_nonneg_right hcard_real hmajorant_nonneg
      exact le_trans hgap_bound hmul

/-- All integer-centered active resonance windows together with their bounded
complement gaps control one shifted half-open correlation block. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_activeCenterCount_window_add_gapMajorants
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b h : ℕ}
    {lam W : ℝ}
    (ha : 1 ≤ a)
    (habh : a ≤ b - h)
    (hpos : 1 ≤ h)
    (hlam :
      lam =
        ‖t‖ *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          (h : ℝ))
    (hlam_pi : lam ≤ Real.pi)
    (hwindow :
      ∀ k : ℤ,
        k ∈
          Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h lam →
          ((Complex.realPhase_integerIncrementResonanceWindow
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h) (2 * Real.pi * (k : ℝ)) lam).card : ℝ) ≤ W)
    (hderiv_antitone :
      AntitoneOn
        (fun x : ℝ =>
          ‖deriv
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h) x‖)
        (Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)))
    (hderiv_lower :
      ∀ x : ℝ,
        x ∈ Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ) →
          ‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (h : ℝ) ≤
            ‖deriv
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                h) x‖)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h))
    (hred_mono :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h)) :
    ‖∑ n ∈ Finset.Ico a (b - h),
      Complex.exp
        (Complex.I *
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h n : ℂ))‖ ≤
      (((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
        t a b h lam).card : ℝ) * W) +
        ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
          t a b h lam).card + 1 : ℕ) : ℝ) *
          Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) := by
  have hunion :
      ‖∑ n ∈
        Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceUnion
          t a b h lam,
        Complex.exp
          (Complex.I *
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h n : ℂ))‖ ≤
        (((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
          t a b h lam).card : ℝ) * W) :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceUnion_sum_norm_le_card_mul_window_bound
      t hwindow
  have hgap :
      ‖∑ n ∈
        Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
          t a b h lam,
        Complex.exp
          (Complex.I *
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h n : ℂ))‖ ≤
        ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
          t a b h lam).card + 1 : ℕ) : ℝ) *
          Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_sum_norm_le_activeCenterCount_mul_curvatureMajorant
      t ht ha habh hpos hlam hlam_pi hderiv_antitone hderiv_lower
      hinc_mono hred_mono
  exact
    Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_of_activeResonanceFamily_bounds
      t lam hunion hgap (le_of_eq rfl)

/-- Active resonance windows plus the refined all-principal-branch complement
control one shifted half-open correlation block. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_activeCenterCount_window_add_refinedPrincipalGapMajorants
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b h : ℕ}
    {lam W lo hi : ℝ}
    (ha : 1 ≤ a)
    (habh : a ≤ b - h)
    (hpos : 1 ≤ h)
    (hlam :
      lam =
        ‖t‖ *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          (h : ℝ))
    (hlam_pi : lam ≤ Real.pi)
    (hrange :
      ∀ n : ℕ,
        n ∈ Finset.Ico a (b - h) →
          lo ≤
              Complex.realPhase_integerIncrement
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                n ∧
            Complex.realPhase_integerIncrement
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                n ≤ hi)
    (hwindow :
      ∀ k : ℤ,
        k ∈
          Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h lam →
          ((Complex.realPhase_integerIncrementResonanceWindow
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h) (2 * Real.pi * (k : ℝ)) lam).card : ℝ) ≤ W)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h))
    (hred_mono :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h)) :
    ‖∑ n ∈ Finset.Ico a (b - h),
      Complex.exp
        (Complex.I *
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h n : ℂ))‖ ≤
      (((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
        t a b h lam).card : ℝ) * W) +
        (((Finset.Ico a (b - h)).card : ℝ) *
          Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) := by
  have hunion :
      ‖∑ n ∈
        Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceUnion
          t a b h lam,
        Complex.exp
          (Complex.I *
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h n : ℂ))‖ ≤
        (((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
          t a b h lam).card : ℝ) * W) :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceUnion_sum_norm_le_card_mul_window_bound
      t hwindow
  have hgap :
      ‖∑ n ∈
        Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
          t a b h lam,
        Complex.exp
          (Complex.I *
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h n : ℂ))‖ ≤
        (((Finset.Ico a (b - h)).card : ℝ) *
          Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_sum_norm_le_refinedPrincipalCount_mul_curvatureMajorant
      t ht ha habh hpos hlam hlam_pi hinc_mono hrange
  exact
    Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_of_activeResonanceFamily_bounds
      t lam hunion hgap (le_of_eq rfl)

/-- Active resonance windows plus the refined all-principal-branch complement
control one shifted half-open correlation block at an arbitrary resonance
thickness `eta`. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_activeCenterCount_window_add_refinedPrincipalFirstDerivativeGapMajorants
    (t : ℝ)
    {a b h : ℕ}
    {eta W lo hi : ℝ}
    (ha : 1 ≤ a)
    (habh : a ≤ b - h)
    (heta_pos : 0 < eta)
    (heta_pi : eta ≤ Real.pi)
    (hrange :
      ∀ n : ℕ,
        n ∈ Finset.Ico a (b - h) →
          lo ≤
              Complex.realPhase_integerIncrement
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                n ∧
            Complex.realPhase_integerIncrement
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                n ≤ hi)
    (hwindow :
      ∀ k : ℤ,
        k ∈
          Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h eta →
          ((Complex.realPhase_integerIncrementResonanceWindow
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h) (2 * Real.pi * (k : ℝ)) eta).card : ℝ) ≤ W)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h))
    (hred_mono :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h)) :
    ‖∑ n ∈ Finset.Ico a (b - h),
      Complex.exp
        (Complex.I *
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h n : ℂ))‖ ≤
      (((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
        t a b h eta).card : ℝ) * W) +
        (((Finset.Ico a (b - h)).card : ℝ) *
          (4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹)) := by
  have hunion :
      ‖∑ n ∈
        Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceUnion
          t a b h eta,
        Complex.exp
          (Complex.I *
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h n : ℂ))‖ ≤
        (((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
          t a b h eta).card : ℝ) * W) :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceUnion_sum_norm_le_card_mul_window_bound
      t hwindow
  have hgap :
      ‖∑ n ∈
        Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
          t a b h eta,
        Complex.exp
          (Complex.I *
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h n : ℂ))‖ ≤
        (((Finset.Ico a (b - h)).card : ℝ) *
          (4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹)) :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_sum_norm_le_refinedPrincipalCount_mul_firstDerivativeMajorant
      t ha habh heta_pos heta_pi hinc_mono hrange
  exact
    Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_of_activeResonanceFamily_bounds
      t eta hunion hgap (le_of_eq rfl)

/-- Active resonance windows plus the direct active-center gap-count
complement control one shifted half-open correlation block at an arbitrary
resonance thickness. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_activeCenterCount_window_add_firstDerivativeGapMajorants
    (t : ℝ)
    {a b h : ℕ}
    {eta W : ℝ}
    (ha : 1 ≤ a)
    (habh : a ≤ b - h)
    (heta_pos : 0 < eta)
    (heta_pi : eta ≤ Real.pi)
    (hwindow :
      ∀ k : ℤ,
        k ∈
          Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h eta →
          ((Complex.realPhase_integerIncrementResonanceWindow
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h) (2 * Real.pi * (k : ℝ)) eta).card : ℝ) ≤ W)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h))
    (hred_mono :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h)) :
    ‖∑ n ∈ Finset.Ico a (b - h),
      Complex.exp
        (Complex.I *
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h n : ℂ))‖ ≤
      (((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
        t a b h eta).card : ℝ) * W) +
        ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
          t a b h eta).card + 1 : ℕ) : ℝ) *
          (4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹)) := by
  have hunion :
      ‖∑ n ∈
        Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceUnion
          t a b h eta,
        Complex.exp
          (Complex.I *
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h n : ℂ))‖ ≤
        (((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
          t a b h eta).card : ℝ) * W) :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceUnion_sum_norm_le_card_mul_window_bound
      t hwindow
  have hgap :
      ‖∑ n ∈
        Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
          t a b h eta,
        Complex.exp
          (Complex.I *
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h n : ℂ))‖ ≤
        ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
          t a b h eta).card + 1 : ℕ) : ℝ) *
          (4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹)) :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_sum_norm_le_activeCenterCount_mul_allIntegerFirstDerivativeMajorant
      t ha habh heta_pos heta_pi hinc_mono hred_mono
  exact
    Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_of_activeResonanceFamily_bounds
      t eta hunion hgap (le_of_eq rfl)

/-- Active resonance windows plus the direct active-center gap-count
complement control one shifted half-open correlation block at an arbitrary
resonance thickness, using the all-integer monotone Kusmin-Landau primitive. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_activeCenterCount_window_add_allIntegerFirstDerivativeGapMajorants
    (t : ℝ)
    {a b h : ℕ}
    {eta W : ℝ}
    (ha : 1 ≤ a)
    (habh : a ≤ b - h)
    (heta_pos : 0 < eta)
    (heta_pi : eta ≤ Real.pi)
    (hwindow :
      ∀ k : ℤ,
        k ∈
          Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h eta →
          ((Complex.realPhase_integerIncrementResonanceWindow
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h) (2 * Real.pi * (k : ℝ)) eta).card : ℝ) ≤ W)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h))
    (hred_mono :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h)) :
    ‖∑ n ∈ Finset.Ico a (b - h),
      Complex.exp
        (Complex.I *
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h n : ℂ))‖ ≤
      (((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
        t a b h eta).card : ℝ) * W) +
        ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
          t a b h eta).card + 1 : ℕ) : ℝ) *
          (4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹)) := by
  have hunion :
      ‖∑ n ∈
        Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceUnion
          t a b h eta,
        Complex.exp
          (Complex.I *
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h n : ℂ))‖ ≤
        (((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
          t a b h eta).card : ℝ) * W) :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceUnion_sum_norm_le_card_mul_window_bound
      t hwindow
  have hgap :
      ‖∑ n ∈
        Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
          t a b h eta,
        Complex.exp
          (Complex.I *
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h n : ℂ))‖ ≤
        ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
          t a b h eta).card + 1 : ℕ) : ℝ) *
          (4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹)) :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_sum_norm_le_activeCenterCount_mul_allIntegerFirstDerivativeMajorant_of_reduced
      t ha habh heta_pos heta_pi hinc_mono hred_mono
  exact
    Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_of_activeResonanceFamily_bounds
      t eta hunion hgap (le_of_eq rfl)

/-- Closed shifted correlations inherit the all-integer active-resonance
decomposition with the terminal endpoint contribution made explicit. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedCorrelation_norm_le_activeCenterCount_window_add_gapMajorants_add_one
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b h : ℕ}
    {lam W : ℝ}
    (ha : 1 ≤ a)
    (habh : a ≤ b - h)
    (hpos : 1 ≤ h)
    (hlam :
      lam =
        ‖t‖ *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          (h : ℝ))
    (hlam_pi : lam ≤ Real.pi)
    (hwindow :
      ∀ k : ℤ,
        k ∈
          Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h lam →
          ((Complex.realPhase_integerIncrementResonanceWindow
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h) (2 * Real.pi * (k : ℝ)) lam).card : ℝ) ≤ W)
    (hderiv_antitone :
      AntitoneOn
        (fun x : ℝ =>
          ‖deriv
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h) x‖)
        (Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)))
    (hderiv_lower :
      ∀ x : ℝ,
        x ∈ Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ) →
          ‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (h : ℝ) ≤
            ‖deriv
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                h) x‖)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h))
    (hred_mono :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h)) :
    ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖ ≤
      ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
        t a b h lam).card : ℝ) * W) +
        ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
          t a b h lam).card + 1 : ℕ) : ℝ) *
          Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h)) +
        1 := by
  have hclosed :
      ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖ ≤
        ‖∑ n ∈ Finset.Ico a (b - h),
          Complex.exp
            (Complex.I *
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                h n : ℂ))‖ + 1 :=
    Complex.logarithmicPhaseRealPhase_shiftedCorrelation_norm_le_Ico_sum_norm_add_one
      t habh
  have hIco :
      ‖∑ n ∈ Finset.Ico a (b - h),
        Complex.exp
          (Complex.I *
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h n : ℂ))‖ ≤
        (((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
          t a b h lam).card : ℝ) * W) +
          ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h lam).card + 1 : ℕ) : ℝ) *
            Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_activeCenterCount_window_add_gapMajorants
      t ht ha habh hpos hlam hlam_pi hwindow
      hderiv_antitone hderiv_lower hinc_mono hred_mono
  exact le_trans hclosed (add_le_add_right hIco 1)

/-- Closed shifted correlations inherit the refined all-principal-branch
active resonance decomposition. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedCorrelation_norm_le_activeCenterCount_window_add_refinedPrincipalGapMajorants_add_one
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b h : ℕ}
    {lam W lo hi : ℝ}
    (ha : 1 ≤ a)
    (habh : a ≤ b - h)
    (hpos : 1 ≤ h)
    (hlam :
      lam =
        ‖t‖ *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          (h : ℝ))
    (hlam_pi : lam ≤ Real.pi)
    (hrange :
      ∀ n : ℕ,
        n ∈ Finset.Ico a (b - h) →
          lo ≤
              Complex.realPhase_integerIncrement
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                n ∧
            Complex.realPhase_integerIncrement
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                n ≤ hi)
    (hwindow :
      ∀ k : ℤ,
        k ∈
          Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h lam →
          ((Complex.realPhase_integerIncrementResonanceWindow
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h) (2 * Real.pi * (k : ℝ)) lam).card : ℝ) ≤ W)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h))
    (hred_mono :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h)) :
    ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖ ≤
      ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
        t a b h lam).card : ℝ) * W) +
        (((Finset.Ico a (b - h)).card : ℝ) *
          Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h)) +
        1 := by
  have hclosed :
      ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖ ≤
        ‖∑ n ∈ Finset.Ico a (b - h),
          Complex.exp
            (Complex.I *
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                h n : ℂ))‖ + 1 :=
    Complex.logarithmicPhaseRealPhase_shiftedCorrelation_norm_le_Ico_sum_norm_add_one
      t habh
  have hIco :
      ‖∑ n ∈ Finset.Ico a (b - h),
        Complex.exp
          (Complex.I *
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h n : ℂ))‖ ≤
        (((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
          t a b h lam).card : ℝ) * W) +
          (((Finset.Ico a (b - h)).card : ℝ) *
            Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_activeCenterCount_window_add_refinedPrincipalGapMajorants
      t ht ha habh hpos hlam hlam_pi hrange hwindow hinc_mono hred_mono
  exact le_trans hclosed (add_le_add_right hIco 1)

/-- Closed shifted correlations inherit the refined all-principal-branch
active resonance decomposition with first-derivative complement gaps. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedCorrelation_norm_le_activeCenterCount_window_add_refinedPrincipalFirstDerivativeGapMajorants_add_one
    (t : ℝ)
    {a b h : ℕ}
    {eta W lo hi : ℝ}
    (ha : 1 ≤ a)
    (habh : a ≤ b - h)
    (heta_pos : 0 < eta)
    (heta_pi : eta ≤ Real.pi)
    (hrange :
      ∀ n : ℕ,
        n ∈ Finset.Ico a (b - h) →
          lo ≤
              Complex.realPhase_integerIncrement
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                n ∧
            Complex.realPhase_integerIncrement
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                n ≤ hi)
    (hwindow :
      ∀ k : ℤ,
        k ∈
          Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h eta →
          ((Complex.realPhase_integerIncrementResonanceWindow
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h) (2 * Real.pi * (k : ℝ)) eta).card : ℝ) ≤ W)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h))
    (hred_mono :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h)) :
    ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖ ≤
      ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
        t a b h eta).card : ℝ) * W) +
        (((Finset.Ico a (b - h)).card : ℝ) *
          (4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹))) +
        1 := by
  have hclosed :
      ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖ ≤
        ‖∑ n ∈ Finset.Ico a (b - h),
          Complex.exp
            (Complex.I *
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                h n : ℂ))‖ + 1 :=
    Complex.logarithmicPhaseRealPhase_shiftedCorrelation_norm_le_Ico_sum_norm_add_one
      t habh
  have hIco :
      ‖∑ n ∈ Finset.Ico a (b - h),
        Complex.exp
          (Complex.I *
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h n : ℂ))‖ ≤
        (((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
          t a b h eta).card : ℝ) * W) +
          (((Finset.Ico a (b - h)).card : ℝ) *
            (4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹)) :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_activeCenterCount_window_add_refinedPrincipalFirstDerivativeGapMajorants
      t ha habh heta_pos heta_pi hrange hwindow hinc_mono hred_mono
  exact le_trans hclosed (add_le_add_right hIco 1)

/-- Closed shifted correlations inherit the direct all-integer active
resonance decomposition with first-derivative complement gaps. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedCorrelation_norm_le_activeCenterCount_window_add_firstDerivativeGapMajorants_add_one
    (t : ℝ)
    {a b h : ℕ}
    {eta W : ℝ}
    (ha : 1 ≤ a)
    (habh : a ≤ b - h)
    (heta_pos : 0 < eta)
    (heta_pi : eta ≤ Real.pi)
    (hwindow :
      ∀ k : ℤ,
        k ∈
          Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h eta →
          ((Complex.realPhase_integerIncrementResonanceWindow
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h) (2 * Real.pi * (k : ℝ)) eta).card : ℝ) ≤ W)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h))
    (hred_mono :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h)) :
    ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖ ≤
      (((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
        t a b h eta).card : ℝ) * W) +
        ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
          t a b h eta).card + 1 : ℕ) : ℝ) *
          (4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹)) +
        1 := by
  have hclosed :
      ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖ ≤
        ‖∑ n ∈ Finset.Ico a (b - h),
          Complex.exp
            (Complex.I *
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                h n : ℂ))‖ + 1 :=
    Complex.logarithmicPhaseRealPhase_shiftedCorrelation_norm_le_Ico_sum_norm_add_one
      t habh
  have hIco :
      ‖∑ n ∈ Finset.Ico a (b - h),
        Complex.exp
          (Complex.I *
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h n : ℂ))‖ ≤
        (((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
          t a b h eta).card : ℝ) * W) +
          ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h eta).card + 1 : ℕ) : ℝ) *
            (4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹)) :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_activeCenterCount_window_add_firstDerivativeGapMajorants
      t ha habh heta_pos heta_pi hwindow hinc_mono hred_mono
  exact le_trans hclosed (add_le_add_right hIco 1)

/-- Closed shifted correlations inherit the direct all-integer active
resonance decomposition with first-derivative complement gaps. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedCorrelation_norm_le_activeCenterCount_window_add_allIntegerFirstDerivativeGapMajorants_add_one
    (t : ℝ)
    {a b h : ℕ}
    {eta W : ℝ}
    (ha : 1 ≤ a)
    (habh : a ≤ b - h)
    (heta_pos : 0 < eta)
    (heta_pi : eta ≤ Real.pi)
    (hwindow :
      ∀ k : ℤ,
        k ∈
          Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h eta →
          ((Complex.realPhase_integerIncrementResonanceWindow
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h) (2 * Real.pi * (k : ℝ)) eta).card : ℝ) ≤ W)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h))
    (hred_mono :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h)) :
    ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖ ≤
      (((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
        t a b h eta).card : ℝ) * W) +
        ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
          t a b h eta).card + 1 : ℕ) : ℝ) *
          (4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹)) +
        1 := by
  have hclosed :
      ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖ ≤
        ‖∑ n ∈ Finset.Ico a (b - h),
          Complex.exp
            (Complex.I *
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                h n : ℂ))‖ + 1 :=
    Complex.logarithmicPhaseRealPhase_shiftedCorrelation_norm_le_Ico_sum_norm_add_one
      t habh
  have hIco :
      ‖∑ n ∈ Finset.Ico a (b - h),
        Complex.exp
          (Complex.I *
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h n : ℂ))‖ ≤
        (((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
          t a b h eta).card : ℝ) * W) +
          ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h eta).card + 1 : ℕ) : ℝ) *
            (4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹)) :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_activeCenterCount_window_add_allIntegerFirstDerivativeGapMajorants
      t ha habh heta_pos heta_pi hwindow hinc_mono hred_mono
  exact le_trans hclosed (add_le_add_right hIco 1)

/-- Closed shifted correlations inherit the direct all-integer active
resonance decomposition with the resonant family bounded by the ambient
half-open block and complement gaps estimated by first derivative. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedCorrelation_norm_le_blockLength_add_allIntegerFirstDerivativeGapMajorants_add_one
    (t : ℝ)
    {a b h : ℕ}
    {eta : ℝ}
    (ha : 1 ≤ a)
    (habh : a ≤ b - h)
    (heta_pos : 0 < eta)
    (heta_pi : eta ≤ Real.pi)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h))
    (hred_mono :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h)) :
    ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖ ≤
      ((Finset.Ico a (b - h)).card : ℝ) +
        ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
          t a b h eta).card + 1 : ℕ) : ℝ) *
          (4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹)) +
        1 := by
  have hclosed :
      ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖ ≤
        ‖∑ n ∈ Finset.Ico a (b - h),
          Complex.exp
            (Complex.I *
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                h n : ℂ))‖ + 1 :=
    Complex.logarithmicPhaseRealPhase_shiftedCorrelation_norm_le_Ico_sum_norm_add_one
      t habh
  have hunion :
      ‖∑ n ∈
        Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceUnion
          t a b h eta,
        Complex.exp
          (Complex.I *
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h n : ℂ))‖ ≤
        ((Finset.Ico a (b - h)).card : ℝ) :=
    Complex.realPhase_integerIncrementResonanceFamilyUnion_sum_norm_le_block
      (Complex.realPhase_secondDerivative_vdc_shiftedDifference
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        h)
      (Complex.realPhase_secondDerivative_vdc_shiftedDifference
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        h)
      a (b - h) eta
      (Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
        t a b h eta)
  have hgap :
      ‖∑ n ∈
        Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
          t a b h eta,
        Complex.exp
          (Complex.I *
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h n : ℂ))‖ ≤
        ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
          t a b h eta).card + 1 : ℕ) : ℝ) *
          (4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹)) :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_sum_norm_le_activeCenterCount_mul_allIntegerFirstDerivativeMajorant
      t ha habh heta_pos heta_pi hinc_mono hred_mono
  have hIco :
      ‖∑ n ∈ Finset.Ico a (b - h),
        Complex.exp
          (Complex.I *
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h n : ℂ))‖ ≤
        ((Finset.Ico a (b - h)).card : ℝ) +
          ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h eta).card + 1 : ℕ) : ℝ) *
            (4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹)) :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_of_activeResonanceFamily_bounds
      t eta hunion hgap (le_of_eq rfl)
  exact le_trans hclosed (add_le_add_right hIco 1)

/-- Closed shifted correlations inherit the direct all-integer active
resonance decomposition with the resonant family bounded by the ambient
half-open block and complement gaps assigned to principal lattice branches. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedCorrelation_norm_le_blockLength_add_firstDerivativeGapMajorants_add_one_of_principal_gap_cover
    (t : ℝ)
    {a b h : ℕ}
    {eta : ℝ}
    (ha : 1 ≤ a)
    (habh : a ≤ b - h)
    (heta_pos : 0 < eta)
    (heta_pi : eta ≤ Real.pi)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h))
    (hprincipal_cover :
      ∀ gaps : Finset (ℕ × ℕ),
        Complex.realPhase_IcoFamilyUnion gaps =
            Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
              t a b h eta →
          (∀ p₁ : ℕ × ℕ,
            p₁ ∈ gaps →
              ∀ p₂ : ℕ × ℕ,
                p₂ ∈ gaps →
                  p₁ ≠ p₂ →
                    Disjoint (Finset.Ico p₁.1 p₁.2)
                      (Finset.Ico p₂.1 p₂.2)) →
            Complex.realPhase_IcoFamilyBounded a (b - h) gaps →
              ∃ center : ℕ × ℕ → ℤ,
                ∀ p : ℕ × ℕ,
                  p ∈ gaps →
                    ∀ n : ℕ,
                      n ∈ Finset.Ico p.1 p.2 →
                        Complex.realPhase_integerIncrement
                            (Complex.realPhase_integerLatticeShift
                              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                                h)
                              (center p))
                            n ∈
                          Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi))) :
    ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖ ≤
      ((Finset.Ico a (b - h)).card : ℝ) +
        ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
          t a b h eta).card + 1 : ℕ) : ℝ) *
          (4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹)) +
        1 := by
  have hclosed :
      ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖ ≤
        ‖∑ n ∈ Finset.Ico a (b - h),
          Complex.exp
            (Complex.I *
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                h n : ℂ))‖ + 1 :=
    Complex.logarithmicPhaseRealPhase_shiftedCorrelation_norm_le_Ico_sum_norm_add_one
      t habh
  have hunion :
      ‖∑ n ∈
        Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceUnion
          t a b h eta,
        Complex.exp
          (Complex.I *
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h n : ℂ))‖ ≤
        ((Finset.Ico a (b - h)).card : ℝ) :=
    Complex.realPhase_integerIncrementResonanceFamilyUnion_sum_norm_le_block
      (Complex.realPhase_secondDerivative_vdc_shiftedDifference
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        h)
      (Complex.realPhase_secondDerivative_vdc_shiftedDifference
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        h)
      a (b - h) eta
      (Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
        t a b h eta)
  have hgap :
      ‖∑ n ∈
        Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
          t a b h eta,
        Complex.exp
          (Complex.I *
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h n : ℂ))‖ ≤
        ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
          t a b h eta).card + 1 : ℕ) : ℝ) *
          (4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹)) :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_sum_norm_le_activeCenterCount_mul_firstDerivativeMajorant_of_principal_gap_cover
      t ha habh heta_pos heta_pi hinc_mono hprincipal_cover
  have hIco :
      ‖∑ n ∈ Finset.Ico a (b - h),
        Complex.exp
          (Complex.I *
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h n : ℂ))‖ ≤
        ((Finset.Ico a (b - h)).card : ℝ) +
          ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h eta).card + 1 : ℕ) : ℝ) *
            (4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹)) :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_of_activeResonanceFamily_bounds
      t eta hunion hgap (le_of_eq rfl)
  exact le_trans hclosed (add_le_add_right hIco 1)

/-- Shifted-correlation envelope bound using the direct all-integer
active-center gap count at an arbitrary resonance thickness. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedCorrelationEnvelope_le_activeCenterCount_window_add_firstDerivativeGapMajorants_add_one
    (t : ℝ)
    {a b H : ℕ}
    {eta W : ℕ → ℝ}
    (ha : 1 ≤ a)
    (habh :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          a ≤ b - h)
    (heta_pos :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          0 < eta h)
    (heta_pi :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          eta h ≤ Real.pi)
    (hwindow :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ∀ k : ℤ,
            k ∈
              Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
                t a b h (eta h) →
              ((Complex.realPhase_integerIncrementResonanceWindow
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                a (b - h) (2 * Real.pi * (k : ℝ)) (eta h)).card :
                  ℝ) ≤ W h)
    (hinc_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          Complex.realPhase_integerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h))
    (hred_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          Complex.realPhase_reducedIntegerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h)) :
    Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b H ≤
      ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        (((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
          t a b h (eta h)).card : ℝ) * W h) +
          ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h (eta h)).card + 1 : ℕ) : ℝ) *
            (4 * ((eta h)⁻¹ + 1) + 4 * Real.pi * (eta h)⁻¹))) +
          1) := by
  show
    (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
      ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖) ≤
      ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        (((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
          t a b h (eta h)).card : ℝ) * W h) +
          ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h (eta h)).card + 1 : ℕ) : ℝ) *
            (4 * ((eta h)⁻¹ + 1) + 4 * Real.pi * (eta h)⁻¹))) +
          1)
  exact Finset.sum_le_sum
    (fun h hh =>
      Complex.logarithmicPhaseRealPhase_shiftedCorrelation_norm_le_activeCenterCount_window_add_firstDerivativeGapMajorants_add_one
        t ha (habh h hh) (heta_pos h hh) (heta_pi h hh)
        (hwindow h hh) (hinc_mono h hh) (hred_mono h hh))

/-- Shifted-correlation envelope bound using the direct all-integer
active-center gap count and the all-integer monotone Kusmin-Landau primitive. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedCorrelationEnvelope_le_activeCenterCount_window_add_allIntegerFirstDerivativeGapMajorants_add_one
    (t : ℝ)
    {a b H : ℕ}
    {eta W : ℕ → ℝ}
    (ha : 1 ≤ a)
    (habh :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          a ≤ b - h)
    (heta_pos :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          0 < eta h)
    (heta_pi :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          eta h ≤ Real.pi)
    (hwindow :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ∀ k : ℤ,
            k ∈
              Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
                t a b h (eta h) →
              ((Complex.realPhase_integerIncrementResonanceWindow
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                a (b - h) (2 * Real.pi * (k : ℝ)) (eta h)).card :
                  ℝ) ≤ W h)
    (hinc_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          Complex.realPhase_integerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h))
    (hred_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          Complex.realPhase_reducedIntegerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h)) :
    Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b H ≤
      ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        (((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
          t a b h (eta h)).card : ℝ) * W h) +
          ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h (eta h)).card + 1 : ℕ) : ℝ) *
            (4 * ((eta h)⁻¹ + 1) + 4 * Real.pi * (eta h)⁻¹))) +
          1) := by
  show
    (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
      ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖) ≤
      ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        (((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
          t a b h (eta h)).card : ℝ) * W h) +
          ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h (eta h)).card + 1 : ℕ) : ℝ) *
            (4 * ((eta h)⁻¹ + 1) + 4 * Real.pi * (eta h)⁻¹))) +
          1)
  exact Finset.sum_le_sum
    (fun h hh =>
      Complex.logarithmicPhaseRealPhase_shiftedCorrelation_norm_le_activeCenterCount_window_add_allIntegerFirstDerivativeGapMajorants_add_one
        t ha (habh h hh) (heta_pos h hh) (heta_pi h hh)
        (hwindow h hh) (hinc_mono h hh))

/-- A numerical cardinal budget for each active-center family converts the
direct first-derivative all-integer envelope into a counted majorant. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedCorrelationEnvelope_le_counted_activeCenter_window_add_firstDerivativeGapMajorants_add_one
    (t : ℝ)
    {a b H : ℕ}
    {eta W : ℕ → ℝ}
    (C : ℕ → ℕ)
    (ha : 1 ≤ a)
    (habh :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          a ≤ b - h)
    (heta_pos :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          0 < eta h)
    (heta_pi :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          eta h ≤ Real.pi)
    (hwindow :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ∀ k : ℤ,
            k ∈
              Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
                t a b h (eta h) →
              ((Complex.realPhase_integerIncrementResonanceWindow
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                a (b - h) (2 * Real.pi * (k : ℝ)) (eta h)).card :
                  ℝ) ≤ W h)
    (hcard :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          (Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h (eta h)).card ≤ C h)
    (hW_nonneg :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          0 ≤ W h)
    (hinc_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          Complex.realPhase_integerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h))
    (hred_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          Complex.realPhase_reducedIntegerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h)) :
    Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b H ≤
      ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        ((((C h : ℕ) : ℝ) * W h +
          (((C h + 1 : ℕ) : ℝ) *
            (4 * ((eta h)⁻¹ + 1) + 4 * Real.pi * (eta h)⁻¹))) +
          1) := by
  have hraw :
      Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b H ≤
        ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
          (((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h (eta h)).card : ℝ) * W h) +
            ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h (eta h)).card + 1 : ℕ) : ℝ) *
              (4 * ((eta h)⁻¹ + 1) + 4 * Real.pi * (eta h)⁻¹))) +
            1) :=
    Complex.logarithmicPhaseRealPhase_shiftedCorrelationEnvelope_le_activeCenterCount_window_add_firstDerivativeGapMajorants_add_one
      t ha habh heta_pos heta_pi hwindow hinc_mono hred_mono
  have hsum :
      (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
          (((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h (eta h)).card : ℝ) * W h) +
            ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h (eta h)).card + 1 : ℕ) : ℝ) *
              (4 * ((eta h)⁻¹ + 1) + 4 * Real.pi * (eta h)⁻¹))) +
            1)) ≤
        ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
          ((((C h : ℕ) : ℝ) * W h +
            (((C h + 1 : ℕ) : ℝ) *
              (4 * ((eta h)⁻¹ + 1) + 4 * Real.pi * (eta h)⁻¹))) +
            1) := by
    exact Finset.sum_le_sum
      (fun h hh =>
        have hcard_real :
            ((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h (eta h)).card : ℝ) ≤ ((C h : ℕ) : ℝ) :=
          Nat.cast_le.mpr (hcard h hh)
        have hleft :
            (((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h (eta h)).card : ℝ) * W h) ≤
              ((C h : ℕ) : ℝ) * W h :=
          mul_le_mul_of_nonneg_right hcard_real (hW_nonneg h hh)
        have hcard_succ :
            (Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h (eta h)).card + 1 ≤ C h + 1 :=
          Nat.succ_le_succ (hcard h hh)
        have hcard_succ_real :
            (((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h (eta h)).card + 1 : ℕ) : ℝ) ≤
              ((C h + 1 : ℕ) : ℝ) :=
          Nat.cast_le.mpr hcard_succ
        have hmajorant_nonneg :
            0 ≤ 4 * ((eta h)⁻¹ + 1) + 4 * Real.pi * (eta h)⁻¹ := by
          have heta_inv_nonneg : 0 ≤ (eta h)⁻¹ :=
            inv_nonneg.mpr (le_of_lt (heta_pos h hh))
          have hinner_nonneg : 0 ≤ (eta h)⁻¹ + 1 :=
            add_nonneg heta_inv_nonneg zero_le_one
          have hleft_nonneg : 0 ≤ 4 * ((eta h)⁻¹ + 1) :=
            mul_nonneg zero_le_four hinner_nonneg
          have hfour_pi_nonneg : 0 ≤ 4 * Real.pi :=
            mul_nonneg zero_le_four Real.pi_nonneg
          have hright_nonneg : 0 ≤ 4 * Real.pi * (eta h)⁻¹ :=
            mul_nonneg hfour_pi_nonneg heta_inv_nonneg
          exact add_nonneg hleft_nonneg hright_nonneg
        have hright :
            ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h (eta h)).card + 1 : ℕ) : ℝ) *
                (4 * ((eta h)⁻¹ + 1) + 4 * Real.pi * (eta h)⁻¹)) ≤
              (((C h + 1 : ℕ) : ℝ) *
                (4 * ((eta h)⁻¹ + 1) + 4 * Real.pi * (eta h)⁻¹)) :=
          mul_le_mul_of_nonneg_right hcard_succ_real hmajorant_nonneg
        add_le_add_right (add_le_add hleft hright) 1)
  exact le_trans hraw hsum

/-- A numerical cardinal budget for each active-center family converts the
direct all-integer first-derivative envelope into a counted majorant. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedCorrelationEnvelope_le_counted_activeCenter_window_add_allIntegerFirstDerivativeGapMajorants_add_one
    (t : ℝ)
    {a b H : ℕ}
    {eta W : ℕ → ℝ}
    (C : ℕ → ℕ)
    (ha : 1 ≤ a)
    (habh :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          a ≤ b - h)
    (heta_pos :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          0 < eta h)
    (heta_pi :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          eta h ≤ Real.pi)
    (hwindow :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ∀ k : ℤ,
            k ∈
              Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
                t a b h (eta h) →
              ((Complex.realPhase_integerIncrementResonanceWindow
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                a (b - h) (2 * Real.pi * (k : ℝ)) (eta h)).card :
                  ℝ) ≤ W h)
    (hcard :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          (Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h (eta h)).card ≤ C h)
    (hW_nonneg :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          0 ≤ W h)
    (hinc_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          Complex.realPhase_integerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h))
    (hred_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          Complex.realPhase_reducedIntegerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h)) :
    Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b H ≤
      ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        ((((C h : ℕ) : ℝ) * W h +
          (((C h + 1 : ℕ) : ℝ) *
            (4 * ((eta h)⁻¹ + 1) + 4 * Real.pi * (eta h)⁻¹))) +
          1) := by
  have hraw :
      Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b H ≤
        ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
          (((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h (eta h)).card : ℝ) * W h) +
            ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h (eta h)).card + 1 : ℕ) : ℝ) *
              (4 * ((eta h)⁻¹ + 1) + 4 * Real.pi * (eta h)⁻¹))) +
            1) :=
    Complex.logarithmicPhaseRealPhase_shiftedCorrelationEnvelope_le_activeCenterCount_window_add_allIntegerFirstDerivativeGapMajorants_add_one
      t ha habh heta_pos heta_pi hwindow hinc_mono hred_mono
  have hsum :
      (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
          (((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h (eta h)).card : ℝ) * W h) +
            ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h (eta h)).card + 1 : ℕ) : ℝ) *
              (4 * ((eta h)⁻¹ + 1) + 4 * Real.pi * (eta h)⁻¹))) +
            1)) ≤
        ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
          ((((C h : ℕ) : ℝ) * W h +
            (((C h + 1 : ℕ) : ℝ) *
              (4 * ((eta h)⁻¹ + 1) + 4 * Real.pi * (eta h)⁻¹))) +
            1) := by
    exact Finset.sum_le_sum
      (fun h hh =>
        have hcard_real :
            ((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h (eta h)).card : ℝ) ≤ ((C h : ℕ) : ℝ) :=
          Nat.cast_le.mpr (hcard h hh)
        have hleft :
            (((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h (eta h)).card : ℝ) * W h) ≤
              ((C h : ℕ) : ℝ) * W h :=
          mul_le_mul_of_nonneg_right hcard_real (hW_nonneg h hh)
        have hcard_succ :
            (Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h (eta h)).card + 1 ≤ C h + 1 :=
          Nat.succ_le_succ (hcard h hh)
        have hcard_succ_real :
            (((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h (eta h)).card + 1 : ℕ) : ℝ) ≤
              ((C h + 1 : ℕ) : ℝ) :=
          Nat.cast_le.mpr hcard_succ
        have hmajorant_nonneg :
            0 ≤ 4 * ((eta h)⁻¹ + 1) + 4 * Real.pi * (eta h)⁻¹ := by
          have heta_inv_nonneg : 0 ≤ (eta h)⁻¹ :=
            inv_nonneg.mpr (le_of_lt (heta_pos h hh))
          have hinner_nonneg : 0 ≤ (eta h)⁻¹ + 1 :=
            add_nonneg heta_inv_nonneg zero_le_one
          have hleft_nonneg : 0 ≤ 4 * ((eta h)⁻¹ + 1) :=
            mul_nonneg zero_le_four hinner_nonneg
          have hfour_pi_nonneg : 0 ≤ 4 * Real.pi :=
            mul_nonneg zero_le_four Real.pi_nonneg
          have hright_nonneg : 0 ≤ 4 * Real.pi * (eta h)⁻¹ :=
            mul_nonneg hfour_pi_nonneg heta_inv_nonneg
          exact add_nonneg hleft_nonneg hright_nonneg
        have hright :
            ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h (eta h)).card + 1 : ℕ) : ℝ) *
                (4 * ((eta h)⁻¹ + 1) + 4 * Real.pi * (eta h)⁻¹)) ≤
              (((C h + 1 : ℕ) : ℝ) *
                (4 * ((eta h)⁻¹ + 1) + 4 * Real.pi * (eta h)⁻¹)) :=
          mul_le_mul_of_nonneg_right hcard_succ_real hmajorant_nonneg
        add_le_add_right (add_le_add hleft hright) 1)
  exact le_trans hraw hsum

/-- Explicit increment ranges supply the active-center count in the direct
first-derivative all-integer active resonance envelope. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedCorrelationEnvelope_le_rangeCounted_activeCenter_window_add_firstDerivativeGapMajorants_add_one
    (t : ℝ)
    {a b H : ℕ}
    {eta W lo hi : ℕ → ℝ}
    (ha : 1 ≤ a)
    (habh :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          a ≤ b - h)
    (heta_pos :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          0 < eta h)
    (heta_pi :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          eta h ≤ Real.pi)
    (hrange :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ∀ n : ℕ,
            n ∈ Finset.Ico a (b - h) →
              lo h ≤
                  Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    n ∧
                Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    n ≤ hi h)
    (hwindow :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ∀ k : ℤ,
            k ∈
              Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
                t a b h (eta h) →
              ((Complex.realPhase_integerIncrementResonanceWindow
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                a (b - h) (2 * Real.pi * (k : ℝ)) (eta h)).card :
                  ℝ) ≤ W h)
    (hW_nonneg :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          0 ≤ W h)
    (hinc_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          Complex.realPhase_integerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h))
    (hred_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          Complex.realPhase_reducedIntegerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h)) :
    Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b H ≤
      ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        (((Complex.realPhase_integerIncrementRangeActiveCenters
            (lo h) (hi h) (eta h)).card : ℝ) * W h +
          (((Complex.realPhase_integerIncrementRangeActiveCenters
              (lo h) (hi h) (eta h)).card + 1 : ℕ) : ℝ) *
            (4 * ((eta h)⁻¹ + 1) + 4 * Real.pi * (eta h)⁻¹) +
          1) := by
  let C : ℕ → ℕ :=
    fun h : ℕ =>
      (Complex.realPhase_integerIncrementRangeActiveCenters
        (lo h) (hi h) (eta h)).card
  have hcard :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          (Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h (eta h)).card ≤ C h := by
    intro h hh
    exact
      Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters_card_le_rangeActiveCenters_card
        t (hrange h hh)
  exact
    Complex.logarithmicPhaseRealPhase_shiftedCorrelationEnvelope_le_counted_activeCenter_window_add_firstDerivativeGapMajorants_add_one
      t C ha habh heta_pos heta_pi hwindow hcard hW_nonneg
      hinc_mono hred_mono

/-- Explicit increment ranges supply the active-center count in the direct
all-integer first-derivative active resonance envelope.

This is the owner-level all-integer Kusmin-Landau gap sink: raw shifted
increments are monotone, reduced increments are monotone on the complement
gaps, all integer-centered resonance tubes are removed, and the complement is
controlled by the active-center gap count. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedCorrelationEnvelope_le_rangeCounted_activeCenter_window_add_allIntegerFirstDerivativeGapMajorants_add_one
    (t : ℝ)
    {a b H : ℕ}
    {eta W lo hi : ℕ → ℝ}
    (ha : 1 ≤ a)
    (habh :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          a ≤ b - h)
    (heta_pos :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          0 < eta h)
    (heta_pi :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          eta h ≤ Real.pi)
    (hrange :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ∀ n : ℕ,
            n ∈ Finset.Ico a (b - h) →
              lo h ≤
                  Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    n ∧
                Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    n ≤ hi h)
    (hwindow :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ∀ k : ℤ,
            k ∈
              Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
                t a b h (eta h) →
              ((Complex.realPhase_integerIncrementResonanceWindow
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                a (b - h) (2 * Real.pi * (k : ℝ)) (eta h)).card :
                  ℝ) ≤ W h)
    (hW_nonneg :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          0 ≤ W h)
    (hinc_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          Complex.realPhase_integerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h))
    (hred_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          Complex.realPhase_reducedIntegerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h)) :
    Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b H ≤
      ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        (((Complex.realPhase_integerIncrementRangeActiveCenters
            (lo h) (hi h) (eta h)).card : ℝ) * W h +
          (((Complex.realPhase_integerIncrementRangeActiveCenters
              (lo h) (hi h) (eta h)).card + 1 : ℕ) : ℝ) *
            (4 * ((eta h)⁻¹ + 1) + 4 * Real.pi * (eta h)⁻¹) +
          1) := by
  let C : ℕ → ℕ :=
    fun h : ℕ =>
      (Complex.realPhase_integerIncrementRangeActiveCenters
        (lo h) (hi h) (eta h)).card
  have hcard :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          (Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h (eta h)).card ≤ C h := by
    intro h hh
    exact
      Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters_card_le_rangeActiveCenters_card
        t (hrange h hh)
  exact
    Complex.logarithmicPhaseRealPhase_shiftedCorrelationEnvelope_le_counted_activeCenter_window_add_allIntegerFirstDerivativeGapMajorants_add_one
      t C ha habh heta_pos heta_pi hwindow hcard hW_nonneg
      hinc_mono hred_mono

/-- The shifted-correlation envelope is controlled by the all-integer active
resonance decomposition with first-derivative complement gaps on each Weyl
shift. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedCorrelationEnvelope_le_activeCenterCount_window_add_refinedPrincipalFirstDerivativeGapMajorants_add_one
    (t : ℝ)
    {a b H : ℕ}
    {eta W lo hi : ℕ → ℝ}
    (ha : 1 ≤ a)
    (habh :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          a ≤ b - h)
    (heta_pos :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          0 < eta h)
    (heta_pi :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          eta h ≤ Real.pi)
    (hrange :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ∀ n : ℕ,
            n ∈ Finset.Ico a (b - h) →
              lo h ≤
                  Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    n ∧
                Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    n ≤ hi h)
    (hwindow :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ∀ k : ℤ,
            k ∈
              Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
                t a b h (eta h) →
              ((Complex.realPhase_integerIncrementResonanceWindow
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                a (b - h) (2 * Real.pi * (k : ℝ)) (eta h)).card :
                  ℝ) ≤ W h)
    (hinc_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          Complex.realPhase_integerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h)) :
    Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b H ≤
      ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        (((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
          t a b h (eta h)).card : ℝ) * W h) +
          (((Finset.Ico a (b - h)).card : ℝ) *
            (4 * ((eta h)⁻¹ + 1) + 4 * Real.pi * (eta h)⁻¹))) +
          1) := by
  show
    (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
      ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖) ≤
      ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        (((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
          t a b h (eta h)).card : ℝ) * W h) +
          (((Finset.Ico a (b - h)).card : ℝ) *
            (4 * ((eta h)⁻¹ + 1) + 4 * Real.pi * (eta h)⁻¹))) +
          1)
  exact Finset.sum_le_sum
    (fun h hh =>
      Complex.logarithmicPhaseRealPhase_shiftedCorrelation_norm_le_activeCenterCount_window_add_refinedPrincipalFirstDerivativeGapMajorants_add_one
        t ha (habh h hh) (heta_pos h hh) (heta_pi h hh)
        (hrange h hh) (hwindow h hh) (hinc_mono h hh))

/-- A numerical cardinal budget for each active-center family converts the
first-derivative refined all-principal-branch envelope into a counted
majorant. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedCorrelationEnvelope_le_counted_activeCenter_window_add_refinedPrincipalFirstDerivativeGapMajorants_add_one
    (t : ℝ)
    {a b H : ℕ}
    {eta W lo hi : ℕ → ℝ}
    (C : ℕ → ℕ)
    (ha : 1 ≤ a)
    (habh :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          a ≤ b - h)
    (heta_pos :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          0 < eta h)
    (heta_pi :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          eta h ≤ Real.pi)
    (hrange :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ∀ n : ℕ,
            n ∈ Finset.Ico a (b - h) →
              lo h ≤
                  Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    n ∧
                Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    n ≤ hi h)
    (hwindow :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ∀ k : ℤ,
            k ∈
              Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
                t a b h (eta h) →
              ((Complex.realPhase_integerIncrementResonanceWindow
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                a (b - h) (2 * Real.pi * (k : ℝ)) (eta h)).card :
                  ℝ) ≤ W h)
    (hcard :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          (Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h (eta h)).card ≤ C h)
    (hW_nonneg :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          0 ≤ W h)
    (hinc_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          Complex.realPhase_integerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h)) :
    Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b H ≤
      ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        ((((C h : ℕ) : ℝ) * W h +
          (((Finset.Ico a (b - h)).card : ℝ) *
            (4 * ((eta h)⁻¹ + 1) + 4 * Real.pi * (eta h)⁻¹))) +
          1) := by
  have hraw :
      Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b H ≤
        ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
          (((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h (eta h)).card : ℝ) * W h) +
            (((Finset.Ico a (b - h)).card : ℝ) *
              (4 * ((eta h)⁻¹ + 1) + 4 * Real.pi * (eta h)⁻¹))) +
            1) :=
    Complex.logarithmicPhaseRealPhase_shiftedCorrelationEnvelope_le_activeCenterCount_window_add_refinedPrincipalFirstDerivativeGapMajorants_add_one
      t ha habh heta_pos heta_pi hrange hwindow hinc_mono
  have hsum :
      (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
          (((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h (eta h)).card : ℝ) * W h) +
            (((Finset.Ico a (b - h)).card : ℝ) *
              (4 * ((eta h)⁻¹ + 1) + 4 * Real.pi * (eta h)⁻¹))) +
            1)) ≤
        ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
          ((((C h : ℕ) : ℝ) * W h +
            (((Finset.Ico a (b - h)).card : ℝ) *
              (4 * ((eta h)⁻¹ + 1) + 4 * Real.pi * (eta h)⁻¹))) +
            1) := by
    exact Finset.sum_le_sum
      (fun h hh =>
        have hcard_real :
            ((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h (eta h)).card : ℝ) ≤ ((C h : ℕ) : ℝ) :=
          Nat.cast_le.mpr (hcard h hh)
        have hleft :
            (((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h (eta h)).card : ℝ) * W h) ≤
              ((C h : ℕ) : ℝ) * W h :=
          mul_le_mul_of_nonneg_right hcard_real (hW_nonneg h hh)
        have hright :
            ((Finset.Ico a (b - h)).card : ℝ) *
                (4 * ((eta h)⁻¹ + 1) + 4 * Real.pi * (eta h)⁻¹) ≤
              ((Finset.Ico a (b - h)).card : ℝ) *
                (4 * ((eta h)⁻¹ + 1) + 4 * Real.pi * (eta h)⁻¹) :=
          le_refl _
        add_le_add_right (add_le_add hleft hright) 1)
  exact le_trans hraw hsum

/-- Counted all-integer active resonance control with first-derivative
principal-branch gaps supplies the positive long Weyl target once the
corresponding explicit radicand is below the target square. -/
theorem Complex.logarithmicPhaseRealPhase_long_bound_of_counted_activeCenter_window_refinedPrincipalFirstDerivative_radicand
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    {eta W lo hi : ℕ → ℝ}
    (C : ℕ → ℕ)
    (habh :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          a ≤ b - h)
    (heta_pos :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          0 < eta h)
    (heta_pi :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          eta h ≤ Real.pi)
    (hrange :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ n : ℕ,
            n ∈ Finset.Ico a (b - h) →
              lo h ≤
                  Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    n ∧
                Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    n ≤ hi h)
    (hwindow :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ k : ℤ,
            k ∈
              Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
                t a b h (eta h) →
              ((Complex.realPhase_integerIncrementResonanceWindow
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                a (b - h) (2 * Real.pi * (k : ℝ)) (eta h)).card :
                  ℝ) ≤ W h)
    (hcard :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          (Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h (eta h)).card ≤ C h)
    (hW_nonneg :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          0 ≤ W h)
    (hinc_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          Complex.realPhase_integerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h))
    (hrad :
      ((Real.secondDerivativeVdc_blockLength a b) +
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ)) *
          (((Real.secondDerivativeVdc_blockLength a b) +
              2 *
                (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                  (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
                  ((((C h : ℕ) : ℝ) * W h +
                    (((Finset.Ico a (b - h)).card : ℝ) *
                      (4 * ((eta h)⁻¹ + 1) +
                        4 * Real.pi * (eta h)⁻¹))) +
                    1))) *
            (((Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℕ) : ℝ)⁻¹)) ≤
        (80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖) +
          Real.sqrt (1 + ‖t‖))) ^ 2) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  have henvelope :
      Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b (Real.secondDerivativeVdc_weylShiftLength ‖t‖) ≤
        ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
          ((((C h : ℕ) : ℝ) * W h +
            (((Finset.Ico a (b - h)).card : ℝ) *
              (4 * ((eta h)⁻¹ + 1) +
                4 * Real.pi * (eta h)⁻¹))) +
            1) :=
    Complex.logarithmicPhaseRealPhase_shiftedCorrelationEnvelope_le_counted_activeCenter_window_add_refinedPrincipalFirstDerivativeGapMajorants_add_one
      t C ha habh heta_pos heta_pi hrange hwindow hcard hW_nonneg
      hinc_mono
  exact
    Complex.logarithmicPhaseRealPhase_long_bound_of_weylEnvelope_radicand_target_of_shiftedCorrelationEnvelope_bound
      t ht hab hlong_sqrt henvelope hrad

/-- Explicit increment ranges supply the active-center count in the
first-derivative all-principal-branch long Weyl radicand. -/
theorem Complex.logarithmicPhaseRealPhase_long_bound_of_rangeCounted_activeCenter_window_refinedPrincipalFirstDerivative_radicand
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    {eta W lo hi : ℕ → ℝ}
    (habh :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          a ≤ b - h)
    (heta_pos :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          0 < eta h)
    (heta_pi :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          eta h ≤ Real.pi)
    (hrange :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ n : ℕ,
            n ∈ Finset.Ico a (b - h) →
              lo h ≤
                  Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    n ∧
                Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    n ≤ hi h)
    (hwindow :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ k : ℤ,
            k ∈
              Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
                t a b h (eta h) →
              ((Complex.realPhase_integerIncrementResonanceWindow
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                a (b - h) (2 * Real.pi * (k : ℝ)) (eta h)).card :
                  ℝ) ≤ W h)
    (hW_nonneg :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          0 ≤ W h)
    (hinc_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          Complex.realPhase_integerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h))
    (hrad :
      ((Real.secondDerivativeVdc_blockLength a b) +
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ)) *
          (((Real.secondDerivativeVdc_blockLength a b) +
              2 *
                (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                  (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
                  ((((((Complex.realPhase_integerIncrementRangeActiveCenters
                      (lo h) (hi h) (eta h)).card : ℕ) : ℝ) * W h +
                    (((Finset.Ico a (b - h)).card : ℝ) *
                      (4 * ((eta h)⁻¹ + 1) +
                        4 * Real.pi * (eta h)⁻¹))) +
                    1))) *
            (((Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℕ) : ℝ)⁻¹)) ≤
        (80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖))) ^ 2) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  let C : ℕ → ℕ :=
    fun h : ℕ =>
      (Complex.realPhase_integerIncrementRangeActiveCenters
        (lo h) (hi h) (eta h)).card
  have hcard :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          (Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h (eta h)).card ≤ C h := by
    intro h hh
    exact
      Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters_card_le_rangeActiveCenters_card
        t (hrange h hh)
  exact
    Complex.logarithmicPhaseRealPhase_long_bound_of_counted_activeCenter_window_refinedPrincipalFirstDerivative_radicand
      t ht ha hab hlong_sqrt C habh heta_pos heta_pi hrange hwindow
      hcard hW_nonneg hinc_mono hrad

/-- The shifted-correlation envelope is controlled by the all-integer active
resonance decomposition on each Weyl shift. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedCorrelationEnvelope_le_activeCenterCount_window_add_gapMajorants_add_one
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b H : ℕ}
    {lam W : ℕ → ℝ}
    (ha : 1 ≤ a)
    (habh :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          a ≤ b - h)
    (hpos :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          1 ≤ h)
    (hlam :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          lam h =
            ‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (h : ℝ))
    (hlam_pi :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          lam h ≤ Real.pi)
    (hwindow :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ∀ k : ℤ,
            k ∈
              Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
                t a b h (lam h) →
              ((Complex.realPhase_integerIncrementResonanceWindow
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                a (b - h) (2 * Real.pi * (k : ℝ)) (lam h)).card :
                  ℝ) ≤ W h)
    (hderiv_antitone :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          AntitoneOn
            (fun x : ℝ =>
              ‖deriv
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                h) x‖)
            (Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)))
    (hderiv_lower :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ∀ x : ℝ,
            x ∈ Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ) →
              ‖t‖ *
                  ((((b + 1 : ℕ) : ℝ) *
                    (((b + 1 : ℕ) : ℝ)))⁻¹) *
                  (h : ℝ) ≤
                ‖deriv
                  (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                    h) x‖)
    (hinc_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          Complex.realPhase_integerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h))
    (hred_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          Complex.realPhase_reducedIntegerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h)) :
    Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b H ≤
      ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        (((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
          t a b h (lam h)).card : ℝ) * W h) +
          ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h (lam h)).card + 1 : ℕ) : ℝ) *
            Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h)) +
          1) := by
  show
    (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
      ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖) ≤
      ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        (((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
          t a b h (lam h)).card : ℝ) * W h) +
          ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h (lam h)).card + 1 : ℕ) : ℝ) *
            Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h)) +
          1)
  exact Finset.sum_le_sum
    (fun h hh =>
      Complex.logarithmicPhaseRealPhase_shiftedCorrelation_norm_le_activeCenterCount_window_add_gapMajorants_add_one
        t ht ha (habh h hh) (hpos h hh) (hlam h hh) (hlam_pi h hh)
        (hwindow h hh) (hderiv_antitone h hh) (hderiv_lower h hh)
        (hinc_mono h hh) (hred_mono h hh))

/-- The shifted-correlation envelope is controlled by the refined
all-principal-branch active resonance decomposition on each Weyl shift. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedCorrelationEnvelope_le_activeCenterCount_window_add_refinedPrincipalGapMajorants_add_one
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b H : ℕ}
    {lam W lo hi : ℕ → ℝ}
    (ha : 1 ≤ a)
    (habh :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          a ≤ b - h)
    (hpos :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          1 ≤ h)
    (hlam :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          lam h =
            ‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (h : ℝ))
    (hlam_pi :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          lam h ≤ Real.pi)
    (hrange :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ∀ n : ℕ,
            n ∈ Finset.Ico a (b - h) →
              lo h ≤
                  Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    n ∧
                Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    n ≤ hi h)
    (hwindow :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ∀ k : ℤ,
            k ∈
              Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
                t a b h (lam h) →
              ((Complex.realPhase_integerIncrementResonanceWindow
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                a (b - h) (2 * Real.pi * (k : ℝ)) (lam h)).card :
                  ℝ) ≤ W h)
    (hinc_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          Complex.realPhase_integerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h)) :
    Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b H ≤
      ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        (((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
          t a b h (lam h)).card : ℝ) * W h) +
          (((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h (lam h)).card + 1 : ℕ) *
              (Complex.realPhase_integerIncrementRangeActiveCenters
                (lo h) (hi h) Real.pi).card : ℕ) : ℝ) *
            Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h)) +
          1) := by
  show
    (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
      ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖) ≤
      ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        (((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
          t a b h (lam h)).card : ℝ) * W h) +
          (((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h (lam h)).card + 1 : ℕ) *
              (Complex.realPhase_integerIncrementRangeActiveCenters
                (lo h) (hi h) Real.pi).card : ℕ) : ℝ) *
            Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h)) +
          1)
  exact Finset.sum_le_sum
    (fun h hh =>
      Complex.logarithmicPhaseRealPhase_shiftedCorrelation_norm_le_activeCenterCount_window_add_refinedPrincipalGapMajorants_add_one
        t ht ha (habh h hh) (hpos h hh) (hlam h hh) (hlam_pi h hh)
        (hrange h hh) (hwindow h hh) (hinc_mono h hh))

/-- A numerical cardinal budget for each active-center family converts the
active decomposition envelope into a counted majorant. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedCorrelationEnvelope_le_counted_activeCenter_window_add_gapMajorants_add_one
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b H : ℕ}
    {lam W : ℕ → ℝ}
    (C : ℕ → ℕ)
    (ha : 1 ≤ a)
    (habh :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          a ≤ b - h)
    (hpos :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          1 ≤ h)
    (hlam :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          lam h =
            ‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (h : ℝ))
    (hlam_pi :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          lam h ≤ Real.pi)
    (hwindow :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ∀ k : ℤ,
            k ∈
              Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
                t a b h (lam h) →
              ((Complex.realPhase_integerIncrementResonanceWindow
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                a (b - h) (2 * Real.pi * (k : ℝ)) (lam h)).card :
                  ℝ) ≤ W h)
    (hcard :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          (Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h (lam h)).card ≤ C h)
    (hW_nonneg :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          0 ≤ W h)
    (hderiv_antitone :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          AntitoneOn
            (fun x : ℝ =>
              ‖deriv
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                h) x‖)
            (Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)))
    (hderiv_lower :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ∀ x : ℝ,
            x ∈ Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ) →
              ‖t‖ *
                  ((((b + 1 : ℕ) : ℝ) *
                    (((b + 1 : ℕ) : ℝ)))⁻¹) *
                  (h : ℝ) ≤
                ‖deriv
                  (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                    h) x‖)
    (hinc_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          Complex.realPhase_integerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h))
    (hred_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          Complex.realPhase_reducedIntegerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h)) :
    Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b H ≤
      ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        ((((C h : ℕ) : ℝ) * W h +
          (((C h + 1 : ℕ) : ℝ) *
            Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h)) +
          1) := by
  have hraw :
      Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b H ≤
        ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
          (((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h (lam h)).card : ℝ) * W h) +
            ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h (lam h)).card + 1 : ℕ) : ℝ) *
              Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h)) +
            1) :=
    Complex.logarithmicPhaseRealPhase_shiftedCorrelationEnvelope_le_activeCenterCount_window_add_gapMajorants_add_one
      t ht ha habh hpos hlam hlam_pi hwindow
      hderiv_antitone hderiv_lower hinc_mono hred_mono
  have hsum :
      (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
          (((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h (lam h)).card : ℝ) * W h) +
            ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h (lam h)).card + 1 : ℕ) : ℝ) *
              Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h)) +
            1)) ≤
        ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
          (((C h : ℕ) : ℝ) * W h +
            (((C h + 1 : ℕ) : ℝ) *
              Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) +
            1)) := by
    exact Finset.sum_le_sum
      (fun h hh =>
        have hcard_real :
            ((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h (lam h)).card : ℝ) ≤ ((C h : ℕ) : ℝ) :=
          Nat.cast_le.mpr (hcard h hh)
        have hleft :
            (((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h (lam h)).card : ℝ) * W h) ≤
              ((C h : ℕ) : ℝ) * W h :=
          mul_le_mul_of_nonneg_right hcard_real (hW_nonneg h hh)
        have hcard_succ :
            (Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h (lam h)).card + 1 ≤ C h + 1 :=
          Nat.succ_le_succ (hcard h hh)
        have hcard_succ_real :
            (((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h (lam h)).card + 1 : ℕ) : ℝ) ≤
              ((C h + 1 : ℕ) : ℝ) :=
          Nat.cast_le.mpr hcard_succ
        have hgap_nonneg :
            0 ≤ Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h :=
          Real.secondDerivativeVdc_shiftedCorrelationMajorant_nonneg
            ht (hpos h hh)
        have hright :
            ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h (lam h)).card + 1 : ℕ) : ℝ) *
                Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) ≤
              (((C h + 1 : ℕ) : ℝ) *
                Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) :=
          mul_le_mul_of_nonneg_right hcard_succ_real hgap_nonneg
        add_le_add_right (add_le_add hleft hright) 1)
  exact le_trans hraw hsum

/-- A numerical cardinal budget for each active-center family converts the
refined all-principal-branch envelope into a counted majorant. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedCorrelationEnvelope_le_counted_activeCenter_window_add_refinedPrincipalGapMajorants_add_one
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b H : ℕ}
    {lam W lo hi : ℕ → ℝ}
    (C : ℕ → ℕ)
    (ha : 1 ≤ a)
    (habh :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          a ≤ b - h)
    (hpos :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          1 ≤ h)
    (hlam :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          lam h =
            ‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (h : ℝ))
    (hlam_pi :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          lam h ≤ Real.pi)
    (hrange :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ∀ n : ℕ,
            n ∈ Finset.Ico a (b - h) →
              lo h ≤
                  Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    n ∧
                Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    n ≤ hi h)
    (hwindow :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ∀ k : ℤ,
            k ∈
              Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
                t a b h (lam h) →
              ((Complex.realPhase_integerIncrementResonanceWindow
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                a (b - h) (2 * Real.pi * (k : ℝ)) (lam h)).card :
                  ℝ) ≤ W h)
    (hcard :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          (Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h (lam h)).card ≤ C h)
    (hW_nonneg :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          0 ≤ W h)
    (hinc_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          Complex.realPhase_integerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h)) :
    Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b H ≤
      ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        (((C h : ℝ) * W h) +
          (((C h + 1 : ℕ) *
              (Complex.realPhase_integerIncrementRangeActiveCenters
                (lo h) (hi h) Real.pi).card : ℕ) : ℝ) *
            Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h +
          1) := by
  have hraw :
      Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b H ≤
        ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
          (((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h (lam h)).card : ℝ) * W h) +
            (((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h (lam h)).card + 1 : ℕ) *
                (Complex.realPhase_integerIncrementRangeActiveCenters
                  (lo h) (hi h) Real.pi).card : ℕ) : ℝ) *
              Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h)) +
            1) :=
    Complex.logarithmicPhaseRealPhase_shiftedCorrelationEnvelope_le_activeCenterCount_window_add_refinedPrincipalGapMajorants_add_one
      t ht ha habh hpos hlam hlam_pi hrange hwindow hinc_mono
  have hsum :
      (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
          (((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h (lam h)).card : ℝ) * W h) +
            (((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h (lam h)).card + 1 : ℕ) *
                (Complex.realPhase_integerIncrementRangeActiveCenters
                  (lo h) (hi h) Real.pi).card : ℕ) : ℝ) *
              Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h)) +
            1)) ≤
        ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
          (((C h : ℕ) : ℝ) * W h +
            (((((C h + 1 : ℕ) *
                (Complex.realPhase_integerIncrementRangeActiveCenters
                  (lo h) (hi h) Real.pi).card : ℕ) : ℝ) *
              Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) +
            1)) := by
    exact Finset.sum_le_sum
      (fun h hh =>
        have hcard_real :
            ((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h (lam h)).card : ℝ) ≤ ((C h : ℕ) : ℝ) :=
          Nat.cast_le.mpr (hcard h hh)
        have hleft :
            (((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h (lam h)).card : ℝ) * W h) ≤
              ((C h : ℕ) : ℝ) * W h :=
          mul_le_mul_of_nonneg_right hcard_real (hW_nonneg h hh)
        have hcard_succ_mul :
            ((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h (lam h)).card + 1) *
                (Complex.realPhase_integerIncrementRangeActiveCenters
                  (lo h) (hi h) Real.pi).card ≤
              (C h + 1) *
                (Complex.realPhase_integerIncrementRangeActiveCenters
                  (lo h) (hi h) Real.pi).card :=
          Nat.mul_le_mul_right
            (Complex.realPhase_integerIncrementRangeActiveCenters
              (lo h) (hi h) Real.pi).card
            (Nat.succ_le_succ (hcard h hh))
        have hcard_succ_mul_real :
            (((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h (lam h)).card + 1 : ℕ) *
                (Complex.realPhase_integerIncrementRangeActiveCenters
                  (lo h) (hi h) Real.pi).card : ℕ) : ℝ) ≤
              ((((C h + 1 : ℕ) *
                (Complex.realPhase_integerIncrementRangeActiveCenters
                  (lo h) (hi h) Real.pi).card : ℕ) : ℝ) :=
          Nat.cast_le.mpr hcard_succ_mul
        have hgap_nonneg :
            0 ≤ Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h :=
          Real.secondDerivativeVdc_shiftedCorrelationMajorant_nonneg
            ht (hpos h hh)
        have hright :
            (((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h (lam h)).card + 1 : ℕ) *
                (Complex.realPhase_integerIncrementRangeActiveCenters
                  (lo h) (hi h) Real.pi).card : ℕ) : ℝ) *
                Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) ≤
              (((((C h + 1 : ℕ) *
                (Complex.realPhase_integerIncrementRangeActiveCenters
                  (lo h) (hi h) Real.pi).card : ℕ) : ℝ) *
                Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) :=
          mul_le_mul_of_nonneg_right hcard_succ_mul_real hgap_nonneg
        add_le_add_right (add_le_add hleft hright) 1)
  exact le_trans hraw hsum

/-- Explicit increment ranges supply the active-center count in the active
all-integer resonance envelope. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedCorrelationEnvelope_le_rangeCounted_activeCenter_window_add_gapMajorants_add_one
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b H : ℕ}
    {lam W lo hi : ℕ → ℝ}
    (ha : 1 ≤ a)
    (habh :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          a ≤ b - h)
    (hpos :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          1 ≤ h)
    (hlam :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          lam h =
            ‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (h : ℝ))
    (hlam_pi :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          lam h ≤ Real.pi)
    (hrange :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ∀ n : ℕ,
            n ∈ Finset.Ico a (b - h) →
              lo h ≤
                  Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    n ∧
                Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    n ≤ hi h)
    (hwindow :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ∀ k : ℤ,
            k ∈
              Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
                t a b h (lam h) →
              ((Complex.realPhase_integerIncrementResonanceWindow
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                a (b - h) (2 * Real.pi * (k : ℝ)) (lam h)).card :
                  ℝ) ≤ W h)
    (hW_nonneg :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          0 ≤ W h)
    (hderiv_antitone :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          AntitoneOn
            (fun x : ℝ =>
              ‖deriv
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                h) x‖)
            (Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)))
    (hderiv_lower :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ∀ x : ℝ,
            x ∈ Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ) →
              ‖t‖ *
                  ((((b + 1 : ℕ) : ℝ) *
                    (((b + 1 : ℕ) : ℝ)))⁻¹) *
                  (h : ℝ) ≤
                ‖deriv
                  (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                    h) x‖)
    (hinc_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          Complex.realPhase_integerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h))
    (hred_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          Complex.realPhase_reducedIntegerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h)) :
    Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b H ≤
      ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        (((((Complex.realPhase_integerIncrementRangeActiveCenters
            (lo h) (hi h) (lam h)).card : ℕ) : ℝ) * W h +
          ((((Complex.realPhase_integerIncrementRangeActiveCenters
              (lo h) (hi h) (lam h)).card + 1 : ℕ) : ℝ) *
            Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h)) +
          1) := by
  let C : ℕ → ℕ :=
    fun h : ℕ =>
      (Complex.realPhase_integerIncrementRangeActiveCenters
        (lo h) (hi h) (lam h)).card
  have hcard :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          (Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h (lam h)).card ≤ C h := by
    intro h hh
    exact
      Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters_card_le_rangeActiveCenters_card
        t (hrange h hh)
  exact
    Complex.logarithmicPhaseRealPhase_shiftedCorrelationEnvelope_le_counted_activeCenter_window_add_gapMajorants_add_one
      t ht C ha habh hpos hlam hlam_pi hwindow hcard hW_nonneg
      hderiv_antitone hderiv_lower hinc_mono hred_mono

/-- Explicit increment ranges supply the active-center count in the refined
all-principal-branch active resonance envelope. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedCorrelationEnvelope_le_rangeCounted_activeCenter_window_add_refinedPrincipalGapMajorants_add_one
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b H : ℕ}
    {lam W lo hi : ℕ → ℝ}
    (ha : 1 ≤ a)
    (habh :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          a ≤ b - h)
    (hpos :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          1 ≤ h)
    (hlam :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          lam h =
            ‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (h : ℝ))
    (hlam_pi :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          lam h ≤ Real.pi)
    (hrange :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ∀ n : ℕ,
            n ∈ Finset.Ico a (b - h) →
              lo h ≤
                  Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    n ∧
                Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    n ≤ hi h)
    (hwindow :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ∀ k : ℤ,
            k ∈
              Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
                t a b h (lam h) →
              ((Complex.realPhase_integerIncrementResonanceWindow
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                a (b - h) (2 * Real.pi * (k : ℝ)) (lam h)).card :
                  ℝ) ≤ W h)
    (hW_nonneg :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          0 ≤ W h)
    (hinc_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          Complex.realPhase_integerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h)) :
    Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b H ≤
      ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        (((((Complex.realPhase_integerIncrementRangeActiveCenters
            (lo h) (hi h) (lam h)).card : ℕ) : ℝ) * W h +
          (((((Complex.realPhase_integerIncrementRangeActiveCenters
              (lo h) (hi h) (lam h)).card + 1 : ℕ) *
              (Complex.realPhase_integerIncrementRangeActiveCenters
                (lo h) (hi h) Real.pi).card : ℕ) : ℝ) *
            Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h)) +
          1) := by
  let C : ℕ → ℕ :=
    fun h : ℕ =>
      (Complex.realPhase_integerIncrementRangeActiveCenters
        (lo h) (hi h) (lam h)).card
  have hcard :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          (Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h (lam h)).card ≤ C h := by
    intro h hh
    exact
      Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters_card_le_rangeActiveCenters_card
        t (hrange h hh)
  exact
    Complex.logarithmicPhaseRealPhase_shiftedCorrelationEnvelope_le_counted_activeCenter_window_add_refinedPrincipalGapMajorants_add_one
      t ht C ha habh hpos hlam hlam_pi hrange hwindow hcard hW_nonneg
      hinc_mono

/-- Range-counted all-integer active resonance control supplies the positive
long Weyl target once the resulting explicit radicand is below the target
square. -/
theorem Complex.logarithmicPhaseRealPhase_long_bound_of_rangeCounted_activeCenter_window_radicand
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    {lam W lo hi : ℕ → ℝ}
    (habh :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          a ≤ b - h)
    (hpos :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          1 ≤ h)
    (hlam :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          lam h =
            ‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (h : ℝ))
    (hlam_pi :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          lam h ≤ Real.pi)
    (hrange :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ n : ℕ,
            n ∈ Finset.Ico a (b - h) →
              lo h ≤
                  Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    n ∧
                Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    n ≤ hi h)
    (hwindow :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ k : ℤ,
            k ∈
              Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
                t a b h (lam h) →
              ((Complex.realPhase_integerIncrementResonanceWindow
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                a (b - h) (2 * Real.pi * (k : ℝ)) (lam h)).card :
                  ℝ) ≤ W h)
    (hW_nonneg :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          0 ≤ W h)
    (hderiv_antitone :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          AntitoneOn
            (fun x : ℝ =>
              ‖deriv
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                h) x‖)
            (Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)))
    (hderiv_lower :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ x : ℝ,
            x ∈ Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ) →
              ‖t‖ *
                  ((((b + 1 : ℕ) : ℝ) *
                    (((b + 1 : ℕ) : ℝ)))⁻¹) *
                  (h : ℝ) ≤
                ‖deriv
                  (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                    h) x‖)
    (hinc_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          Complex.realPhase_integerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h))
    (hred_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          Complex.realPhase_reducedIntegerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h))
    (hrad :
      ((Real.secondDerivativeVdc_blockLength a b) +
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ)) *
          (((Real.secondDerivativeVdc_blockLength a b) +
              2 *
                (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                  (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
                  (((((Complex.realPhase_integerIncrementRangeActiveCenters
                      (lo h) (hi h) (lam h)).card : ℕ) : ℝ) * W h +
                    ((((Complex.realPhase_integerIncrementRangeActiveCenters
                        (lo h) (hi h) (lam h)).card + 1 : ℕ) : ℝ) *
                      Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h)) +
                    1))) *
            (((Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℕ) : ℝ)⁻¹)) ≤
        (80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖)))) ^ 2) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  have henvelope :
      Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b (Real.secondDerivativeVdc_weylShiftLength ‖t‖) ≤
        ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
          (((((Complex.realPhase_integerIncrementRangeActiveCenters
              (lo h) (hi h) (lam h)).card : ℕ) : ℝ) * W h +
            ((((Complex.realPhase_integerIncrementRangeActiveCenters
                (lo h) (hi h) (lam h)).card + 1 : ℕ) : ℝ) *
              Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h)) +
            1) :=
    Complex.logarithmicPhaseRealPhase_shiftedCorrelationEnvelope_le_rangeCounted_activeCenter_window_add_gapMajorants_add_one
      t ht ha habh hpos hlam hlam_pi hrange hwindow hW_nonneg
      hderiv_antitone hderiv_lower hinc_mono hred_mono
  exact
    Complex.logarithmicPhaseRealPhase_long_bound_of_weylEnvelope_radicand_target_of_shiftedCorrelationEnvelope_bound
      t ht hab hlong_sqrt henvelope hrad

/-- Range-counted all-integer active resonance control with the refined
principal-branch complement supplies the positive long Weyl target once the
corresponding explicit radicand is below the target square. -/
theorem Complex.logarithmicPhaseRealPhase_long_bound_of_rangeCounted_activeCenter_window_refinedPrincipal_radicand
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    {lam W lo hi : ℕ → ℝ}
    (habh :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          a ≤ b - h)
    (hpos :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          1 ≤ h)
    (hlam :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          lam h =
            ‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (h : ℝ))
    (hlam_pi :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          lam h ≤ Real.pi)
    (hrange :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ n : ℕ,
            n ∈ Finset.Ico a (b - h) →
              lo h ≤
                  Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    n ∧
                Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    n ≤ hi h)
    (hwindow :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ k : ℤ,
            k ∈
              Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
                t a b h (lam h) →
              ((Complex.realPhase_integerIncrementResonanceWindow
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                a (b - h) (2 * Real.pi * (k : ℝ)) (lam h)).card :
                  ℝ) ≤ W h)
    (hW_nonneg :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          0 ≤ W h)
    (hinc_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          Complex.realPhase_integerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h))
    (hrad :
      ((Real.secondDerivativeVdc_blockLength a b) +
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ)) *
          (((Real.secondDerivativeVdc_blockLength a b) +
              2 *
                (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                  (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
                  (((((Complex.realPhase_integerIncrementRangeActiveCenters
                      (lo h) (hi h) (lam h)).card : ℕ) : ℝ) * W h +
                    (((((Complex.realPhase_integerIncrementRangeActiveCenters
                        (lo h) (hi h) (lam h)).card + 1 : ℕ) *
                        (Complex.realPhase_integerIncrementRangeActiveCenters
                          (lo h) (hi h) Real.pi).card : ℕ) : ℝ) *
                      Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h)) +
                    1))) *
            (((Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℕ) : ℝ)⁻¹)) ≤
        (80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖)))) ^ 2) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  have henvelope :
      Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b (Real.secondDerivativeVdc_weylShiftLength ‖t‖) ≤
        ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
          (((((Complex.realPhase_integerIncrementRangeActiveCenters
              (lo h) (hi h) (lam h)).card : ℕ) : ℝ) * W h +
            (((((Complex.realPhase_integerIncrementRangeActiveCenters
                (lo h) (hi h) (lam h)).card + 1 : ℕ) *
                (Complex.realPhase_integerIncrementRangeActiveCenters
                  (lo h) (hi h) Real.pi).card : ℕ) : ℝ) *
              Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h)) +
            1) :=
    Complex.logarithmicPhaseRealPhase_shiftedCorrelationEnvelope_le_rangeCounted_activeCenter_window_add_refinedPrincipalGapMajorants_add_one
      t ht ha habh hpos hlam hlam_pi hrange hwindow hW_nonneg hinc_mono
  exact
    Complex.logarithmicPhaseRealPhase_long_bound_of_weylEnvelope_radicand_target_of_shiftedCorrelationEnvelope_bound
      t ht hab hlong_sqrt henvelope hrad

end

end LFunctions
end Boundary
