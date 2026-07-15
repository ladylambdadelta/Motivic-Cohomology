import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicFiniteInactiveNumericalClosure
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicInfiniteTailClosure
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicSideSpecificActiveClosure
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicCompleteActiveBudget
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicCompleteComplementTail
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicZeroModeArithmetic
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicFiniteComplementBudget

/-!
# Sharp exact B-process budget

The exact quantitative Poisson packet sum is split into complete active
packets, sharp finite nonzero inactive packets, the zero packet, and both
summable infinite tails.  No analytic witnesses occur in this budget.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseSharpFiniteComplementBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhaseFiniteInactiveSharpBudget t a b +
    Complex.logarithmicPhaseQuantitativeZeroModeBudget t a b

def Complex.logarithmicPhaseSharpOutsideTailBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhaseEnhancedFarNegativeTailBudget t a b +
    Complex.logarithmicPhaseEnhancedPositiveTailBudget t a b

def Complex.logarithmicPhaseSharpComplementBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhaseSharpFiniteComplementBudget t a b +
    Complex.logarithmicPhaseSharpOutsideTailBudget t a b

def Complex.logarithmicPhaseSharpBProcessBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhaseBProcessCompleteActiveBudget t a b +
    Complex.logarithmicPhaseSharpComplementBudget t a b

theorem Complex.logarithmicPhaseSharpFiniteComplementBudget_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    0 ≤ Complex.logarithmicPhaseSharpFiniteComplementBudget
      t (a : ℤ) (b : ℤ) := by
  have hfinite :=
    Complex.logarithmicPhaseFiniteInactiveSharpBudget_nonneg
      t ht ht_nonneg a b hgeometry
  have hzero :=
    Complex.logarithmicPhaseQuantitativeZeroModeBudget_nonneg_explicit
      t (a : ℤ) (b : ℤ)
      (Int.ofNat_le.mpr
        (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry))
      (Int.ofNat_le.mpr
        (Real.logarithmicPhaseLongBranchGeometry_order hgeometry))
  unfold Complex.logarithmicPhaseSharpFiniteComplementBudget
  exact add_nonneg hfinite hzero

theorem Complex.logarithmicPhaseSharpOutsideTailBudget_nonneg
    (t : ℝ) (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhaseSharpOutsideTailBudget t a b := by
  unfold Complex.logarithmicPhaseSharpOutsideTailBudget
  exact add_nonneg
    (Complex.logarithmicPhaseEnhancedFarNegativeTailBudget_nonneg_explicit
      t a b ha hab)
    (Complex.logarithmicPhaseEnhancedPositiveTailBudget_nonneg_explicit
      t a b ha hab)

theorem Complex.logarithmicPhaseSharpComplementBudget_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    0 ≤ Complex.logarithmicPhaseSharpComplementBudget
      t (a : ℤ) (b : ℤ) := by
  have ha := Int.ofNat_le.mpr
    (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry)
  have hab := Int.ofNat_le.mpr
    (Real.logarithmicPhaseLongBranchGeometry_order hgeometry)
  unfold Complex.logarithmicPhaseSharpComplementBudget
  exact add_nonneg
    (Complex.logarithmicPhaseSharpFiniteComplementBudget_nonneg
      t ht ht_nonneg a b hgeometry)
    (Complex.logarithmicPhaseSharpOutsideTailBudget_nonneg
      t (a : ℤ) (b : ℤ) ha hab)

theorem Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget_le_sharpFiniteComplement
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget
        t (a : ℤ) (b : ℤ) ≤
      Complex.logarithmicPhaseSharpFiniteComplementBudget
        t (a : ℤ) (b : ℤ) := by
  have ha := Int.ofNat_le.mpr
    (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry)
  have hab := Int.ofNat_le.mpr
    (Real.logarithmicPhaseLongBranchGeometry_order hgeometry)
  have hpartition :=
    Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget_le_left_add_right_add_zero
      t ht ht_nonneg (a : ℤ) (b : ℤ) ha hab
  have hnonzero :=
    Complex.logarithmicPhaseFiniteInactiveNormBudgets_le_sharpBudget
      t ht ht_nonneg a b hgeometry
  have hlift := add_le_add_right hnonzero
    (Complex.logarithmicPhaseQuantitativeZeroModeBudget
      t (a : ℤ) (b : ℤ))
  unfold Complex.logarithmicPhaseSharpFiniteComplementBudget
  exact le_trans hpartition hlift

theorem Complex.logarithmicPhaseAdaptedOutsideRangeBudget_eq_sharpOutsideTail
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhaseAdaptedOutsideRangeBudget t a b =
      Complex.logarithmicPhaseSharpOutsideTailBudget t a b := by
  unfold Complex.logarithmicPhaseSharpOutsideTailBudget
  exact
    Complex.logarithmicPhaseAdaptedOutsideRangeBudget_eq_completeOutsideTailBudget
      t a b

theorem Complex.logarithmicPhaseAdaptedComplementBudget_le_sharpComplement
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseAdaptedComplementBudget
        t (a : ℤ) (b : ℤ) ≤
      Complex.logarithmicPhaseSharpComplementBudget
        t (a : ℤ) (b : ℤ) := by
  have hfinite :=
    Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget_le_sharpFiniteComplement
      t ht ht_nonneg a b hgeometry
  have hfiniteAdapted := Eq.subst
    (motive := fun value : ℝ => value ≤
      Complex.logarithmicPhaseSharpFiniteComplementBudget t (a : ℤ) (b : ℤ))
    (Complex.logarithmicPhaseAdaptedInRangeInactiveBudget_eq_quantitative_of_nonneg
      t ht_nonneg (a : ℤ) (b : ℤ)).symm hfinite
  have houtside :=
    Complex.logarithmicPhaseAdaptedOutsideRangeBudget_eq_sharpOutsideTail
      t (a : ℤ) (b : ℤ)
  unfold Complex.logarithmicPhaseAdaptedComplementBudget
  unfold Complex.logarithmicPhaseSharpComplementBudget
  exact add_le_add hfiniteAdapted (le_of_eq houtside)

theorem Complex.logarithmicPhaseBProcessQuantitativeActiveBudget_le_completeActive
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseBProcessQuantitativeActiveBudget
        t (a : ℤ) (b : ℤ) ≤
      Complex.logarithmicPhaseBProcessCompleteActiveBudget
        t (a : ℤ) (b : ℤ) := by
  exact Complex.logarithmicPhaseBProcessQuantitativeActiveBudget_le_completeActiveBudget
    t ht (a : ℤ) (b : ℤ)

theorem Complex.norm_logarithmicPhaseQuantitativePacket_tsum_le_sharpBProcessBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    ‖∑' m : ℤ,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket
          t (a : ℤ) (b : ℤ) m‖ ≤
      Complex.logarithmicPhaseSharpBProcessBudget
        t (a : ℤ) (b : ℤ) := by
  have ha := Int.ofNat_le.mpr
    (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry)
  have hab := Int.ofNat_le.mpr
    (Real.logarithmicPhaseLongBranchGeometry_order hgeometry)
  have hglobal :=
    Complex.norm_logarithmicPhaseQuantitativePacket_tsum_le_active_add_adaptedComplement
      t (a : ℤ) (b : ℤ) ha hab
  have hactiveTsum :=
    Complex.norm_logarithmicPhaseQuantitativeActive_tsum_le_BProcessBudget
      ht ht_nonneg hgeometry
  have hparameter : t = ‖t‖ :=
    (Real.norm_of_nonneg ht_nonneg).symm
  have hactiveParameter :
      ‖∑' m : {m : ℤ // m ∈
          Complex.logarithmicPhasePoissonActiveModes
            t (a : ℤ) (b : ℤ)},
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket t
            (a : ℤ) (b : ℤ) m‖ =
        ‖∑' m : {m : ℤ // m ∈
          Complex.logarithmicPhasePoissonActiveModes
            t (a : ℤ) (b : ℤ)},
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖
            (a : ℤ) (b : ℤ) m‖ :=
    congrArg (fun parameter : ℝ =>
      ‖∑' m : {m : ℤ // m ∈
          Complex.logarithmicPhasePoissonActiveModes
            t (a : ℤ) (b : ℤ)},
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket parameter
            (a : ℤ) (b : ℤ) m‖) hparameter
  have hactiveTsumNorm :=
    Eq.subst (motive := fun value : ℝ =>
      value ≤ Complex.logarithmicPhaseBProcessQuantitativeActiveBudget
        t (a : ℤ) (b : ℤ)) hactiveParameter hactiveTsum
  have hactive :=
    Complex.logarithmicPhaseBProcessQuantitativeActiveBudget_le_completeActive
      t ht ht_nonneg a b hgeometry
  have hcomplement :=
    Complex.logarithmicPhaseAdaptedComplementBudget_le_sharpComplement
      t ht ht_nonneg a b hgeometry
  have hsum := add_le_add hactive hcomplement
  have hglobal' := le_trans hglobal
    (add_le_add_right hactiveTsumNorm
      (Complex.logarithmicPhaseAdaptedComplementBudget t (a : ℤ) (b : ℤ)))
  have hpacketParameter :
      ‖∑' m : ℤ,
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket t
            (a : ℤ) (b : ℤ) m‖ =
        ‖∑' m : ℤ,
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖
            (a : ℤ) (b : ℤ) m‖ :=
    congrArg (fun parameter : ℝ =>
      ‖∑' m : ℤ,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket parameter
          (a : ℤ) (b : ℤ) m‖) hparameter
  unfold Complex.logarithmicPhaseSharpBProcessBudget
  exact le_trans (le_of_eq hpacketParameter) (le_trans hglobal' hsum)

theorem Complex.logarithmicPhaseSharpFiniteComplementBudget_le_stationary_add_refined
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseSharpFiniteComplementBudget
        t (a : ℤ) (b : ℤ) ≤
      (37 / 2 : ℝ) * Complex.logarithmicPhaseBProcessScale t +
        (11 / 3 : ℝ) * Real.logarithmicPhaseRefinedScale t (b : ℤ) := by
  have hfinite :=
    Complex.logarithmicPhaseFiniteInactiveSharpBudget_le_thirty_seven_halves_scale
      t ht ht_nonneg a b hgeometry
  have hzeroRefined :=
    Complex.logarithmicPhaseQuantitativeZeroModeBudget_le_eleven_thirds_refined
      t a b ht (Real.logarithmicPhaseLongBranchGeometry_order hgeometry)
  unfold Complex.logarithmicPhaseSharpFiniteComplementBudget
  exact add_le_add hfinite hzeroRefined

end

end LFunctions
end Boundary
