import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.QuantitativeLogarithmicCutoff
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.Support

/-!
# Smooth support for the quantitative logarithmic packet

The explicit transition cutoff is zero on a positive neighborhood of zero for
every positive integer block.  Thus the product with the logarithmic phase is
globally smooth, while retaining the exact lattice values used by Poisson
reconstruction.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped ContDiff FourierTransform Interval

theorem Complex.contDiff_logarithmicPhase_quantitativeBlockCutoffFunction
    (t : ℝ)
    (a b : ℤ)
    (ha : 1 ≤ a) :
    ContDiff ℝ ∞
      (Complex.phaseCutoffFunction
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        (Real.quantitativeLogarithmicBlockCutoff a b)) := by
  exact contDiff_iff_contDiffAt.mpr
    (fun x : ℝ =>
      match Classical.em (x = 0) with
      | Or.inl hx => by
          have hzero_eventually :
              Complex.phaseCutoffFunction
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  (Real.quantitativeLogarithmicBlockCutoff a b) =ᶠ[nhds 0]
                (fun _y : ℝ => (0 : ℂ)) := by
            show
              {y : ℝ |
                Complex.phaseCutoffFunction
                    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                    (Real.quantitativeLogarithmicBlockCutoff a b) y = 0} ∈ nhds 0
            exact
              Filter.mem_of_superset
                (Iio_mem_nhds Real.one_div_three_pos)
                (fun y hy =>
                  (congrArg
                    (fun value : ℝ =>
                      value •
                        Complex.exp
                          (Complex.I *
                            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                              t y : ℂ)))
                    (Real.quantitativeLogarithmicBlockCutoff_eq_zero_of_le_one_div_three
                      ha (le_of_lt hy))).trans
                    (zero_smul ℝ
                      (Complex.exp
                        (Complex.I *
                          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                            t y : ℂ)))))
          have hat_zero :
              ContDiffAt ℝ ∞
                (Complex.phaseCutoffFunction
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  (Real.quantitativeLogarithmicBlockCutoff a b)) 0 :=
            contDiffAt_const.congr_of_eventuallyEq hzero_eventually
          exact
            Eq.subst
              (motive := fun point : ℝ =>
                ContDiffAt ℝ ∞
                  (Complex.phaseCutoffFunction
                    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                    (Real.quantitativeLogarithmicBlockCutoff a b)) point)
              hx.symm
              hat_zero
      | Or.inr hx =>
          Complex.contDiffAt_phaseCutoffFunction
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            (Real.quantitativeLogarithmicBlockCutoff a b)
            x
            (Complex.contDiffAt_logarithmicPhaseRealPhase t x hx)
            (Real.contDiff_quantitativeLogarithmicBlockCutoff a b).contDiffAt)

def Complex.logarithmicPhaseQuantitativeBlockSchwartz
    (t : ℝ)
    (a b : ℤ)
    (ha : 1 ≤ a) : SchwartzMap ℝ ℂ :=
  Complex.phaseCutoffSchwartzOfSmoothProduct
    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
    (Real.quantitativeLogarithmicBlockCutoff a b)
    (Complex.contDiff_logarithmicPhase_quantitativeBlockCutoffFunction t a b ha)
    (Real.hasCompactSupport_quantitativeLogarithmicBlockCutoff a b)

theorem Complex.logarithmicPhaseQuantitativeBlockSchwartz_eval
    (t : ℝ)
    (a b : ℤ)
    (ha : 1 ≤ a)
    (x : ℝ) :
    Complex.logarithmicPhaseQuantitativeBlockSchwartz t a b ha x =
      Complex.phaseCutoffFunction
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        (Real.quantitativeLogarithmicBlockCutoff a b) x :=
  rfl

end
end LFunctions
end Boundary
