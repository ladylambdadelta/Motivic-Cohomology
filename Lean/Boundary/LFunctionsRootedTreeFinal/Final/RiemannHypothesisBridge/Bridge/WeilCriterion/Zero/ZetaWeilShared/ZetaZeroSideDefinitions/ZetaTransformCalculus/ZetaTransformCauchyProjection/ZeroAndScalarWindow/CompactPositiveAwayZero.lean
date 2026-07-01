import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.ZetaTransformCauchyProjection.ZeroAndScalarWindow.PositiveResidueWindow

namespace Boundary

open scoped Filter FourierTransform Topology
open Filter Real Set MeasureTheory

noncomputable section

section FixedLineCauchyProjection

theorem scalarFourierLaplacePlemelj_compactInterval_positive_awayZero_norm_bound_eventually_of_arc
    (a : ℝ) (ha : 0 < a) (R δ Carc : ℝ) (hδ : 0 < δ)
    (hCarc_nonneg : 0 ≤ Carc)
    (harc :
      ∀ᶠ (T : ℝ) in atTop,
        ∀ x : ℝ,
          δ ≤ x →
          ‖x‖ ≤ R →
            norm
              ((scalarFourierLaplacePlemelj_positiveUpperArc a x T *
                Complex.exp ((a : ℂ) * (x : ℂ))) : ℂ) ≤ Carc) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ (T : ℝ) in atTop,
          ∀ x : ℝ,
            δ ≤ x →
            ‖x‖ ≤ R →
              norm
                ((∫ t in Set.Icc (-T) T,
                  (-1 / ((a : ℂ) + t * Complex.I)) *
                    Complex.exp
                      (Complex.I * (t : ℂ) * (x : ℂ)) *
                    Complex.exp ((a : ℂ) * (x : ℂ))) : ℂ)
              ≤ C := by
  let Cresidue : ℝ := norm ((-2 * (Real.pi : ℂ)) : ℂ)
  let C : ℝ := Cresidue + Carc
  have hCresidue_nonneg : 0 ≤ Cresidue := by
    unfold Cresidue
    exact norm_nonneg _
  have hC_nonneg : 0 ≤ C := by
    unfold C
    exact add_nonneg hCresidue_nonneg hCarc_nonneg
  have hresidue_norm :
      norm ((-2 * (Real.pi : ℂ)) : ℂ) = Cresidue := by
    rfl
  exact
    ⟨C, hC_nonneg,
      (harc.and (eventually_gt_atTop a)).mono
        (fun (T : ℝ) hTpair x hδx hxR =>
          have hxpos : x ∈ Set.Ioi (0 : ℝ) :=
            lt_of_lt_of_le hδ hδx
          have hwindow :
              norm
                ((∫ t in Set.Icc (-T) T,
                  (-1 / ((a : ℂ) + t * Complex.I)) *
                    Complex.exp
                      (Complex.I * (t : ℂ) * (x : ℂ)) *
                    Complex.exp ((a : ℂ) * (x : ℂ))) : ℂ)
              ≤ norm ((-2 * (Real.pi : ℂ)) : ℂ) +
                  norm
                    ((scalarFourierLaplacePlemelj_positiveUpperArc a x T *
                      Complex.exp ((a : ℂ) * (x : ℂ))) : ℂ) :=
            scalarFourierLaplacePlemelj_positive_window_with_exp_norm_le_residue_add_upperArc_of_radius
              a ha x hxpos T hTpair.2
          calc
            norm
              ((∫ t in Set.Icc (-T) T,
                (-1 / ((a : ℂ) + t * Complex.I)) *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp ((a : ℂ) * (x : ℂ))) : ℂ)
                ≤ norm ((-2 * (Real.pi : ℂ)) : ℂ) +
                    norm
                      ((scalarFourierLaplacePlemelj_positiveUpperArc a x T *
                        Complex.exp ((a : ℂ) * (x : ℂ))) : ℂ) := hwindow
            _ ≤ norm ((-2 * (Real.pi : ℂ)) : ℂ) + Carc := by
                exact add_le_add_left (hTpair.1 x hδx hxR)
                  (norm ((-2 * (Real.pi : ℂ)) : ℂ))
            _ = C := by
                exact congrArg (fun r : ℝ => r + Carc) hresidue_norm)⟩

theorem scalarFourierLaplacePlemelj_compactInterval_positive_awayZero_norm_bound_eventually
    (a : ℝ) (ha : 0 < a) (R δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ (T : ℝ) in atTop,
          ∀ x : ℝ,
            δ ≤ x →
            ‖x‖ ≤ R →
              norm
                ((∫ t in Set.Icc (-T) T,
                  (-1 / ((a : ℂ) + t * Complex.I)) *
                    Complex.exp
                      (Complex.I * (t : ℂ) * (x : ℂ)) *
                    Complex.exp ((a : ℂ) * (x : ℂ))) : ℂ)
              ≤ C := by
  match scalarFourierLaplacePlemelj_positiveUpperArc_awayZero_mulExp_norm_bound_eventually
    a ha R δ hδ with
  | ⟨Carc, hCarc_nonneg, harc⟩ =>
      exact
        scalarFourierLaplacePlemelj_compactInterval_positive_awayZero_norm_bound_eventually_of_arc
          a ha R δ Carc hδ hCarc_nonneg harc
end FixedLineCauchyProjection

end
end Boundary
