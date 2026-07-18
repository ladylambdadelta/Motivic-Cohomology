import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ProbeInterface.ZetaAdmissibleFunction.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaAnalyticOrder.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZero.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroOrbit.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.Owner
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.NormedSpace.Connected
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Data.Finset.Basic
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Constructions

/-!
# Boundary zero-side primitive definitions

This file owns the primitive explicit zero-side functional surface used by the
negative-probe branch. It deliberately does not import the counting and
local-finiteness children.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex Filter MeasureTheory
open scoped Topology ComplexConjugate

theorem conj_zero : conj (0 : ℂ) = 0 :=
  map_zero (starRingEnd ℂ)

theorem conj_one : conj (1 : ℂ) = 1 :=
  map_one (starRingEnd ℂ)

theorem conj_half : conj (1 / 2 : ℂ) = 1 / 2 := by
  calc
    conj (1 / 2 : ℂ) = conj (1 : ℂ) / conj (2 : ℂ) :=
      map_div₀ (starRingEnd ℂ) 1 2
    _ = 1 / 2 := by
      exact congrArg₂ HDiv.hDiv (conj_one) (Complex.conj_natCast 2)

/-- Owner-level name for the completed zeta function in zero-side local proofs. -/
def completedRiemannZetaFunction (s : ℂ) : ℂ :=
  completedRiemannZeta s

/-- Owner-level name for the centered completed zeta function in zero-side local proofs. -/
def centeredCompletedRiemannZetaFunction (z : ℂ) : ℂ :=
  centeredCompletedRiemannZeta z

/-- Bridge from the owner name to the completed zeta function. -/
theorem completedRiemannZetaFunction_eq (s : ℂ) :
    completedRiemannZetaFunction s = completedRiemannZeta s := by
  rfl

/-- Bridge from the owner name to the centered completed zeta function. -/
theorem centeredCompletedRiemannZetaFunction_eq (z : ℂ) :
    centeredCompletedRiemannZetaFunction z = centeredCompletedRiemannZeta z := by
  rfl

/-- Bridge from the centered completed zeta function to the shifted completed zeta. -/
theorem centeredCompletedRiemannZeta_eq_completedRiemannZeta_shift (z : ℂ) :
    centeredCompletedRiemannZeta z = completedRiemannZeta ((1 / 2 : ℂ) + z) := by
  rfl

/-- Owner-name bridge from the centered function to the shifted completed function. -/
theorem centeredCompletedRiemannZetaFunction_eq_completedRiemannZetaFunction_shift
    (z : ℂ) :
    centeredCompletedRiemannZetaFunction z =
      completedRiemannZetaFunction ((1 / 2 : ℂ) + z) :=
  (centeredCompletedRiemannZetaFunction_eq z).trans
    ((centeredCompletedRiemannZeta_eq_completedRiemannZeta_shift z).trans
      (completedRiemannZetaFunction_eq ((1 / 2 : ℂ) + z)).symm)

attribute [irreducible] completedRiemannZetaFunction
attribute [irreducible] centeredCompletedRiemannZetaFunction

/-- Mellin transforms of pointwise real-valued complex functions commute with
complex conjugation.  This is the analytic real-structure input used below for
the completed zeta function. -/
theorem mellin_conj_of_pointwise_conj
    (F : ℝ → ℂ)
    (hF : ∀ t : ℝ, conj (F t) = F t)
    (s : ℂ) :
    mellin F (conj s) = conj (mellin F s) := by
  unfold mellin
  calc
    ∫ t : ℝ in Set.Ioi 0, (t : ℂ) ^ (conj s - 1) • F t =
        ∫ t : ℝ in Set.Ioi 0, conj ((t : ℂ) ^ (s - 1) • F t) := by
      exact
        setIntegral_congr_fun measurableSet_Ioi
          (fun t ht => by
            have ht_pos : 0 < t := ht
            have hExponent : conj s - 1 = conj (s - 1) := by
              calc
                conj s - 1 = conj s - conj 1 := by
                  exact congrArg (fun value : ℂ => conj s - value) conj_one.symm
                _ = conj (s - 1) := by
                  exact (map_sub (conj : ℂ →+* ℂ) s 1).symm
            have hArgument : (t : ℂ).arg ≠ Real.pi := by
              intro hArgument
              have hZeroPi : (0 : ℝ) = Real.pi := by
                exact
                  Eq.trans
                    (Complex.arg_ofReal_of_nonneg ht_pos.le).symm
                    hArgument
              exact Real.pi_ne_zero hZeroPi.symm
            have hPower :
                (t : ℂ) ^ (conj s - 1) = conj ((t : ℂ) ^ (s - 1)) := by
              calc
                (t : ℂ) ^ (conj s - 1) =
                    (t : ℂ) ^ (conj (s - 1)) := by
                      exact congrArg (fun exponent : ℂ => (t : ℂ) ^ exponent) hExponent
                _ = conj (conj (t : ℂ) ^ (s - 1)) := by
                      exact Complex.cpow_conj (t : ℂ) (s - 1) hArgument
                _ = conj ((t : ℂ) ^ (s - 1)) := by
                      have htconj : conj (t : ℂ) = (t : ℂ) :=
                        Complex.conj_ofReal t
                      exact congrArg (fun base : ℂ => conj (base ^ (s - 1))) htconj
            calc
              (t : ℂ) ^ (conj s - 1) • F t =
                  (t : ℂ) ^ (conj s - 1) * F t := by
                    exact rfl
              _ = conj ((t : ℂ) ^ (s - 1)) * conj (F t) := by
                    exact
                      Eq.trans
                        (congrArg (fun value : ℂ => value * F t) hPower)
                        (congrArg
                          (fun value : ℂ => conj ((t : ℂ) ^ (s - 1)) * value)
                          (hF t).symm)
              _ = conj ((t : ℂ) ^ (s - 1)) * F t := by
                    exact congrArg (fun value : ℂ => conj ((t : ℂ) ^ (s - 1)) * value)
                      (hF t)
              _ = conj ((t : ℂ) ^ (s - 1) * F t) := by
                    exact
                      Eq.trans
                        (congrArg
                          (fun value : ℂ => conj ((t : ℂ) ^ (s - 1)) * value)
                          (hF t).symm)
                        (map_mul (conj : ℂ →+* ℂ)
                          ((t : ℂ) ^ (s - 1)) (F t)).symm
              _ = conj ((t : ℂ) ^ (s - 1) • F t) := by
                    exact
                      congrArg (fun value : ℂ => conj value)
                        (show ((t : ℂ) ^ (s - 1) • F t) =
                          (t : ℂ) ^ (s - 1) * F t from rfl).symm)
    _ = conj (∫ t : ℝ in Set.Ioi 0, (t : ℂ) ^ (s - 1) • F t) := by
      exact integral_conj

/-- The even Hurwitz kernel at the Riemann parameter has real values when
viewed in the complex scalar field. -/
theorem hurwitzEvenKernel_zero_conj
    (t : ℝ) :
    conj (HurwitzZeta.evenKernel 0 t : ℂ) =
      (HurwitzZeta.evenKernel 0 t : ℂ) := by
  exact Complex.conj_ofReal (HurwitzZeta.evenKernel 0 t)

/-- The first kernel of the Riemann functional-equation pair is the complex
embedding of the real even Hurwitz kernel. -/
theorem hurwitzEvenFEPair_zero_f_apply
    (t : ℝ) :
    (HurwitzZeta.hurwitzEvenFEPair 0).f t =
      (HurwitzZeta.evenKernel 0 t : ℂ) := by
  rfl

/-- The Riemann functional-equation pair has unit root number. -/
theorem hurwitzEvenFEPair_zero_epsilon :
    (HurwitzZeta.hurwitzEvenFEPair 0).ε = 1 := by
  rfl

/-- The Riemann functional-equation pair has weight one half. -/
theorem hurwitzEvenFEPair_zero_k :
    (HurwitzZeta.hurwitzEvenFEPair 0).k = (1 / 2 : ℝ) := by
  rfl

/-- The first constant term of the Riemann functional-equation pair is one. -/
theorem hurwitzEvenFEPair_zero_f_zero :
    (HurwitzZeta.hurwitzEvenFEPair 0).f₀ = 1 := by
  change (if (0 : UnitAddCircle) = 0 then 1 else 0) = 1
  exact if_pos rfl

/-- The second constant term of the Riemann functional-equation pair is one. -/
theorem hurwitzEvenFEPair_zero_g_zero :
    (HurwitzZeta.hurwitzEvenFEPair 0).g₀ = 1 := by
  rfl

/-- On the upper support branch, the modified Riemann kernel is the even
Hurwitz kernel minus its constant term. -/
theorem hurwitzEvenFEPair_zero_f_modif_of_one_lt
    {t : ℝ}
    (ht : 1 < t) :
    (HurwitzZeta.hurwitzEvenFEPair 0).f_modif t =
      (HurwitzZeta.evenKernel 0 t : ℂ) - 1 := by
  let P : WeakFEPair ℂ := HurwitzZeta.hurwitzEvenFEPair 0
  have htIoi : t ∈ Set.Ioi 1 := ht
  have htNotIoo : t ∉ Set.Ioo 0 1 :=
    Set.not_mem_Ioo_of_ge ht.le
  have hSupport :
      P.f_modif t = P.f t - P.f₀ := by
    calc
      P.f_modif t =
          (Set.Ioi 1).indicator (fun x : ℝ => P.f x - P.f₀) t +
            (Set.Ioo 0 1).indicator
              (fun x : ℝ =>
                P.f x - (P.ε * ((x ^ (-P.k) : ℝ) : ℂ)) • P.g₀)
                t := by
          rfl
      _ = (P.f t - P.f₀) + 0 := by
          exact
            congrArg₂ HAdd.hAdd
              (Set.indicator_of_mem htIoi (fun x : ℝ => P.f x - P.f₀))
              (Set.indicator_of_not_mem htNotIoo
                (fun x : ℝ => P.f x - (P.ε * ((x ^ (-P.k) : ℝ) : ℂ)) • P.g₀))
      _ = P.f t - P.f₀ := add_zero (P.f t - P.f₀)
  change P.f_modif t = (HurwitzZeta.evenKernel 0 t : ℂ) - 1
  calc
    P.f_modif t = P.f t - P.f₀ := hSupport
    _ = (HurwitzZeta.evenKernel 0 t : ℂ) - 1 := by
      exact
        congrArg₂ HSub.hSub
          (hurwitzEvenFEPair_zero_f_apply t)
          hurwitzEvenFEPair_zero_f_zero

/-- On the middle support branch, the modified Riemann kernel is the raw
kernel minus the explicit functional-equation correction. -/
theorem hurwitzEvenFEPair_zero_f_modif_of_mem_Ioo
    {t : ℝ}
    (ht : t ∈ Set.Ioo 0 1) :
    (HurwitzZeta.hurwitzEvenFEPair 0).f_modif t =
      (HurwitzZeta.hurwitzEvenFEPair 0).f t -
        ((HurwitzZeta.hurwitzEvenFEPair 0).ε *
          ((t ^ (-(HurwitzZeta.hurwitzEvenFEPair 0).k) : ℝ) : ℂ)) •
            (HurwitzZeta.hurwitzEvenFEPair 0).g₀ := by
  let P : WeakFEPair ℂ := HurwitzZeta.hurwitzEvenFEPair 0
  have htNotIoi : t ∉ Set.Ioi 1 :=
    Set.not_mem_Ioi.mpr ht.2.le
  have hSupport :
      P.f_modif t =
        P.f t - (P.ε * ((t ^ (-P.k) : ℝ) : ℂ)) • P.g₀ := by
    calc
      P.f_modif t =
          (Set.Ioi 1).indicator (fun x : ℝ => P.f x - P.f₀) t +
            (Set.Ioo 0 1).indicator
              (fun x : ℝ =>
                P.f x - (P.ε * ((x ^ (-P.k) : ℝ) : ℂ)) • P.g₀)
                t := by
          rfl
      _ = 0 + (P.f t - (P.ε * ((t ^ (-P.k) : ℝ) : ℂ)) • P.g₀) := by
          exact
            congrArg₂ HAdd.hAdd
              (Set.indicator_of_not_mem htNotIoi
                (fun x : ℝ => P.f x - P.f₀))
              (Set.indicator_of_mem ht
                (fun x : ℝ => P.f x - (P.ε * ((x ^ (-P.k) : ℝ) : ℂ)) • P.g₀))
      _ = P.f t - (P.ε * ((t ^ (-P.k) : ℝ) : ℂ)) • P.g₀ := by
          exact zero_add (P.f t - (P.ε * ((t ^ (-P.k) : ℝ) : ℂ)) • P.g₀)
  exact hSupport

/-- The middle support branch is a difference of two real-valued complex
terms after evaluating the Riemann functional-equation pair. -/
theorem hurwitzEvenFEPair_zero_f_modif_middle_normalForm
    {t : ℝ}
    (ht : t ∈ Set.Ioo 0 1) :
    (HurwitzZeta.hurwitzEvenFEPair 0).f_modif t =
      (HurwitzZeta.evenKernel 0 t : ℂ) -
        ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  have hBranch := hurwitzEvenFEPair_zero_f_modif_of_mem_Ioo ht
  calc
    (HurwitzZeta.hurwitzEvenFEPair 0).f_modif t =
        (HurwitzZeta.hurwitzEvenFEPair 0).f t -
          ((HurwitzZeta.hurwitzEvenFEPair 0).ε *
            ((t ^ (-(HurwitzZeta.hurwitzEvenFEPair 0).k) : ℝ) : ℂ)) •
              (HurwitzZeta.hurwitzEvenFEPair 0).g₀ := hBranch
    _ = (HurwitzZeta.evenKernel 0 t : ℂ) -
          ((1 : ℂ) * ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) • (1 : ℂ) := by
      exact
        congrArg₂ HSub.hSub
          (hurwitzEvenFEPair_zero_f_apply t)
          (congrArg₂ HSMul.hSMul
            (congrArg₂ HMul.hMul
              hurwitzEvenFEPair_zero_epsilon
              (congrArg
                (fun exponent : ℝ => ((t ^ (-exponent) : ℝ) : ℂ))
                hurwitzEvenFEPair_zero_k))
            hurwitzEvenFEPair_zero_g_zero)
    _ = (HurwitzZeta.evenKernel 0 t : ℂ) -
          ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
      exact
        congrArg
          (fun correction : ℂ => (HurwitzZeta.evenKernel 0 t : ℂ) - correction)
          (calc
            ((1 : ℂ) * ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) • (1 : ℂ) =
                ((1 : ℂ) * ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) * (1 : ℂ) := by
                  exact rfl
            _ = ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
                  exact
                    Eq.trans
                      (mul_one ((1 : ℂ) * ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)))
                      (one_mul ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)))

/-- Outside both support regions, the modified Riemann kernel vanishes. -/
theorem hurwitzEvenFEPair_zero_f_modif_eq_zero_of_outside
    {t : ℝ}
    (htIoi : t ∉ Set.Ioi 1)
    (htIoo : t ∉ Set.Ioo 0 1) :
    (HurwitzZeta.hurwitzEvenFEPair 0).f_modif t = 0 := by
  let P : WeakFEPair ℂ := HurwitzZeta.hurwitzEvenFEPair 0
  have hSupport : P.f_modif t = 0 := by
    calc
      P.f_modif t =
          (Set.Ioi 1).indicator (fun x : ℝ => P.f x - P.f₀) t +
            (Set.Ioo 0 1).indicator
              (fun x : ℝ =>
                P.f x - (P.ε * ((x ^ (-P.k) : ℝ) : ℂ)) • P.g₀)
                t := by
          rfl
      _ = 0 + 0 := by
          exact
            congrArg₂ HAdd.hAdd
              (Set.indicator_of_not_mem htIoi (fun x : ℝ => P.f x - P.f₀))
              (Set.indicator_of_not_mem htIoo
                (fun x : ℝ => P.f x - (P.ε * ((x ^ (-P.k) : ℝ) : ℂ)) • P.g₀))
      _ = 0 := zero_add 0
  exact hSupport

/-- The modified Riemann kernel is pointwise fixed by complex conjugation. -/
theorem hurwitzEvenFEPair_zero_f_modif_conj
    (t : ℝ) :
    conj ((HurwitzZeta.hurwitzEvenFEPair 0).f_modif t) =
      (HurwitzZeta.hurwitzEvenFEPair 0).f_modif t := by
  by_cases hTop : 1 < t
  · have hBranch := hurwitzEvenFEPair_zero_f_modif_of_one_lt hTop
    calc
      conj ((HurwitzZeta.hurwitzEvenFEPair 0).f_modif t) =
          conj ((HurwitzZeta.evenKernel 0 t : ℂ) - 1) := by
            exact congrArg (fun value : ℂ => conj value) hBranch
      _ = conj (HurwitzZeta.evenKernel 0 t : ℂ) - conj 1 := by
            exact map_sub (conj : ℂ →+* ℂ)
              (HurwitzZeta.evenKernel 0 t : ℂ) 1
      _ = (HurwitzZeta.evenKernel 0 t : ℂ) - 1 := by
            exact
              congrArg₂ HSub.hSub
                (hurwitzEvenKernel_zero_conj t)
                conj_one
      _ = (HurwitzZeta.hurwitzEvenFEPair 0).f_modif t := hBranch.symm
  · have hTopSet : t ∉ Set.Ioi 1 :=
      Set.not_mem_Ioi.mpr (not_lt.mp hTop)
    by_cases hMiddle : t ∈ Set.Ioo 0 1
    · have hBranch := hurwitzEvenFEPair_zero_f_modif_middle_normalForm hMiddle
      calc
        conj ((HurwitzZeta.hurwitzEvenFEPair 0).f_modif t) =
            conj ((HurwitzZeta.evenKernel 0 t : ℂ) -
              ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) := by
              exact congrArg (fun value : ℂ => conj value) hBranch
        _ = conj (HurwitzZeta.evenKernel 0 t : ℂ) -
              conj ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
              exact map_sub (conj : ℂ →+* ℂ)
                (HurwitzZeta.evenKernel 0 t : ℂ)
                ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
        _ = (HurwitzZeta.evenKernel 0 t : ℂ) -
              ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
              exact
                congrArg₂ HSub.hSub
                  (hurwitzEvenKernel_zero_conj t)
                  (Complex.conj_ofReal (t ^ (-(1 / 2 : ℝ))))
        _ = (HurwitzZeta.hurwitzEvenFEPair 0).f_modif t := hBranch.symm
    · have hZero :=
        hurwitzEvenFEPair_zero_f_modif_eq_zero_of_outside hTopSet hMiddle
      calc
        conj ((HurwitzZeta.hurwitzEvenFEPair 0).f_modif t) = conj 0 :=
            congrArg (fun value : ℂ => conj value) hZero
        _ = 0 := conj_zero
        _ = (HurwitzZeta.hurwitzEvenFEPair 0).f_modif t := hZero.symm

/-- The pole-cleared completed Riemann zeta function has real structure. -/
theorem completedRiemannZeta₀_conj
    (s : ℂ) :
    completedRiemannZeta₀ (conj s) = conj (completedRiemannZeta₀ s) := by
  let P : WeakFEPair ℂ := HurwitzZeta.hurwitzEvenFEPair 0
  have hArgument : conj s / 2 = conj (s / 2) := by
    calc
      conj s / 2 = conj s / conj 2 := by
        exact congrArg (fun denominator : ℂ => conj s / denominator)
          (Complex.conj_natCast 2).symm
      _ = conj (s / 2) := by
        exact (map_div₀ (conj : ℂ →+* ℂ) s 2).symm
  change P.Λ₀ (conj s / 2) / 2 = conj (P.Λ₀ (s / 2) / 2)
  calc
    P.Λ₀ (conj s / 2) / 2 = P.Λ₀ (conj (s / 2)) / 2 := by
      exact congrArg (fun argument : ℂ => P.Λ₀ argument / 2) hArgument
    _ = conj (P.Λ₀ (s / 2)) / 2 := by
      exact
        congrArg (fun value : ℂ => value / 2)
          (mellin_conj_of_pointwise_conj P.f_modif
            (by
              intro t
              exact hurwitzEvenFEPair_zero_f_modif_conj t)
            (s / 2))
    _ = conj (P.Λ₀ (s / 2) / 2) := by
      exact
        (Eq.trans
          (map_div₀ (conj : ℂ →+* ℂ) (P.Λ₀ (s / 2)) 2)
            (congrArg (fun denominator : ℂ => conj (P.Λ₀ (s / 2)) / denominator)
              (Complex.conj_natCast 2))).symm

/-- The completed Riemann zeta function has real structure. -/
theorem completedRiemannZeta_conj
    (s : ℂ) :
    completedRiemannZeta (conj s) = conj (completedRiemannZeta s) := by
  have hFirstPole : 1 / conj s = conj (1 / s) := by
    calc
      1 / conj s = conj 1 / conj s := by
        exact congrArg (fun numerator : ℂ => numerator / conj s) conj_one.symm
      _ = conj (1 / s) := by
        exact (map_div₀ (conj : ℂ →+* ℂ) 1 s).symm
  have hSecondDenominator : 1 - conj s = conj (1 - s) := by
    calc
      1 - conj s = conj 1 - conj s := by
        exact congrArg (fun value : ℂ => value - conj s) conj_one.symm
      _ = conj (1 - s) := by
        exact (map_sub (conj : ℂ →+* ℂ) 1 s).symm
  have hSecondPole : 1 / (1 - conj s) = conj (1 / (1 - s)) := by
    calc
      1 / (1 - conj s) = 1 / conj (1 - s) := by
        exact congrArg (fun denominator : ℂ => 1 / denominator) hSecondDenominator
      _ = conj 1 / conj (1 - s) := by
        exact congrArg (fun numerator : ℂ => numerator / conj (1 - s)) conj_one.symm
      _ = conj (1 / (1 - s)) := by
        exact (map_div₀ (conj : ℂ →+* ℂ) 1 (1 - s)).symm
  calc
    completedRiemannZeta (conj s) =
        completedRiemannZeta₀ (conj s) - 1 / conj s - 1 / (1 - conj s) :=
      completedRiemannZeta_eq (conj s)
    _ = conj (completedRiemannZeta₀ s) - conj (1 / s) -
          conj (1 / (1 - s)) := by
      exact
        congrArg₂ HSub.hSub
          (congrArg₂ HSub.hSub
            (completedRiemannZeta₀_conj s)
            hFirstPole)
          hSecondPole
    _ = conj (completedRiemannZeta₀ s - 1 / s - 1 / (1 - s)) := by
      have hmap :
          conj (completedRiemannZeta₀ s - 1 / s - 1 / (1 - s)) =
            (conj (completedRiemannZeta₀ s) - conj (1 / s)) -
              conj (1 / (1 - s)) := by
        exact
          Eq.trans
            (map_sub (conj : ℂ →+* ℂ)
              (completedRiemannZeta₀ s - 1 / s)
              (1 / (1 - s)))
            (congrArg
              (fun value : ℂ => value - conj (1 / (1 - s)))
              (map_sub (conj : ℂ →+* ℂ)
                (completedRiemannZeta₀ s)
                (1 / s)))
      exact hmap.symm
    _ = conj (completedRiemannZeta s) := by
      exact congrArg (fun value : ℂ => conj value) (completedRiemannZeta_eq s).symm

/-- The centered completed Riemann zeta function has real structure. -/
theorem centeredCompletedRiemannZeta_conj
    (z : ℂ) :
    centeredCompletedRiemannZeta z = conj (centeredCompletedRiemannZeta (conj z)) := by
  calc
    centeredCompletedRiemannZeta z = completedRiemannZeta ((1 / 2 : ℂ) + z) := by
      rfl
    _ = conj (completedRiemannZeta (conj ((1 / 2 : ℂ) + z))) := by
      exact
        Eq.trans
          (Eq.symm (Complex.conj_conj (completedRiemannZeta ((1 / 2 : ℂ) + z))))
          (congrArg (fun value : ℂ => conj value)
            (completedRiemannZeta_conj ((1 / 2 : ℂ) + z)).symm)
    _ = conj (completedRiemannZeta ((1 / 2 : ℂ) + conj z)) := by
      exact
        congrArg (fun value : ℂ => conj (completedRiemannZeta value))
          (calc
            conj ((1 / 2 : ℂ) + z) = conj (1 / 2 : ℂ) + conj z :=
              map_add (conj : ℂ →+* ℂ) (1 / 2) z
            _ = (1 / 2 : ℂ) + conj z := by
              exact congrArg (fun value : ℂ => value + conj z)
                conj_half)
    _ = conj (centeredCompletedRiemannZeta (conj z)) := by
      rfl

/-- Conjugation transport in the forward centered-completed-zeta direction. -/
theorem centeredCompletedRiemannZeta_conj_apply
    (z : ℂ) :
    centeredCompletedRiemannZeta (conj z) =
      conj (centeredCompletedRiemannZeta z) := by
  calc
    centeredCompletedRiemannZeta (conj z) =
        conj (centeredCompletedRiemannZeta (conj (conj z))) :=
      centeredCompletedRiemannZeta_conj (conj z)
    _ = conj (centeredCompletedRiemannZeta z) := by
      exact
        congrArg (fun argument : ℂ => conj (centeredCompletedRiemannZeta argument))
          (Complex.conj_conj z)

private theorem complex_neg_neg_half :
    - (-(1 / 2 : ℂ)) = (1 / 2 : ℂ) :=
  neg_neg (1 / 2 : ℂ)

private theorem complex_add_sub_half (z : ℂ) :
    ((1 / 2 : ℂ) + z) - (1 / 2 : ℂ) = z :=
  add_sub_cancel_left (1 / 2 : ℂ) z

private theorem complex_zero_sub_half :
    (0 : ℂ) - (1 / 2 : ℂ) = -(1 / 2 : ℂ) :=
  zero_sub (1 / 2 : ℂ)

private theorem complex_half_add_half :
    (1 / 2 : ℂ) + (1 / 2 : ℂ) = 1 := by
  have htwo_ne : (2 : ℂ) ≠ 0 :=
    two_ne_zero
  calc
    (1 / 2 : ℂ) + (1 / 2 : ℂ) =
        (1 + 1 : ℂ) / 2 := by
      exact (add_div (1 : ℂ) 1 2).symm
    _ = (2 : ℂ) / 2 := by
      exact congrArg (fun w : ℂ => w / 2) one_add_one_eq_two
    _ = 1 := by
      exact div_self htwo_ne

private theorem complex_sub_half_eq_zero_of_half_add_eq_one
    {z : ℂ}
    (h : (1 / 2 : ℂ) + z = 1) :
    z - (1 / 2 : ℂ) = 0 := by
  have htarget :
      (1 / 2 : ℂ) + z = (1 / 2 : ℂ) + (1 / 2 : ℂ) :=
    Eq.trans h complex_half_add_half.symm
  have hz : z = (1 / 2 : ℂ) :=
    add_left_cancel htarget
  exact sub_eq_zero.mpr hz

private theorem complex_sub_add_half (z : ℂ) :
    (z - (1 / 2 : ℂ)) + (1 / 2 : ℂ) = z :=
  sub_add_cancel z (1 / 2 : ℂ)

private theorem complex_half_add_sub_half (z : ℂ) :
    (1 / 2 : ℂ) + (z - (1 / 2 : ℂ)) = z := by
  calc
    (1 / 2 : ℂ) + (z - (1 / 2 : ℂ)) =
        (1 / 2 : ℂ) + (z + (-(1 / 2 : ℂ))) := by
      exact congrArg
        (fun w : ℂ => (1 / 2 : ℂ) + w)
        (sub_eq_add_neg z (1 / 2 : ℂ))
    _ = ((1 / 2 : ℂ) + z) + (-(1 / 2 : ℂ)) := by
      exact (add_assoc (1 / 2 : ℂ) z (-(1 / 2 : ℂ))).symm
    _ = (z + (1 / 2 : ℂ)) + (-(1 / 2 : ℂ)) := by
      exact congrArg
        (fun w : ℂ => w + (-(1 / 2 : ℂ)))
        (add_comm (1 / 2 : ℂ) z)
    _ = z + ((1 / 2 : ℂ) + (-(1 / 2 : ℂ))) := by
      exact add_assoc z (1 / 2 : ℂ) (-(1 / 2 : ℂ))
    _ = z + 0 := by
      exact congrArg
        (fun w : ℂ => z + w)
        (add_neg_cancel (1 / 2 : ℂ))
    _ = z := add_zero z

/-- The centered completed zeta zero predicate used by the zero-side
definitions. Completed zero-side coordinates exclude the shifted pole
locations; the shifted poles are handled by the pole/correction channels. -/
abbrev ZetaCompletedZero (ρ : ℂ) : Prop :=
  ρ ≠ -(1 / 2 : ℂ) ∧
    ρ ≠ (1 / 2 : ℂ) ∧
      centeredCompletedRiemannZetaFunction ρ = 0

/-- A completed zero is a zero of the owner-named centered completed zeta function. -/
theorem zetaCompletedZero_zero
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    centeredCompletedRiemannZetaFunction (ρ : ℂ) = 0 :=
  ρ.2.2.2

/-- Constructor for completed zeros after the shifted poles have been excluded. -/
theorem zetaCompletedZero_mk
    {ρ : ℂ}
    (hneg : ρ ≠ -(1 / 2 : ℂ))
    (hpos : ρ ≠ (1 / 2 : ℂ))
    (hzero : centeredCompletedRiemannZetaFunction ρ = 0) :
    ZetaCompletedZero ρ :=
  ⟨hneg, hpos, hzero⟩

/-- A raw completed-zero proof carries the zero equation. -/
theorem zetaCompletedZero_zero_of_prop
    {ρ : ℂ}
    (hρ : ZetaCompletedZero ρ) :
    centeredCompletedRiemannZetaFunction ρ = 0 :=
  hρ.2.2

/-- A raw completed-zero proof excludes the negative shifted pole. -/
theorem zetaCompletedZero_ne_negHalf_of_prop
    {ρ : ℂ}
    (hρ : ZetaCompletedZero ρ) :
    ρ ≠ -(1 / 2 : ℂ) :=
  hρ.1

/-- A raw completed-zero proof excludes the positive shifted pole. -/
theorem zetaCompletedZero_ne_posHalf_of_prop
    {ρ : ℂ}
    (hρ : ZetaCompletedZero ρ) :
    ρ ≠ (1 / 2 : ℂ) :=
  hρ.2.1

/-- The completed-zero locus is stable under centered negation. -/
theorem zetaCompletedZero_neg
    {ρ : ℂ}
    (hρ : ZetaCompletedZero ρ) :
    ZetaCompletedZero (-ρ) := by
  have hneg : -ρ ≠ -(1 / 2 : ℂ) := by
    intro hneg
    have hρpos : ρ = (1 / 2 : ℂ) := by
      calc
        ρ = -(-ρ) := by exact (neg_neg ρ).symm
        _ = - (-(1 / 2 : ℂ)) := by
          exact congrArg Neg.neg hneg
        _ = (1 / 2 : ℂ) := complex_neg_neg_half
    exact zetaCompletedZero_ne_posHalf_of_prop hρ hρpos
  have hpos : -ρ ≠ (1 / 2 : ℂ) := by
    intro hpos
    have hρneg : ρ = -(1 / 2 : ℂ) := by
      calc
        ρ = -(-ρ) := by exact (neg_neg ρ).symm
        _ = - (1 / 2 : ℂ) := by
          exact congrArg Neg.neg hpos
    exact zetaCompletedZero_ne_negHalf_of_prop hρ hρneg
  have hzero :
      centeredCompletedRiemannZetaFunction (-ρ) = 0 := by
    calc
      centeredCompletedRiemannZetaFunction (-ρ) =
          centeredCompletedRiemannZeta (-ρ) := by
        exact centeredCompletedRiemannZetaFunction_eq (-ρ)
      _ = centeredCompletedRiemannZeta ρ := by
        exact centeredCompletedRiemannZeta_neg ρ
      _ = centeredCompletedRiemannZetaFunction ρ := by
        exact (centeredCompletedRiemannZetaFunction_eq ρ).symm
      _ = 0 := zetaCompletedZero_zero_of_prop hρ
  exact zetaCompletedZero_mk hneg hpos hzero

/-- The completed-zero locus is stable under complex conjugation. -/
theorem zetaCompletedZero_conj
    {ρ : ℂ}
    (hρ : ZetaCompletedZero ρ) :
    ZetaCompletedZero (conj ρ) := by
  have hneg : conj ρ ≠ -(1 / 2 : ℂ) := by
    intro hneg
    apply hρ.1
    calc
      ρ = conj (conj ρ) := (Complex.conj_conj ρ).symm
      _ = conj (-(1 / 2 : ℂ)) := by
        exact congrArg (fun value : ℂ => conj value) hneg
      _ = -(1 / 2 : ℂ) := by
        calc
          conj (-(1 / 2 : ℂ)) = -conj (1 / 2 : ℂ) :=
            map_neg (conj : ℂ →+* ℂ) (1 / 2 : ℂ)
          _ = -(1 / 2 : ℂ) := by
            exact congrArg Neg.neg conj_half
  have hpos : conj ρ ≠ (1 / 2 : ℂ) := by
    intro hpos
    apply hρ.2.1
    calc
      ρ = conj (conj ρ) := (Complex.conj_conj ρ).symm
      _ = conj (1 / 2 : ℂ) := by
        exact congrArg (fun value : ℂ => conj value) hpos
      _ = (1 / 2 : ℂ) := conj_half
  have hzero : centeredCompletedRiemannZetaFunction (conj ρ) = 0 := by
    calc
      centeredCompletedRiemannZetaFunction (conj ρ) =
          centeredCompletedRiemannZeta (conj ρ) :=
        centeredCompletedRiemannZetaFunction_eq (conj ρ)
      _ = conj (centeredCompletedRiemannZeta ρ) :=
        centeredCompletedRiemannZeta_conj_apply ρ
      _ = conj (centeredCompletedRiemannZetaFunction ρ) := by
        exact
          congrArg (fun value : ℂ => conj value)
            (centeredCompletedRiemannZetaFunction_eq ρ).symm
      _ = conj 0 := by
        exact congrArg (fun value : ℂ => conj value) hρ.2.2
      _ = 0 := conj_zero
  exact ⟨hneg, hpos, hzero⟩

/-- The multiplicity of a completed zeta zero.

This uses the local analytic order of the entire cleared zero-carrier.  At
non-pole centered zeros, the clearing factor is a unit, so this is the same
zero multiplicity as the centered completed zeta function without requiring a
global decidability branch for analyticity. -/
noncomputable def completedZetaZeroMultiplicity (ρ : ℂ) : ℕ :=
  (centeredCompletedRiemannZetaZeroCarrier_analyticAt ρ).order.toNat

/-- The multiplicity of a centered completed zeta zero. -/
def zetaZeroMultiplicity (ρ : ℂ) : ℕ :=
  completedZetaZeroMultiplicity ρ

/-- The completed-zero multiplicity is the local analytic order of the cleared carrier. -/
theorem completedZetaZeroMultiplicity_eq_carrier_order (ρ : ℂ) :
    completedZetaZeroMultiplicity ρ =
      (centeredCompletedRiemannZetaZeroCarrier_analyticAt ρ).order.toNat := by
  rfl

/-- A completed zero is not the negative shifted pole. -/
theorem zetaCompletedZero_ne_negHalf
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    (ρ : ℂ) ≠ -(1 / 2 : ℂ) := by
  exact ρ.2.1

/-- A completed zero is not the positive shifted pole. -/
theorem zetaCompletedZero_ne_posHalf
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    (ρ : ℂ) ≠ (1 / 2 : ℂ) := by
  exact ρ.2.2.1

/-- The completed Riemann zeta factors as `ζ · Γℝ` away from `0`. -/
private theorem completedRiemannZeta_eq_riemannZeta_mul_gamma_core
    {s : ℂ}
    (hs : s ≠ 0)
    (hΓ : Gammaℝ s ≠ 0) :
    completedRiemannZeta s = riemannZeta s * Gammaℝ s := by
  have hquotient :
      riemannZeta s = completedRiemannZeta s / Gammaℝ s :=
    riemannZeta_def_of_ne_zero hs
  exact (div_eq_iff hΓ).mp hquotient.symm

/-- The completed Riemann zeta factors at `2`. -/
private theorem completedRiemannZeta_two_eq_riemannZeta_mul_gamma :
    completedRiemannZeta (2 : ℂ) =
      riemannZeta (2 : ℂ) * Gammaℝ (2 : ℂ) := by
  have htwo_ne : (2 : ℂ) ≠ 0 :=
    two_ne_zero
  have hgamma : Gammaℝ (2 : ℂ) ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos
      (show 0 < (2 : ℂ).re by
        exact zero_lt_two)
  exact completedRiemannZeta_eq_riemannZeta_mul_gamma_core htwo_ne hgamma

/-- The completed Gamma factor is nonzero at `2`. -/
private theorem Gammaℝ_two_ne_zero :
    Gammaℝ (2 : ℂ) ≠ 0 :=
  Gammaℝ_ne_zero_of_re_pos
    (show 0 < (2 : ℂ).re by
      exact zero_lt_two)

/-- The zeta value at `2` is nonzero. -/
private theorem riemannZeta_two_ne_zero :
    riemannZeta (2 : ℂ) ≠ 0 := by
  have hpi : (Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hpi_sq : (Real.pi : ℂ) ^ 2 ≠ 0 :=
    pow_ne_zero 2 hpi
  have hsix : (6 : ℂ) ≠ 0 :=
    OfNat.ofNat_ne_zero 6
  have hzeta_two_rhs : (Real.pi : ℂ) ^ 2 / 6 ≠ 0 :=
    div_ne_zero hpi_sq hsix
  intro hzeta
  exact hzeta_two_rhs ((riemannZeta_two).symm.trans hzeta)

/-- The product `ζ(2) Γℝ(2)` is nonzero. -/
private theorem riemannZeta_mul_Gammaℝ_two_ne_zero :
    riemannZeta (2 : ℂ) * Gammaℝ (2 : ℂ) ≠ 0 :=
  mul_ne_zero riemannZeta_two_ne_zero Gammaℝ_two_ne_zero

/-- The punctured plane for completed zeta. -/
private def completedRiemannZetaPuncturedPlane : Set ℂ :=
  {w : ℂ | w ≠ 0 ∧ w ≠ 1}

/-- The explicit two-point complement used for the completed-zeta punctured plane. -/
private theorem completedRiemannZetaPuncturedPlane_eq_twoPoint_compl :
    completedRiemannZetaPuncturedPlane = ({0, 1} : Set ℂ)ᶜ := by
  ext w
  constructor
  · intro hw
    intro hwset
    match hwset with
    | Or.inl h0 => exact hw.1 h0
    | Or.inr h1 => exact hw.2 h1
  · intro hw
    constructor
    · intro h0
      exact hw (Or.inl h0)
    · intro h1
      exact hw (Or.inr h1)

/-- The deleted two-point set is countable. -/
private theorem completedRiemannZeta_twoPoint_countable :
    ({0, 1} : Set ℂ).Countable :=
  ((Set.finite_singleton (1 : ℂ)).insert (0 : ℂ)).countable

/-- The complex line has real rank greater than one. -/
private theorem complex_rank_real_gt_one :
    1 < Module.rank ℝ ℂ :=
  Complex.rank_real_complex ▸ Cardinal.one_lt_two

/-- Points away from `0` and `1` lie in the completed-zeta punctured plane. -/
private theorem mem_completedRiemannZetaPuncturedPlane_of_ne
    {z : ℂ}
    (hz0 : z ≠ 0)
    (hz1 : z ≠ 1) :
    z ∈ completedRiemannZetaPuncturedPlane :=
  And.intro hz0 hz1

/-- The completed-zeta punctured plane is path connected. -/
private theorem completedRiemannZetaPuncturedPlane_isPathConnected :
    IsPathConnected completedRiemannZetaPuncturedPlane := by
  have hpath_compl : IsPathConnected ({0, 1} : Set ℂ)ᶜ :=
    Set.Countable.isPathConnected_compl_of_one_lt_rank
      complex_rank_real_gt_one
      completedRiemannZeta_twoPoint_countable
  exact completedRiemannZetaPuncturedPlane_eq_twoPoint_compl.symm ▸ hpath_compl

/-- The completed-zeta punctured plane is preconnected. -/
private theorem completedRiemannZetaPuncturedPlane_isPreconnected :
    IsPreconnected completedRiemannZetaPuncturedPlane :=
  completedRiemannZetaPuncturedPlane_isPathConnected.isConnected.isPreconnected

/-- Completed zeta is eventually differentiable at every point of its punctured
plane. -/
private theorem completedRiemannZeta_eventually_differentiableAt_puncturedPlane
    {w : ℂ}
    (hw : w ∈ completedRiemannZetaPuncturedPlane) :
    ∀ᶠ y in 𝓝 w, DifferentiableAt ℂ completedRiemannZeta y := by
  have hne :
      ∀ᶠ y in 𝓝 w, y ≠ 0 ∧ y ≠ 1 :=
    (eventually_ne_nhds hw.1).and (eventually_ne_nhds hw.2)
  exact hne.mono
    (fun y hy =>
      differentiableAt_completedZeta hy.1 hy.2)

/-- Completed zeta is analytic on its punctured plane. -/
private theorem completedRiemannZeta_analyticOnNhd_puncturedPlane :
    AnalyticOnNhd ℂ completedRiemannZeta completedRiemannZetaPuncturedPlane := by
  intro w hw
  exact Complex.analyticAt_iff_eventually_differentiableAt.2
    (completedRiemannZeta_eventually_differentiableAt_puncturedPlane hw)

/-- The punctured-plane neighborhood used to rule out local vanishing of
`completedRiemannZeta`. -/
private theorem completedRiemannZeta_eventuallyEq_zero_on_puncturedPlane
    (z : ℂ)
    (hz0 : z ≠ 0)
    (hz1 : z ≠ 1)
    (hzero : ∀ᶠ w in 𝓝 z, completedRiemannZeta w = 0) :
    Set.EqOn completedRiemannZeta (fun _ : ℂ => 0) completedRiemannZetaPuncturedPlane := by
  have hzU : z ∈ completedRiemannZetaPuncturedPlane :=
    mem_completedRiemannZetaPuncturedPlane_of_ne hz0 hz1
  exact
    AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (f := completedRiemannZeta)
      (U := completedRiemannZetaPuncturedPlane)
      completedRiemannZeta_analyticOnNhd_puncturedPlane
      completedRiemannZetaPuncturedPlane_isPreconnected
      hzU
      hzero

/-- The completed zeta is nonzero at `2`, which is enough to contradict
eventual vanishing. -/
private theorem completedRiemannZeta_nonzero_two :
    completedRiemannZeta (2 : ℂ) ≠ 0 := by
  intro hcompleted_zero
  have hproduct : riemannZeta (2 : ℂ) * Gammaℝ (2 : ℂ) = 0 :=
    completedRiemannZeta_two_eq_riemannZeta_mul_gamma.symm.trans hcompleted_zero
  exact riemannZeta_mul_Gammaℝ_two_ne_zero hproduct

/-- The completed zeta function is not identically zero on the punctured plane
`ℂ \ {0,1}`. -/
private theorem completedRiemannZeta_not_eventually_zero
    (z : ℂ)
    (hz0 : z ≠ 0)
    (hz1 : z ≠ 1) :
    ¬ ∀ᶠ w in 𝓝 z, completedRiemannZeta w = 0 := by
  intro hzero
  have hzeroU :
      Set.EqOn completedRiemannZeta (fun _ : ℂ => 0) completedRiemannZetaPuncturedPlane :=
    completedRiemannZeta_eventuallyEq_zero_on_puncturedPlane z hz0 hz1 hzero
  have htwo_mem : (2 : ℂ) ∈ completedRiemannZetaPuncturedPlane :=
    And.intro two_ne_zero (OfNat.ofNat_ne_one 2)
  exact completedRiemannZeta_nonzero_two (hzeroU htwo_mem)

/-- The owner-named completed zeta function is not locally identically zero away
from `0` and `1`. -/
theorem completedRiemannZetaFunction_not_eventually_zero
    (z : ℂ)
    (hz0 : z ≠ 0)
    (hz1 : z ≠ 1) :
    ¬ ∀ᶠ w in 𝓝 z, completedRiemannZetaFunction w = 0 := by
  intro hzero
  have hraw :
      ∀ᶠ w in 𝓝 z, completedRiemannZeta w = 0 :=
    hzero.mono
      (fun w hw =>
        (completedRiemannZetaFunction_eq w).symm.trans hw)
  exact completedRiemannZeta_not_eventually_zero z hz0 hz1 hraw

/-- Translating by the center then subtracting it tends to the original point. -/
theorem centered_sub_half_tendsto_nhds
    (z : ℂ) :
    Tendsto
      (fun s : ℂ => s - (1 / 2 : ℂ))
      (𝓝 ((1 / 2 : ℂ) + z))
      (𝓝 z) := by
  have hraw :
      Tendsto
        (fun s : ℂ => s - (1 / 2 : ℂ))
        (𝓝 ((1 / 2 : ℂ) + z))
        (𝓝 (((1 / 2 : ℂ) + z) - (1 / 2 : ℂ))) :=
    (continuous_id.sub continuous_const).continuousAt.tendsto
  exact Eq.subst
    (motive := fun u : ℂ =>
      Tendsto
        (fun s : ℂ => s - (1 / 2 : ℂ))
        (𝓝 ((1 / 2 : ℂ) + z))
        (𝓝 u))
    (complex_add_sub_half z)
    hraw

/-- A centered zero equation transported back to the owner-named completed zeta
coordinate. -/
theorem centered_zero_shift_to_completed_zero_function
    {s : ℂ}
    (hs : centeredCompletedRiemannZetaFunction (s - (1 / 2 : ℂ)) = 0) :
    completedRiemannZetaFunction s = 0 := by
  have hcenter : (1 / 2 : ℂ) + (s - (1 / 2 : ℂ)) = s :=
    complex_half_add_sub_half s
  have hcompleted :
      completedRiemannZetaFunction ((1 / 2 : ℂ) + (s - (1 / 2 : ℂ))) = 0 :=
    (centeredCompletedRiemannZetaFunction_eq_completedRiemannZetaFunction_shift
      (s - (1 / 2 : ℂ))).symm.trans hs
  exact hcenter ▸ hcompleted

/-- Eventual centered vanishing transports across the half-shift. -/
theorem centered_eventually_zero_shift_to_centered_pullback
    {z : ℂ}
    (hzero : ∀ᶠ w in 𝓝 z, centeredCompletedRiemannZetaFunction w = 0) :
    ∀ᶠ s in 𝓝 ((1 / 2 : ℂ) + z),
      centeredCompletedRiemannZetaFunction (s - (1 / 2 : ℂ)) = 0 := by
  exact (centered_sub_half_tendsto_nhds z).eventually hzero

/-- Eventual centered vanishing transports to eventual completed-zeta vanishing. -/
theorem centered_eventually_zero_shift_to_completed_eventually_zero
    {z : ℂ}
    (hzero_shift :
      ∀ᶠ s in 𝓝 ((1 / 2 : ℂ) + z),
        centeredCompletedRiemannZetaFunction (s - (1 / 2 : ℂ)) = 0) :
    ∀ᶠ s in 𝓝 ((1 / 2 : ℂ) + z), completedRiemannZetaFunction s = 0 := by
  exact hzero_shift.mono
    (fun s hs =>
      centered_zero_shift_to_completed_zero_function hs)

/-- Excluding the negative shifted pole excludes `0` after uncentering. -/
theorem centered_half_add_ne_zero_of_ne_negHalf
    {z : ℂ}
    (hzneg : z ≠ -(1 / 2 : ℂ)) :
    (1 / 2 : ℂ) + z ≠ 0 := by
  exact centeredShift_leftDenominator_ne_zero_of_ne_negHalf hzneg

/-- Excluding the positive shifted pole excludes `1` after uncentering. -/
theorem centered_half_add_ne_one_of_ne_posHalf
    {z : ℂ}
    (hzpos : z ≠ (1 / 2 : ℂ)) :
    (1 / 2 : ℂ) + z ≠ 1 := by
  intro hone
  have hright : 1 - ((1 / 2 : ℂ) + z) = 0 :=
    sub_eq_zero.mpr hone.symm
  exact centeredShift_rightDenominator_ne_zero_of_ne_posHalf hzpos hright

/-- Away from the shifted poles, the centered completed zeta function is not
locally identically zero at a zero. -/
theorem centeredCompletedRiemannZeta_not_eventually_zero_at_zero_of_ne_shiftedPoles
    {z : ℂ}
    (hzneg : z ≠ -(1 / 2 : ℂ))
    (hzpos : z ≠ (1 / 2 : ℂ)) :
    ¬ ∀ᶠ w in 𝓝 z, centeredCompletedRiemannZetaFunction w = 0 := by
  intro hzero
  have hs0 : (1 / 2 : ℂ) + z ≠ 0 := by
    exact centered_half_add_ne_zero_of_ne_negHalf hzneg
  have hs1 : (1 / 2 : ℂ) + z ≠ 1 := by
    exact centered_half_add_ne_one_of_ne_posHalf hzpos
  have hshift_zero :
      ∀ᶠ s in 𝓝 ((1 / 2 : ℂ) + z), completedRiemannZetaFunction s = 0 := by
    have hpullback :
        ∀ᶠ s in 𝓝 ((1 / 2 : ℂ) + z),
          centeredCompletedRiemannZetaFunction (s - (1 / 2 : ℂ)) = 0 :=
      centered_eventually_zero_shift_to_centered_pullback hzero
    exact centered_eventually_zero_shift_to_completed_eventually_zero hpullback
  exact completedRiemannZetaFunction_not_eventually_zero
    ((1 / 2 : ℂ) + z)
    hs0
    hs1
    hshift_zero

/-- The centered completed zeta function is not locally identically zero at a
completed zero. -/
theorem centeredCompletedRiemannZeta_not_eventually_zero_at_completedZero
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    ¬ ∀ᶠ z in 𝓝 (ρ : ℂ), centeredCompletedRiemannZetaFunction z = 0 := by
  exact centeredCompletedRiemannZeta_not_eventually_zero_at_zero_of_ne_shiftedPoles
    (zetaCompletedZero_ne_negHalf ρ)
    (zetaCompletedZero_ne_posHalf ρ)

/-- The pole-clearing denominator in centered coordinates. -/
def centeredCompletedRiemannZetaDenominator (w : ℂ) : ℂ :=
  ((1 / 2 : ℂ) + w) * (1 - ((1 / 2 : ℂ) + w))

/-- The product model for the cleared centered completed-zeta carrier. -/
def centeredCompletedRiemannZetaCarrierModel (w : ℂ) : ℂ :=
  centeredCompletedRiemannZetaDenominator w * centeredCompletedRiemannZetaFunction w

/-- The centered denominator is nonzero when both shifted pole factors are
nonzero. -/
theorem centeredCompletedRiemannZetaDenominator_ne_zero
    {w : ℂ}
    (hleft_w : (1 / 2 : ℂ) + w ≠ 0)
    (hright_w : 1 - ((1 / 2 : ℂ) + w) ≠ 0) :
    centeredCompletedRiemannZetaDenominator w ≠ 0 := by
  exact mul_ne_zero hleft_w hright_w

/-- The pointwise carrier factorization in named model form. -/
theorem centeredCompletedRiemannZetaZeroCarrier_eq_model
    {w : ℂ}
    (hleft_w : (1 / 2 : ℂ) + w ≠ 0)
    (hright_w : 1 - ((1 / 2 : ℂ) + w) ≠ 0) :
    centeredCompletedRiemannZetaZeroCarrier w =
      centeredCompletedRiemannZetaCarrierModel w := by
  have hraw :
      centeredCompletedRiemannZetaZeroCarrier w =
        ((1 / 2 : ℂ) + w) *
          (1 - ((1 / 2 : ℂ) + w)) *
            centeredCompletedRiemannZeta w :=
    centeredCompletedRiemannZetaZeroCarrier_eq_denominator_mul hleft_w hright_w
  calc
    centeredCompletedRiemannZetaZeroCarrier w =
        ((1 / 2 : ℂ) + w) *
          (1 - ((1 / 2 : ℂ) + w)) *
            centeredCompletedRiemannZeta w := hraw
    _ =
        ((1 / 2 : ℂ) + w) *
          (1 - ((1 / 2 : ℂ) + w)) *
            centeredCompletedRiemannZetaFunction w := by
      exact congrArg
        (fun u : ℂ =>
          ((1 / 2 : ℂ) + w) *
            (1 - ((1 / 2 : ℂ) + w)) * u)
        (centeredCompletedRiemannZetaFunction_eq w).symm
    _ = centeredCompletedRiemannZetaCarrierModel w := by
      rfl

/-- Near a completed zero, the cleared carrier is the nonzero clearing factor
times the centered completed zeta function. -/
theorem centeredCompletedRiemannZetaZeroCarrier_eventuallyEq_denominator_mul_core
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    centeredCompletedRiemannZetaZeroCarrier =ᶠ[𝓝 (ρ : ℂ)]
      centeredCompletedRiemannZetaCarrierModel := by
  have hleft_ne : (1 / 2 : ℂ) + (ρ : ℂ) ≠ 0 :=
    centeredShift_leftDenominator_ne_zero_of_ne_negHalf
      (zetaCompletedZero_ne_negHalf ρ)
  have hright_ne : 1 - ((1 / 2 : ℂ) + (ρ : ℂ)) ≠ 0 :=
    centeredShift_rightDenominator_ne_zero_of_ne_posHalf
      (zetaCompletedZero_ne_posHalf ρ)
  have hleft_eventual :
      ∀ᶠ w in 𝓝 (ρ : ℂ), (1 / 2 : ℂ) + w ≠ 0 :=
    ((continuous_const.add continuous_id).continuousAt).eventually_ne hleft_ne
  have hright_eventual :
      ∀ᶠ w in 𝓝 (ρ : ℂ), 1 - ((1 / 2 : ℂ) + w) ≠ 0 :=
    ((continuous_const.sub (continuous_const.add continuous_id)).continuousAt).eventually_ne
      hright_ne
  exact
    (hleft_eventual.and hright_eventual).mono
      (fun w hw =>
        centeredCompletedRiemannZetaZeroCarrier_eq_model hw.1 hw.2)

/-- Pointwise cancellation for the nonzero denominator in the cleared centered
zero carrier. -/
theorem centeredCompletedRiemannZeta_eq_zero_of_carrier_factor_eq_zero
    {w : ℂ}
    (hcarrier_w : centeredCompletedRiemannZetaZeroCarrier w = 0)
    (hfactor :
      centeredCompletedRiemannZetaZeroCarrier w =
        centeredCompletedRiemannZetaCarrierModel w)
    (hden_w : centeredCompletedRiemannZetaDenominator w ≠ 0) :
    centeredCompletedRiemannZetaFunction w = 0 := by
  have hproduct :
      centeredCompletedRiemannZetaCarrierModel w = 0 :=
    hfactor.symm.trans hcarrier_w
  have hmodel :
      centeredCompletedRiemannZetaDenominator w *
          centeredCompletedRiemannZetaFunction w = 0 :=
    hproduct
  match mul_eq_zero.mp hmodel with
  | Or.inl hden_zero => exact False.elim (hden_w hden_zero)
  | Or.inr hcenter_zero => exact hcenter_zero

/-- If the cleared carrier vanished locally at a completed zero, then the
centered completed zeta function would vanish locally there. -/
theorem centeredCompletedRiemannZeta_eventually_zero_of_carrier_eventually_zero
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (hcarrier_eventual :
      ∀ᶠ w in 𝓝 (ρ : ℂ), centeredCompletedRiemannZetaZeroCarrier w = 0) :
    ∀ᶠ w in 𝓝 (ρ : ℂ), centeredCompletedRiemannZetaFunction w = 0 := by
  have hleft_ne : (1 / 2 : ℂ) + (ρ : ℂ) ≠ 0 :=
    centeredShift_leftDenominator_ne_zero_of_ne_negHalf
      (zetaCompletedZero_ne_negHalf ρ)
  have hright_ne : 1 - ((1 / 2 : ℂ) + (ρ : ℂ)) ≠ 0 :=
    centeredShift_rightDenominator_ne_zero_of_ne_posHalf
      (zetaCompletedZero_ne_posHalf ρ)
  have hleft_eventual :
      ∀ᶠ w in 𝓝 (ρ : ℂ), (1 / 2 : ℂ) + w ≠ 0 :=
    ((continuous_const.add continuous_id).continuousAt).eventually_ne hleft_ne
  have hright_eventual :
      ∀ᶠ w in 𝓝 (ρ : ℂ), 1 - ((1 / 2 : ℂ) + w) ≠ 0 :=
    ((continuous_const.sub (continuous_const.add continuous_id)).continuousAt).eventually_ne
      hright_ne
  exact
    (hcarrier_eventual.and
      ((centeredCompletedRiemannZetaZeroCarrier_eventuallyEq_denominator_mul_core ρ).and
        (hleft_eventual.and hright_eventual))).mono
      (fun w hw =>
        have hden_w : centeredCompletedRiemannZetaDenominator w ≠ 0 :=
          centeredCompletedRiemannZetaDenominator_ne_zero
            hw.2.2.1
            hw.2.2.2
        centeredCompletedRiemannZeta_eq_zero_of_carrier_factor_eq_zero
          hw.1
          hw.2.1
          hden_w)

/-- The cleared zero carrier is not locally identically zero at a completed
zero. -/
theorem centeredCompletedRiemannZetaZeroCarrier_not_eventually_zero_at_completedZero
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    ¬ ∀ᶠ w in 𝓝 (ρ : ℂ), centeredCompletedRiemannZetaZeroCarrier w = 0 := by
  intro hcarrier_eventual
  have hcenter_eventual :
      ∀ᶠ w in 𝓝 (ρ : ℂ), centeredCompletedRiemannZetaFunction w = 0 :=
    centeredCompletedRiemannZeta_eventually_zero_of_carrier_eventually_zero
      ρ
      hcarrier_eventual
  exact centeredCompletedRiemannZeta_not_eventually_zero_at_completedZero ρ hcenter_eventual

/-- A completed zero has positive analytic multiplicity. -/
theorem zetaZeroMultiplicity_pos_of_completedZero
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    0 < zetaZeroMultiplicity (ρ : ℂ) := by
  have hanalytic :
      AnalyticAt ℂ centeredCompletedRiemannZetaZeroCarrier (ρ : ℂ) :=
    centeredCompletedRiemannZetaZeroCarrier_analyticAt (ρ : ℂ)
  have hleft_ne : (1 / 2 : ℂ) + (ρ : ℂ) ≠ 0 :=
    centeredShift_leftDenominator_ne_zero_of_ne_negHalf
      (zetaCompletedZero_ne_negHalf ρ)
  have hright_ne : 1 - ((1 / 2 : ℂ) + (ρ : ℂ)) ≠ 0 :=
    centeredShift_rightDenominator_ne_zero_of_ne_posHalf
      (zetaCompletedZero_ne_posHalf ρ)
  have hcarrier_zero :
      centeredCompletedRiemannZetaZeroCarrier (ρ : ℂ) = 0 :=
    have hzero_raw : centeredCompletedRiemannZeta (ρ : ℂ) = 0 :=
      (centeredCompletedRiemannZetaFunction_eq (ρ : ℂ)).symm.trans
        (zetaCompletedZero_zero ρ)
    centeredCompletedRiemannZetaZeroCarrier_eq_zero_of_completed_zero
      hleft_ne
      hright_ne
      hzero_raw
  have hcarrier_not :
      ¬ ∀ᶠ w in 𝓝 (ρ : ℂ), centeredCompletedRiemannZetaZeroCarrier w = 0 := by
    exact centeredCompletedRiemannZetaZeroCarrier_not_eventually_zero_at_completedZero ρ
  have horder_pos :
      0 < hanalytic.order.toNat :=
    analyticAt_order_toNat_pos_of_zero_not_eventually_zero
      hanalytic
      hcarrier_zero
      hcarrier_not
  exact horder_pos

/-- The centered zero coordinate. -/
def zetaCenteredZero (ρ : ℂ) : ℂ :=
  ρ - (1 / 2 : ℂ)

/-- Vertical height of a completed zero after centering. -/
noncomputable def zetaCompletedZeroCenteredHeight
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) : ℝ :=
  1 + ‖(zetaCenteredZero (ρ : ℂ)).im‖

/-- Completed-zero centered height is at least one. -/
theorem zetaCompletedZeroCenteredHeight_ge_one
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    1 ≤ zetaCompletedZeroCenteredHeight ρ := by
  exact le_add_of_nonneg_right (norm_nonneg ((zetaCenteredZero (ρ : ℂ)).im))

/-- Completed-zero centered height is positive. -/
theorem zetaCompletedZeroCenteredHeight_pos
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    0 < zetaCompletedZeroCenteredHeight ρ := by
  exact lt_of_lt_of_le zero_lt_one (zetaCompletedZeroCenteredHeight_ge_one ρ)

/-- Completed-zero centered height is nonzero. -/
theorem zetaCompletedZeroCenteredHeight_ne_zero
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    zetaCompletedZeroCenteredHeight ρ ≠ 0 := by
  exact ne_of_gt (zetaCompletedZeroCenteredHeight_pos ρ)

/-- Completed zeros in the centered vertical height ball of radius `T`. -/
def completedZerosInCenteredHeightBall (T : ℝ) :
    Set {ρ : ℂ // ZetaCompletedZero ρ} :=
  {ρ | zetaCompletedZeroCenteredHeight ρ ≤ T}

/-- The height-ball multiplicity summand. -/
noncomputable def completedZeroMultiplicityHeightBallSummand
    (T : ℝ) (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) : ℝ :=
  if zetaCompletedZeroCenteredHeight ρ ≤ T then
    (zetaZeroMultiplicity (ρ : ℂ) : ℝ)
  else
    0

/-- Completed-zero multiplicity count in a centered height ball. -/
noncomputable def completedZeroMultiplicityCountingInCenteredHeightBall
    (T : ℝ) : ℝ :=
  ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ},
    completedZeroMultiplicityHeightBallSummand T ρ

/-- The spectral transform of a test function. -/
def zetaSpectralTransform : ZetaTestFunction → ℂ → ℂ :=
  zetaLaplaceTransform

/-- The spectral evaluation of an admissible test function. -/
abbrev zetaSpectralEval (φ : ZetaAdmissibleFunction) (z : ℂ) : ℂ :=
  zetaSpectralTransform φ.toZetaTestFunction' z

/-- The spectral transform is the zeta Laplace transform. -/
theorem zetaSpectralTransform_eq_laplace
    (φ : ZetaTestFunction) :
    zetaSpectralTransform φ = Boundary.zetaLaplaceTransform φ := by
  exact Eq.refl _

/-- The spectral evaluation is the zeta Laplace transform evaluation. -/
theorem zetaSpectralEval_eq_laplace
    (φ : ZetaAdmissibleFunction) (z : ℂ) :
    zetaSpectralEval φ z = Boundary.zetaLaplaceTransform φ.toZetaTestFunction' z := by
  exact Eq.refl _

/-- The spectral evaluation of an autocorrelation is the constructed Laplace transform. -/
theorem zetaSpectralEval_autocorrelation
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    zetaSpectralTransform (ZetaAdmissibleFunction.autocorrelation f).toZetaTestFunction' z =
      Boundary.zetaLaplaceTransform
        (ZetaAdmissibleFunction.autocorrelation f).toZetaTestFunction' z := by
  exact Eq.refl _

/-- The single zero contribution to the completed zero side. -/
def zetaZeroSideContribution (ρ : ℂ) (φ : ZetaAdmissibleFunction) : ℂ :=
  - (zetaZeroMultiplicity ρ : ℂ) * zetaSpectralEval φ ρ

/-- The functional-equation orbit of a centered zero. -/
def zetaZeroOrbitFinset (ρ : ℂ) : Finset ℂ :=
  insert ρ <| insert (-ρ) ∅

/-- Membership in the centered zero orbit is membership in the two reflection faces. -/
theorem zetaZeroOrbitFinset_mem_iff (ρ η : ℂ) :
    η ∈ zetaZeroOrbitFinset ρ ↔ η = ρ ∨ η = -ρ := by
  constructor
  · intro hη
    exact
      match Finset.mem_insert.mp hη with
      | Or.inl hleft => Or.inl hleft
      | Or.inr hright =>
          have hneg : η = -ρ :=
            Finset.mem_singleton.mp hright
          Or.inr hneg
  · intro hη
    exact
      match hη with
      | Or.inl hleft => Finset.mem_insert.mpr (Or.inl hleft)
      | Or.inr hright =>
          Finset.mem_insert.mpr
            (Or.inr (Finset.mem_singleton.mpr hright))

/-- The centered zero orbit contains its positive face. -/
theorem zetaZeroOrbitFinset_mem_self (ρ : ℂ) :
    ρ ∈ zetaZeroOrbitFinset ρ := by
  exact (zetaZeroOrbitFinset_mem_iff ρ ρ).2 (Or.inl rfl)

/-- The centered zero orbit contains its reflected face. -/
theorem zetaZeroOrbitFinset_mem_neg (ρ : ℂ) :
    -ρ ∈ zetaZeroOrbitFinset ρ := by
  exact (zetaZeroOrbitFinset_mem_iff ρ (-ρ)).2 (Or.inr rfl)

/-- The orbit contribution attached to a centered zero. -/
def zetaZeroOrbitContribution (ρ : ℂ) (φ : ZetaAdmissibleFunction) : ℂ :=
  Finset.sum (zetaZeroOrbitFinset ρ) (fun η => zetaZeroSideContribution η φ)

/-- The zero tail away from a finite excluded set. -/
def zetaZeroTail (S : Finset ℂ) (φ : ZetaAdmissibleFunction) : ℂ :=
  tsum (fun η : {η : ℂ // ZetaCompletedZero η ∧ η ∉ S} =>
    zetaZeroSideContribution (η : ℂ) φ)

/-- The orbit remainder is the tail after removing the orbit of the chosen zero. -/
def zetaZeroOrbitRemainder (ρ : ℂ) (φ : ZetaAdmissibleFunction) : ℂ :=
  zetaZeroTail (zetaZeroOrbitFinset ρ) φ

/-- Real-valued projection of the single zero contribution. -/
def zetaZeroSideContributionRe (ρ : ℂ) (φ : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (zetaZeroSideContribution ρ φ)

/-- Real-valued projection of the orbit contribution. -/
def zetaZeroOrbitContributionRe (ρ : ℂ) (φ : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (zetaZeroOrbitContribution ρ φ)

/-- Real-valued projection of the zero tail. -/
def zetaZeroTailRe (S : Finset ℂ) (φ : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (zetaZeroTail S φ)

/-- Real-valued projection of the orbit remainder. -/
def zetaZeroOrbitRemainderRe (ρ : ℂ) (φ : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (zetaZeroOrbitRemainder ρ φ)

theorem zetaZeroSideContribution_def (ρ : ℂ) (φ : ZetaAdmissibleFunction) :
    zetaZeroSideContribution ρ φ =
      - (zetaZeroMultiplicity ρ : ℂ) * zetaSpectralEval φ ρ := by
  exact Eq.refl _

/-- The spectral transform of an autocorrelation is the constructed Laplace transform. -/
theorem zetaSpectralTransform_autocorrelation
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    zetaSpectralTransform (ZetaAdmissibleFunction.autocorrelation f).toZetaTestFunction' z =
      Boundary.zetaLaplaceTransform
        (ZetaAdmissibleFunction.autocorrelation f).toZetaTestFunction' z := by
  exact Eq.refl _

/-- The spectral transform is additive. -/
theorem zetaSpectralTransform_add
    (φ ψ : ZetaTestFunction) (z : ℂ)
    (hφ : Integrable (fun t : ℝ => φ t * Complex.exp (z * t)) (volume : Measure ℝ))
    (hψ : Integrable (fun t : ℝ => ψ t * Complex.exp (z * t)) (volume : Measure ℝ)) :
    zetaSpectralTransform (φ + ψ) z =
      zetaSpectralTransform φ z + zetaSpectralTransform ψ z := by
  exact Boundary.zetaLaplaceTransform_add φ ψ z hφ hψ

/-- The spectral transform is homogeneous under scalar multiplication. -/
theorem zetaSpectralTransform_smul
    (a : ℂ) (φ : ZetaTestFunction) (z : ℂ) :
    zetaSpectralTransform (a • φ) z = a * zetaSpectralTransform φ z := by
  exact Boundary.zetaLaplaceTransform_smul a φ z

/-- The spectral transform commutes with finite sums. -/
theorem zetaSpectralTransform_sum
    {α : Type*} [DecidableEq α] (s : Finset α) (φ : α → ZetaTestFunction) (z : ℂ)
    (h : ∀ a ∈ s, Integrable (fun t : ℝ => φ a t * Complex.exp (z * t)) (volume : Measure ℝ)) :
    zetaSpectralTransform (∑ a in s, φ a) z =
      ∑ a in s, zetaSpectralTransform (φ a) z := by
  exact Boundary.zetaLaplaceTransform_sum s φ z h

/-- The spectral transform of an autocorrelation is the explicit Laplace integral. -/
theorem zetaSpectralTransform_autocorrelation_eq_integral
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    zetaSpectralTransform (ZetaAdmissibleFunction.autocorrelation f).toZetaTestFunction' z =
      ∫ t : ℝ, (f t * star (f t)) * Complex.exp (z * t) := by
  exact Boundary.zetaLaplaceTransform_autocorrelation f z

/-- The spectral evaluation of an autocorrelation is the explicit Laplace integral. -/
theorem zetaSpectralEval_autocorrelation_eq_integral
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    zetaSpectralTransform (ZetaAdmissibleFunction.autocorrelation f).toZetaTestFunction' z =
      ∫ t : ℝ, (f t * star (f t)) * Complex.exp (z * t) := by
  exact Boundary.zetaLaplaceTransform_autocorrelation f z

theorem zetaZeroOrbitContribution_eq_sum (ρ : ℂ) (φ : ZetaAdmissibleFunction) :
    zetaZeroOrbitContribution ρ φ =
      Finset.sum (zetaZeroOrbitFinset ρ) (fun η => zetaZeroSideContribution η φ) := by
  exact Eq.refl _

theorem zetaZeroOrbitRemainder_eq_tail (ρ : ℂ) (φ : ZetaAdmissibleFunction) :
    zetaZeroOrbitRemainder ρ φ =
      zetaZeroTail (zetaZeroOrbitFinset ρ) φ := by
  exact Eq.refl _

theorem zetaZeroTail_def (S : Finset ℂ) (φ : ZetaAdmissibleFunction) :
    zetaZeroTail S φ =
      tsum (fun η : {η : ℂ // ZetaCompletedZero η ∧ η ∉ S} =>
        zetaZeroSideContribution (η : ℂ) φ) := by
  exact Eq.refl _

end
end LFunctions
end Boundary
