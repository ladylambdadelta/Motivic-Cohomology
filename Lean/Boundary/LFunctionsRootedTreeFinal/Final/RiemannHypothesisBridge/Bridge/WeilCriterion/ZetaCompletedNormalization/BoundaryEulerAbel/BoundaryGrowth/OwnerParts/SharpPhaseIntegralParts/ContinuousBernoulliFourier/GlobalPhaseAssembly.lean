import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.SharpPhaseIntegralParts.ContinuousBernoulliFourier.NatIocReindex
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Core.Owner

/-!
# Identification of global Bernoulli phase blocks with local unit coordinates
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

/-- The zero Fourier mode is exactly the positive-real logarithmic phase in
the translated unit coordinate. -/
theorem boundaryLineOnePointRealParam_zeroModeOscillation_eq_logarithmicPhaseFunction
    (t : ℝ)
    (a : ℕ)
    (u : ℝ) :
    Complex.realPhaseOscillation
        (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 a) u =
      boundaryLineOnePointRealParam_logarithmicPhaseFunction t ((a : ℝ) + u) := by
  have hzeroCast : ((0 : ℤ) : ℝ) = 0 :=
    Int.cast_zero
  have hangular : 2 * Real.pi * ((0 : ℤ) : ℝ) * u = 0 := by
    exact Eq.trans
      (congrArg (fun r : ℝ => 2 * Real.pi * r * u) hzeroCast)
      (Eq.trans
        (congrArg (fun r : ℝ => r * u) (mul_zero (2 * Real.pi)))
        (zero_mul u))
  let logarithm : ℂ := (Real.log ((a : ℝ) + u) : ℂ)
  have hcastProduct :
      ((t * Real.log ((a : ℝ) + u) : ℝ) : ℂ) = (t : ℂ) * logarithm :=
    map_mul Complex.ofRealHom t (Real.log ((a : ℝ) + u))
  have hexponent :
      Complex.I *
          ((boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 a u : ℝ) : ℂ) =
        (-(t : ℂ) * Complex.I) * logarithm := by
    unfold boundaryLineOnePointRealParam_unitBlockCombinedPhase
    have hphase :
        2 * Real.pi * ((0 : ℤ) : ℝ) * u -
            t * Real.log ((a : ℝ) + u) =
          -(t * Real.log ((a : ℝ) + u)) :=
      Eq.trans
        (congrArg
          (fun r : ℝ => r - t * Real.log ((a : ℝ) + u))
          hangular)
        (zero_sub (t * Real.log ((a : ℝ) + u)))
    have hcastPhase := congrArg (fun r : ℝ => (r : ℂ)) hphase
    have hcastNegative :
        ((-(t * Real.log ((a : ℝ) + u)) : ℝ) : ℂ) =
          -((t : ℂ) * logarithm) :=
      Eq.trans
        (map_neg Complex.ofRealHom (t * Real.log ((a : ℝ) + u)))
        (congrArg Neg.neg hcastProduct)
    exact Eq.trans
      (congrArg (fun z : ℂ => Complex.I * z)
        (Eq.trans hcastPhase hcastNegative))
      (calc
        Complex.I * (-((t : ℂ) * logarithm)) =
            -(Complex.I * ((t : ℂ) * logarithm)) :=
          mul_neg Complex.I ((t : ℂ) * logarithm)
        _ = -((Complex.I * (t : ℂ)) * logarithm) :=
          congrArg Neg.neg (mul_assoc Complex.I (t : ℂ) logarithm).symm
        _ = -(((t : ℂ) * Complex.I) * logarithm) := by
          exact congrArg (fun z : ℂ => -(z * logarithm))
            (mul_comm Complex.I (t : ℂ))
        _ = (-(t : ℂ) * Complex.I) * logarithm := by
          exact Eq.trans
            (neg_mul ((t : ℂ) * Complex.I) logarithm).symm
            (congrArg (fun z : ℂ => z * logarithm)
              (neg_mul (t : ℂ) Complex.I).symm))
  unfold Complex.realPhaseOscillation
  unfold boundaryLineOnePointRealParam_logarithmicPhaseFunction
  exact congrArg Complex.exp hexponent

/-- One Bernoulli-weighted positive-real phase block is its affine unit-block
coordinate integral.  The endpoint discrepancy of the sawtooth is removed by
the null equality `Ioo 0 1 =ᵐ Ioc 0 1`. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseBlock_eq_unitBlock
    (t : ℝ)
    {a : ℕ}
    (ha : ⌊2 + ‖t‖⌋₊ ≤ a) :
    (∫ x in Set.Ioc (a : ℝ) ((a + 1 : ℕ) : ℝ),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((x : ℂ) ^ (-(t : ℂ) * Complex.I))) =
      (∫ u in (0 : ℝ)..1,
        Complex.realPhaseOscillation
            (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 a) u *
          ((u - 1 / 2 : ℝ) : ℂ)) := by
  let global : ℝ → ℂ := fun x =>
    ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
      ((x : ℂ) ^ (-(t : ℂ) * Complex.I))
  let localBlock : ℝ → ℂ := fun u =>
    Complex.realPhaseOscillation
        (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 a) u *
      ((u - 1 / 2 : ℝ) : ℂ)
  have hle : (a : ℝ) ≤ ((a + 1 : ℕ) : ℝ) :=
    Nat.cast_le.mpr (Nat.le_succ a)
  have hupper : (a : ℝ) + 1 = ((a + 1 : ℕ) : ℝ) :=
    Eq.trans
      (congrArg (fun r : ℝ => (a : ℝ) + r)
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ)))
      (Nat.cast_add a 1).symm
  have htranslate :
      (∫ u in (0 : ℝ)..1, global ((a : ℝ) + u)) =
        ∫ x in (a : ℝ)..((a + 1 : ℕ) : ℝ), global x := by
    exact Eq.trans
      (intervalIntegral.integral_comp_add_left global (a : ℝ))
      (congrArg₂
        (fun left right : ℝ => ∫ x in left..right, global x)
        (add_zero (a : ℝ)) hupper)
  have hae :
      (fun u : ℝ => global ((a : ℝ) + u)) =ᵐ[
        volume.restrict (Set.Ioc (0 : ℝ) 1)] localBlock := by
    have hinterior :
        (fun u : ℝ => global ((a : ℝ) + u)) =ᵐ[
          volume.restrict (Set.Ioo (0 : ℝ) 1)] localBlock := by
      exact ae_restrict_of_forall_mem measurableSet_Ioo (fun u hu => by
        have hxpos :=
          boundaryLineOnePointRealParam_unitBlock_coordinate_pos t ha hu.1.le
        have hbernoulli :=
          eulerMaclaurinFirstPeriodicBernoulli_natAdd_eq_affine a hu.1.le hu.2
        have hoscillator :=
          boundaryLineOnePointRealParam_zeroModeOscillation_eq_logarithmicPhaseFunction
            t a u
        have hcpow :=
          boundaryLineOnePointRealParam_logarithmicPhaseFunction_eq_cpow_of_pos
            t hxpos
        unfold global
        unfold localBlock
        exact Eq.trans
          (congrArg₂ Mul.mul
            (congrArg (fun r : ℝ => (r : ℂ)) hbernoulli)
            (Eq.trans hcpow.symm hoscillator.symm))
          (mul_comm ((u - 1 / 2 : ℝ) : ℂ)
            (Complex.realPhaseOscillation
              (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 a) u)))
    exact ae_restrict_of_ae_eq_of_ae_restrict Ioo_ae_eq_Ioc hinterior
  have hlocalCongruence :
      (∫ u in (0 : ℝ)..1, global ((a : ℝ) + u)) =
        ∫ u in (0 : ℝ)..1, localBlock u := by
    have hambient := (ae_restrict_iff' measurableSet_Ioc).mp hae
    exact intervalIntegral.integral_congr_ae
      (hambient.mono (fun u hu huInterval =>
        hu
          (Eq.subst
            (motive := fun s : Set ℝ => u ∈ s)
            (Set.uIoc_of_le zero_le_one)
            huInterval)))
  exact Eq.trans
    (intervalIntegral.integral_of_le hle).symm
    (Eq.trans htranslate.symm hlocalCongruence)

/-- The global phase-block sum is the zero-based sum of affine unit-block
integrals. -/
theorem sum_boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseBlock_eq_localRange
    (t : ℝ)
    {C K : ℕ}
    (hC : ⌊2 + ‖t‖⌋₊ ≤ C)
    (hK : C ≤ K) :
    (∑ n ∈ Finset.Ioc C K,
      ∫ x in Set.Ioc ((n - 1 : ℕ) : ℝ) (n : ℝ),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((x : ℂ) ^ (-(t : ℂ) * Complex.I))) =
      (∑ k ∈ Finset.range (K - C),
        ∫ u in (0 : ℝ)..1,
          Complex.realPhaseOscillation
              (boundaryLineOnePointRealParam_unitBlockCombinedPhase
                t 0 (C + k)) u *
            ((u - 1 / 2 : ℝ) : ℂ)) := by
  let block : ℕ → ℂ := fun n =>
    ∫ x in Set.Ioc ((n - 1 : ℕ) : ℝ) (n : ℝ),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        ((x : ℂ) ^ (-(t : ℂ) * Complex.I))
  let localBlock : ℕ → ℂ := fun k =>
    ∫ u in (0 : ℝ)..1,
      Complex.realPhaseOscillation
          (boundaryLineOnePointRealParam_unitBlockCombinedPhase
            t 0 (C + k)) u *
        ((u - 1 / 2 : ℝ) : ℂ)
  have hupper : C + (K - C) = K :=
    Nat.add_sub_of_le hK
  have hreindex := sum_Ioc_add_eq_sum_range_add_succ block C (K - C)
  have hdomain :
      (∑ n ∈ Finset.Ioc C K, block n) =
        ∑ n ∈ Finset.Ioc C (C + (K - C)), block n :=
    congrArg
      (fun upper : ℕ => ∑ n ∈ Finset.Ioc C upper, block n)
      hupper.symm
  have hlocal :
      ∀ k ∈ Finset.range (K - C), block (C + k + 1) = localBlock k := by
    intro k _hk
    have hleft : C + k + 1 - 1 = C + k :=
      Nat.succ_sub_one (C + k)
    have hcutoff : ⌊2 + ‖t‖⌋₊ ≤ C + k :=
      le_trans hC (Nat.le_add_right C k)
    unfold block
    unfold localBlock
    exact Eq.trans
      (congrArg
        (fun left : ℕ =>
          ∫ x in Set.Ioc (left : ℝ) (C + k + 1 : ℕ),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              ((x : ℂ) ^ (-(t : ℂ) * Complex.I)))
        hleft)
      (boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseBlock_eq_unitBlock
        t hcutoff)
  exact Eq.trans hdomain
    (Eq.trans hreindex
      (Finset.sum_congr rfl hlocal))

end
end LFunctions
end Boundary
