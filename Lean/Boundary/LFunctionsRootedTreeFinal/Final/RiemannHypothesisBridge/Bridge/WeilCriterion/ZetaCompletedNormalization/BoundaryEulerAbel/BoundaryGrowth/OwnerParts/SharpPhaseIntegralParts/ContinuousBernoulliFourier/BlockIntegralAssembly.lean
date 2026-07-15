import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.SharpPhaseIntegralParts.ContinuousBernoulliFourier.BlockTranslation

/-!
# Assembly of translated centered unit-block integrals
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

/-- The centered derivative integrand in the single global coordinate based at
the canonical left endpoint. -/
noncomputable def boundaryLineOnePointRealParam_globalCenteredDerivativeIntegrand
    (t : ℝ)
    (C : ℕ)
    (x : ℝ) : ℂ :=
  (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t C x *
    Complex.realPhaseOscillation
      (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 C) x) *
    periodicCenteredQuadraticPrimitive x

/-- A local centered block integral is the corresponding interval of the
single global-coordinate integrand. -/
theorem intervalIntegral_boundaryLineOnePointRealParam_localCentered_eq_globalBlock
    (t : ℝ)
    (C k : ℕ) :
    (∫ u in (0 : ℝ)..1,
        (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude
            t (C + k) u *
          Complex.realPhaseOscillation
            (boundaryLineOnePointRealParam_unitBlockCombinedPhase
              t 0 (C + k)) u) *
          eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitiveComplex u) =
      ∫ x in ((k : ℕ) : ℝ)..(((k + 1 : ℕ) : ℕ) : ℝ),
        boundaryLineOnePointRealParam_globalCenteredDerivativeIntegrand t C x := by
  let F : ℝ → ℂ :=
    boundaryLineOnePointRealParam_globalCenteredDerivativeIntegrand t C
  have hlocalToShifted :
      (∫ u in (0 : ℝ)..1,
          (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude
              t (C + k) u *
            Complex.realPhaseOscillation
              (boundaryLineOnePointRealParam_unitBlockCombinedPhase
                t 0 (C + k)) u) *
            eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitiveComplex u) =
        ∫ u in (0 : ℝ)..1, F ((k : ℝ) + u) := by
    exact intervalIntegral.integral_congr
      (fun u hu =>
        have huIcc : u ∈ Set.Icc (0 : ℝ) 1 :=
          Eq.subst
            (motive := fun s : Set ℝ => u ∈ s)
            (Set.uIcc_of_le zero_le_one)
            hu
        boundaryLineOnePointRealParam_centeredDerivativeIntegrand_natAdd
          t C k huIcc)
  have htranslated :
      (∫ u in (0 : ℝ)..1, F ((k : ℝ) + u)) =
        ∫ x in ((k : ℝ) + 0)..((k : ℝ) + 1), F x :=
    intervalIntegral.integral_comp_add_left F (k : ℝ)
  have hleft : (k : ℝ) + 0 = (((k : ℕ) : ℝ)) :=
    add_zero (k : ℝ)
  have hright :
      (k : ℝ) + 1 = (((k + 1 : ℕ) : ℕ) : ℝ) := by
    exact Eq.trans
      (congrArg (fun r : ℝ => (k : ℝ) + r)
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ)))
      (Nat.cast_add k 1).symm
  exact Eq.trans hlocalToShifted
    (Eq.trans htranslated
      (congrArg₂
        (fun a b : ℝ => ∫ x in a..b, F x)
        hleft hright))

/-- The global centered derivative integrand is interval-integrable on each
natural unit block after the cutoff. -/
theorem intervalIntegrable_boundaryLineOnePointRealParam_globalCenteredDerivativeIntegrand_natBlock
    (t : ℝ)
    {C : ℕ}
    (hC : ⌊2 + ‖t‖⌋₊ ≤ C)
    (k : ℕ) :
    IntervalIntegrable
      (boundaryLineOnePointRealParam_globalCenteredDerivativeIntegrand t C)
      volume
      ((k : ℕ) : ℝ)
      (((k + 1 : ℕ) : ℕ) : ℝ) := by
  let F : ℝ → ℂ :=
    boundaryLineOnePointRealParam_globalCenteredDerivativeIntegrand t C
  let G : ℝ → ℂ := fun u =>
    (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude
        t (C + k) u *
      Complex.realPhaseOscillation
        (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 (C + k)) u) *
      eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitiveComplex u
  have hCk : ⌊2 + ‖t‖⌋₊ ≤ C + k :=
    le_trans hC (Nat.le_add_right C k)
  have hG : IntervalIntegrable G volume 0 1 :=
    intervalIntegrable_boundaryLineOnePointRealParam_zeroModeDerivative_mul_centeredPrimitive
      t hCk
  have hshifted :
      IntervalIntegrable (fun u : ℝ => F ((k : ℝ) + u)) volume 0 1 := by
    exact hG.congr
      (ae_restrict_of_forall_mem measurableSet_uIoc (fun u hu =>
        have huIoc : u ∈ Set.Ioc (0 : ℝ) 1 :=
          Eq.subst
            (motive := fun s : Set ℝ => u ∈ s)
            (Set.uIoc_of_le zero_le_one)
            hu
        boundaryLineOnePointRealParam_centeredDerivativeIntegrand_natAdd
          t C k (Set.Ioc_subset_Icc_self huIoc)))
  have hback :
      IntervalIntegrable
        (fun x : ℝ => F ((k : ℝ) + (x - (k : ℝ))))
        volume (0 + (k : ℝ)) (1 + (k : ℝ)) :=
    hshifted.comp_sub_right (k : ℝ)
  have hbackF :
      IntervalIntegrable F volume (0 + (k : ℝ)) (1 + (k : ℝ)) := by
    exact hback.congr
      (ae_restrict_of_forall_mem measurableSet_uIoc (fun x _hx =>
        congrArg F
          (Eq.trans
            (add_sub_assoc (k : ℝ) x (k : ℝ)).symm
            (add_sub_cancel_left (k : ℝ) x))))
  have hleft : (0 : ℝ) + (k : ℝ) = ((k : ℕ) : ℝ) :=
    zero_add (k : ℝ)
  have hright :
      (1 : ℝ) + (k : ℝ) = (((k + 1 : ℕ) : ℕ) : ℝ) := by
    exact Eq.trans
      (add_comm (1 : ℝ) (k : ℝ))
      (Eq.trans
        (congrArg (fun r : ℝ => (k : ℝ) + r)
          (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ)))
        (Nat.cast_add k 1).symm)
  exact Eq.subst
    (motive := fun a : ℝ =>
      IntervalIntegrable F volume a (((k + 1 : ℕ) : ℕ) : ℝ))
    hleft
    (Eq.subst
      (motive := fun b : ℝ =>
        IntervalIntegrable F volume (0 + (k : ℝ)) b)
      hright
      hbackF)

/-- The finite sum of local centered integrals is one global Fourier-owner
integral over the full translated length. -/
theorem sum_intervalIntegral_boundaryLineOnePointRealParam_localCentered_eq_global
    (t : ℝ)
    {C : ℕ}
    (hC : ⌊2 + ‖t‖⌋₊ ≤ C)
    (D : ℕ) :
    (∑ k ∈ Finset.range D,
      ∫ u in (0 : ℝ)..1,
        (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude
            t (C + k) u *
          Complex.realPhaseOscillation
            (boundaryLineOnePointRealParam_unitBlockCombinedPhase
              t 0 (C + k)) u) *
          eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitiveComplex u) =
      ∫ x in (0 : ℝ)..(D : ℝ),
        boundaryLineOnePointRealParam_globalCenteredDerivativeIntegrand t C x := by
  have hlocal :
      ∀ k ∈ Finset.range D,
        (∫ u in (0 : ℝ)..1,
            (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude
                t (C + k) u *
              Complex.realPhaseOscillation
                (boundaryLineOnePointRealParam_unitBlockCombinedPhase
                  t 0 (C + k)) u) *
              eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitiveComplex u) =
          ∫ x in (k : ℝ)..((k + 1 : ℕ) : ℝ),
            boundaryLineOnePointRealParam_globalCenteredDerivativeIntegrand t C x :=
    fun k _hk =>
      intervalIntegral_boundaryLineOnePointRealParam_localCentered_eq_globalBlock
        t C k
  have hsumCongruence :
      (∑ k ∈ Finset.range D,
        ∫ u in (0 : ℝ)..1,
          (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude
              t (C + k) u *
            Complex.realPhaseOscillation
              (boundaryLineOnePointRealParam_unitBlockCombinedPhase
                t 0 (C + k)) u) *
            eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitiveComplex u) =
        ∑ k ∈ Finset.range D,
          ∫ x in (k : ℝ)..((k + 1 : ℕ) : ℝ),
            boundaryLineOnePointRealParam_globalCenteredDerivativeIntegrand t C x :=
    Finset.sum_congr rfl hlocal
  have hadjacent :
      (∑ k ∈ Finset.range D,
          ∫ x in (k : ℝ)..((k + 1 : ℕ) : ℝ),
            boundaryLineOnePointRealParam_globalCenteredDerivativeIntegrand t C x) =
        ∫ x in ((0 : ℕ) : ℝ)..((D : ℕ) : ℝ),
          boundaryLineOnePointRealParam_globalCenteredDerivativeIntegrand t C x :=
    intervalIntegral.sum_integral_adjacent_intervals
      (f := boundaryLineOnePointRealParam_globalCenteredDerivativeIntegrand t C)
      (a := fun k : ℕ => (k : ℝ))
      (n := D)
      (fun k hk =>
        intervalIntegrable_boundaryLineOnePointRealParam_globalCenteredDerivativeIntegrand_natBlock
          t hC k)
  have hzero : ((0 : ℕ) : ℝ) = 0 :=
    Nat.cast_zero
  have hfinal :
      (∫ x in ((0 : ℕ) : ℝ)..((D : ℕ) : ℝ),
          boundaryLineOnePointRealParam_globalCenteredDerivativeIntegrand t C x) =
        ∫ x in (0 : ℝ)..(D : ℝ),
          boundaryLineOnePointRealParam_globalCenteredDerivativeIntegrand t C x :=
    congrArg
      (fun left : ℝ =>
        ∫ x in left..(D : ℝ),
          boundaryLineOnePointRealParam_globalCenteredDerivativeIntegrand t C x)
      hzero
  exact Eq.trans hsumCongruence (Eq.trans hadjacent hfinal)

end
end LFunctions
end Boundary
