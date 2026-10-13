import WMFKI_Stochastic.PrimitiveRecovery
import WMFKI_Stochastic.CanonicalBrownianFamilyProbe
import Lean_Code.FiniteSampling
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Real.Pi.Bounds

open MeasureTheory ProbabilityTheory Set
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
open WMFKIExternalProbe WMFKISynchronousModel WMFKIFeatureCoupling WMFKIPopulationDesign WMFKIObservedDesign
open scoped NNReal ENNReal
namespace WMFKIJointAssembly.HumanCheck
private abbrev E := EuclideanSpace ℝ (Fin 1)
private noncomputable local instance : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
private noncomputable local instance : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
private noncomputable local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
private noncomputable local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
private noncomputable def unit : E := WithLp.toLp 2 (fun _ => 1)
private theorem unit_norm : ‖unit‖ = 1 := by
  have h : ‖unit‖^2 = 1 := by rw [EuclideanSpace.real_norm_sq_eq];norm_num [unit,Fin.sum_univ_one]
  nlinarith [norm_nonneg unit]
private noncomputable def lin : E →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E unit
private theorem lin_norm : ‖lin‖ = 1 := by simp [lin,unit_norm]
private theorem lin_unit : lin unit = 1 := by
  change inner ℝ unit unit = 1
  rw [real_inner_self_eq_norm_sq,unit_norm]
  norm_num
private theorem unit_single : unit = EuclideanSpace.single (0 : Fin 1) 1 := by
  ext i
  fin_cases i
  rfl
private noncomputable def test (x : E) : ℝ := Real.sin (lin x)
private theorem test_first : fderiv ℝ test = fun x => Real.cos (lin x) • lin := by
  funext x
  exact lin.hasFDerivAt.sin.fderiv
private theorem smul_tensor (c : ℝ) : (c • lin).smulRight lin = c • lin.smulRight lin := by
  ext u v
  simp [smul_smul,mul_assoc]
private theorem test_second : fderiv ℝ (fderiv ℝ test) = fun x => -Real.sin (lin x) • lin.smulRight lin := by
  rw [test_first]
  funext x
  simpa only [smul_tensor] using (lin.hasFDerivAt.cos.smul_const lin).fderiv
private theorem test_third (x : E) : fderiv ℝ (fderiv ℝ (fderiv ℝ test)) x =
    (-Real.cos (lin x) • lin).smulRight (lin.smulRight lin) := by
  rw [test_second]
  simpa only [Pi.neg_apply,neg_smul] using (lin.hasFDerivAt.sin.neg.smul_const (lin.smulRight lin)).fderiv
private theorem test_bounds : C3TestBounds 1 test 1 1 1 := by
  constructor
  · exact lin.contDiff.sin
  · intro x
    rw [test_first]
    simpa [norm_smul,lin_norm,Real.norm_eq_abs] using Real.abs_cos_le_one (lin x)
  · intro x
    rw [test_second]
    simpa [norm_smul,ContinuousLinearMap.norm_smulRight_apply,lin_norm,Real.norm_eq_abs] using Real.abs_sin_le_one (lin x)
  · intro x
    rw [test_third]
    simpa [norm_smul,ContinuousLinearMap.norm_smulRight_apply,lin_norm,Real.norm_eq_abs] using Real.abs_cos_le_one (lin x)
private theorem test_bounded (x : E) : |test x| ≤ 1 := Real.abs_sin_le_one _
private theorem test_value (c : ℝ) : test (c • unit) = Real.sin c := by simp [test,lin_unit]
private theorem test_lap (x : E) : Laplacian.laplacian test x = -Real.sin (lin x) := by
  rw [euclidean_laplacian_trace,test_second]
  simp only [Fin.sum_univ_one,←unit_single]
  simp [lin_unit]
private theorem test_gradient (x : E) : gradient test x = Real.cos (lin x) • unit := by
  simp [gradient,test_first,lin]

/-- 空間試験は非定数・有界のsin。三階まで本物のFrechet微分を計算した。 -/
example : C3TestBounds 1 test 1 1 1 ∧ (∀ x, |test x| ≤ 1) ∧
    test ((Real.pi/2) • unit) = 1 ∧ gradient test 0 = unit ∧ Laplacian.laplacian test 0 = 0 := by
  refine ⟨test_bounds,test_bounded,?_,?_,?_⟩
  · simp [test_value]
  · simp [test_gradient]
  · simp [test_lap]

private noncomputable def bump : ContDiffBump (1/2 : ℝ) := ⟨1/8,1/4,by norm_num,by norm_num⟩
private noncomputable def ψ : ℝ → ℝ := bump
private theorem ψ_smooth : ContDiff ℝ 1 ψ := bump.contDiff
private theorem ψ_zero : ψ 0 = 0 := bump.zero_of_le_dist (by norm_num [bump,Real.dist_eq])
private theorem ψ_one : ψ 1 = 0 := bump.zero_of_le_dist (by norm_num [bump,Real.dist_eq])
private theorem ψ_mid : ψ (1/2) = 1 := bump.one_of_mem_closedBall (by simp [bump])
private theorem ψ_bounds : ∃ B : ℝ, 1 ≤ B ∧
    (∀ t ∈ Icc (0 : ℝ) 1, |ψ t| ≤ B) ∧ (∀ t ∈ Icc (0 : ℝ) 1, |deriv ψ t| ≤ B) := by
  obtain ⟨C,hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn ψ_smooth.continuous_deriv_one.continuousOn
  refine ⟨max 1 C,le_max_left _ _,?_,?_⟩
  · intro t _
    change |bump t| ≤ _
    rw [abs_of_nonneg bump.nonneg]
    exact (bump.le_one (x := t)).trans (le_max_left _ _)
  · intro t ht
    simpa only [Real.norm_eq_abs] using (hC t ht).trans (le_max_right 1 C)

/-- 時間試験も非零の滑らかなcompact bump。端点で0、導関数境界も区間上で構成する。 -/
example : ContDiff ℝ 1 ψ ∧ HasCompactSupport ψ ∧ ψ 0 = 0 ∧ ψ 1 = 0 ∧ ψ (1/2) = 1 ∧
    ∃ B : ℝ, 1 ≤ B ∧ (∀ t ∈ Icc (0 : ℝ) 1, |ψ t| ≤ B) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, |deriv ψ t| ≤ B) :=
  ⟨ψ_smooth,bump.hasCompactSupport,ψ_zero,ψ_one,ψ_mid,ψ_bounds⟩

/-- 本物のsinとLaplacianで拡散項の符号とsigma^2/2を検査。応答は2。 -/
example : discreteResponseVector 1 2 1 1 2 (fun _ => 2) (fun _ => 1) (fun _ => test) (fun _ => id)
      (fun _ _ (_z : Fin 1) => (Real.pi/2) • unit) 0 = WithLp.toLp 2 (fun _ => 2) ∧
    WMFKI.observedWeakResponse (fun (_z : Fin 1) (_i : Fin 2) (_t : Fin 1) => (Real.pi/2) • unit)
      (fun (_a : Fin 1) => test) (fun _ => Laplacian.laplacian test)
      (fun _ _ => 1) (fun _ _ => 1) (fun _ => 2) 2 0 0 = 2 := by
  have hv : discreteResponseVector 1 2 1 1 2 (fun _ => 2) (fun _ => 1) (fun _ => test) (fun _ => id)
      (fun _ _ (_z : Fin 1) => (Real.pi/2) • unit) 0 = WithLp.toLp 2 (fun _ => 2) := by
    ext a
    norm_num [discreteResponseVector,normalizedTestVector,discreteWeakResponse,particleTimeAverage,
      weakResponseIntegrand,Fin.sum_univ_one,Fin.sum_univ_two,test_value,test_lap,lin_unit]
  refine ⟨hv,?_⟩
  rw [weak_response_bridge] at hv
  have hh := congrArg (fun v : EuclideanSpace ℝ (Fin 1) => v 0) hv
  simpa using hh

private noncomputable def atom (x : E) : E := (‖x‖+2) • unit
private theorem atom_lipschitz : LipschitzWith 1 atom := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [atom,dist_eq_norm,← sub_smul,norm_smul,unit_norm,mul_one,NNReal.coe_one,one_mul]
  simpa only [add_sub_add_right_eq_sub,Real.norm_eq_abs] using abs_norm_sub_norm_le x y
private theorem atom_growth (x : E) : ‖atom x‖ ≤ 2*(1+‖x‖) := by
  rw [atom,norm_smul,unit_norm,mul_one,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  nlinarith [norm_nonneg x]
private noncomputable def θfull : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![0,1]
private theorem full_real (x : E) : ∑ m : Fin 2, θfull m • atom x = atom x := by
  simp [θfull,Fin.sum_univ_two]

/-- 二列中の後ろの一列を選ぶ。本物の特徴で非零残差-2を両表現で同定する。 -/
example :
    let h := WMFKI.observedPairFeature (fun (_z : Fin 1) (_i : Fin 2) (_t : Fin 1) => (0 : E))
      (fun (_a : Fin 1) _ => 1) (fun _ => gradient test) (fun (_m : Fin 2) => atom)
    let b := WMFKI.observedWeakResponse (fun (_z : Fin 1) (_i : Fin 2) (_t : Fin 1) => (0 : E))
      (fun (_a : Fin 1) => test) (fun _ => Laplacian.laplacian test)
      (fun _ _ => 1) (fun _ _ => 1) (fun _ => 2) 0
    WMFKI.fullRegressionResidual (WMFKI.selectPairFeatures h (fun (_ : Fin 1) => (1 : Fin 2))) (fun _ => 2) b (fun _ => 1) 0 =
      WMFKI.fullRegressionResidual h (fun _ => 2) b θfull 0 ∧
    WMFKI.fullRegressionResidual h (fun _ => 2) b θfull 0 = WithLp.toLp 2 (fun _ => -2) := by
  dsimp only
  have he := selected_residual_eq 1 2 1 1 2 1 0 (fun _ => 2) (fun _ => 1) (fun _ => test) (fun _ => id)
    (fun _ => atom) atom θfull full_real (fun _ => 1) (fun _ => 1) (by intro x;simp)
    (fun _ _ (_ : Fin 1) => 0) 0
  refine ⟨by simpa using he,?_⟩
  ext a
  norm_num [WMFKI.fullRegressionResidual,WMFKI.observedWeakResponse,WMFKI.fullPairDesign,
    WMFKI.observedPairFeature,test,test_lap,test_gradient,atom,unit_norm,θfull,
    Fin.sum_univ_one,Fin.sum_univ_two,WMFKI.orderedPair_card,real_inner_self_eq_norm_sq,inner_smul_right]

private noncomputable abbrev ν := WMFKI.uniformPopulation (Fin 2)
private noncomputable abbrev P0 : Measure (Fin 1) := Measure.dirac 0
private def value (z : Fin 2) : ℝ := (z.val : ℝ)+1
private theorem two_integral (f : Fin 2 → ℝ) : (∫ z, f z ∂ν) = (f 0+f 1)/2 := by
  rw [WMFKI.integral_uniformPopulation]
  norm_num [WMFKI.populationMean,Fin.sum_univ_two]

/-- 完全に共通で偏った雑音から、実sin微分を使う本番組立を構成。
    特徴モーメント156と応答L2は入力せず導く。応答も実際に非零。 -/
example : ∃ data : WMFKI.WeakAssemblyData (F := E) (P0.prod ν) 2 1 1 1,
    data.φ 0 = test ∧ data.g 0 = gradient test ∧ data.lap 0 = Laplacian.laplacian test ∧
    MemLp (fun z => data.response z 0) 2 (P0.prod ν) ∧
    (∀ a m t p, (∫ z, data.features z a m t p^2 ∂P0.prod ν) ≤ 156) ∧ 0 < data.response (0,0) 0 := by
  let O := independentObservationSamples P0 ν 2 1 0 3
    (fun _ _ _ => (0 : E)) (fun _ _ z => value z • unit)
    (fun _ _ => measurable_const) (fun _ _ => measurable_of_finite _) (fun _ _ => MemLp.of_discrete)
    (fun _ _ => MemLp.of_discrete) (by intros;simp)
    (by intros;rw [two_integral];norm_num [value,norm_smul,unit_norm])
  let data := genuineWeakAssembly (P0.prod ν) 2 1 1 1 1 0 3 (by norm_num) (by norm_num) O
    2 (fun _ => 1) (fun _ => 0) (fun _ _ => 1) (fun _ => test) (fun _ => atom)
    1 1 1 1 2 1 (by norm_num) (by norm_num) (by norm_num) (fun _ => test_bounds)
    (fun _ => test_bounded) (by intros;norm_num) (fun _ => atom_lipschitz.continuous) (fun _ => atom_growth)
  have hr := data.regular
  refine ⟨data,rfl,rfl,rfl,hr.2.2.2.1 0,?_,?_⟩
  · intro a m t p
    have hb := hr.2.2.2.2 a m t p
    norm_num [WMFKI.WeakAssemblyData.atomBound,WMFKI.WeakAssemblyData.radius,data,genuineWeakAssembly,WMFKI.featureMomentBound] at hb
    exact hb
  · have hv : data.response (0,0) 0 = 2*Real.sin 1 := by
      norm_num [WMFKI.WeakAssemblyData.response,WMFKI.WeakAssemblyData.observed,data,genuineWeakAssembly,O,
        independentObservationSamples,WMFKI.observedWeakResponse,Fin.sum_univ_one,Fin.sum_univ_two,test_lap,value,lin_unit]
    rw [hv]
    exact mul_pos (by norm_num) (Real.sin_pos_of_pos_of_lt_pi (by norm_num) (by linarith [Real.pi_gt_three]))

private noncomputable def initial (z : Fin 2) : E := (2*(z.val : ℝ)-1) • unit
private noncomputable def qA {Ω : Type*} (N nt : ℕ) (w τ : Fin nt → ℝ)
    (X : HalfClosedTime → Ω → Fin (N*1) → ℝ) (z : Ω) : Matrix (Fin 1) (Fin 1) ℝ :=
  discreteDictionaryDesign 1 N nt 1 1 w τ (fun _ => atom) (fun _ => test) (fun _ => ψ)
    (particleGrid N 1 nt τ X) z-continuousDictionaryDesign 1 N 1 1 (fun _ => atom) (fun _ => test) (fun _ => ψ) 1 X z
private noncomputable def qb {Ω : Type*} (N nt : ℕ) (w τ : Fin nt → ℝ)
    (X : HalfClosedTime → Ω → Fin (N*1) → ℝ) (z : Ω) : E :=
  discreteResponseVector 1 N nt 1 1 w τ (fun _ => test) (fun _ => ψ) (particleGrid N 1 nt τ X) z-
    continuousResponseVector 1 N 1 1 (fun _ => test) (fun _ => ψ) 1 X z

set_option maxHeartbeats 2400000 in
/-- Brownian内部構成、非Gaussian初期値、sigma=T=1、非有界非線形核、真の係数1。
    有界sin空間試験とcompact bump時間試験により、原始終点を全Nに適用する。
    RMS求積と回復証明書内の幾何・smallness・penalty条件は明示的に残る。 -/
example : ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (hP : IsProbabilityMeasure P),
    letI : IsProbabilityMeasure P := hP
    ∃ W : Fin 1 → ℝ≥0 → Ω → ℝ, (∀ j, IsBrownianReal (W j) P) ∧
    ∃ (B : ℝ) (Y : ℝ → Fin 2 × Ω → E) (R Rpos CA CV : ℝ),
      1 ≤ B ∧ ArrayNonlinearFamily ν P 1 atom initial
        (fun t z => WithLp.toLp 2 (fun j => W j (halfTimeReal (realTimeClamp t)) z.2)) Y R ∧
      ∀ N : ℕ, 0 < N →
      ∃ (BN : BrownianSystem (arrayMeasure ν P (Fin N)) (N*1))
        (X : HalfClosedTime → (Fin N → Fin 2) × (Fin N → Ω) → Fin (N*1) → ℝ),
        SynchronousParticlePair ν P W initial 1 1 atom Y BN X ∧
        ∀ (nt : ℕ) (w τ : Fin nt → ℝ), (∑ t, |w t|) ≤ 1 → (∀ t, τ t ∈ Icc 0 1) →
        ∀ (q e : ℝ), 0 ≤ q → 0 ≤ e → ∀ (ε : Fin nt → Fin N → Fin 2 → E),
        (∀ t i, Measurable (ε t i)) → (∀ t i, MemLp (ε t i) 2 ν) →
        (∀ t i, (∫ z, ‖ε t i z‖^2 ∂ν) ≤ q) →
        MemLp (fun z => (WithLp.toLp 2 (fun am : Fin 1 × Fin 1 => qA N nt w τ X z am.1 am.2) :
          EuclideanSpace ℝ (Fin 1 × Fin 1))) 2 (arrayMeasure ν P (Fin N)) →
        (∫ z, WMFKI.frobenius (qA N nt w τ X z)^2 ∂arrayMeasure ν P (Fin N)) ≤ e →
        MemLp (qb N nt w τ X) 2 (arrayMeasure ν P (Fin N)) →
        (∫ z, ‖qb N nt w τ X z‖^2 ∂arrayMeasure ν P (Fin N)) ≤ e →
        let Obs := fun z i t => particleGrid N 1 nt τ X t i z.1+ε t i z.2
        let h := WMFKI.observedPairFeature Obs (fun (_a : Fin 1) t => ψ (τ t)) (fun _ => gradient test) (fun (_m : Fin 1) => atom)
        let b := WMFKI.observedWeakResponse Obs (fun (_a : Fin 1) => test) (fun _ => Laplacian.laplacian test)
          (fun _ t => ψ (τ t)) (fun _ t => deriv ψ (τ t)) w 1
        RecoveryCertificate ((arrayMeasure ν P (Fin N)).prod ν) N nt 1 1 h b w unit
          (populationFeatureDesign (ν.prod P) 1 1 1 (fun _ => ψ) (fun _ => test) (fun _ => atom) Y)
          (CA*(1/(N : ℝ)+e+q)) (CV*(1/(N : ℝ)+e+q))
          (WMFKI.featureMomentBound B 1 2 (2*Rpos+2*q)) (WMFKI.featureMomentBound B 1 3 (2*Rpos+2*q)) (fun _ => atom) atom := by
  obtain ⟨Ω,m,P,hP,W,hW,hm,hI⟩ := WMFKIExternalProbe.exists_independent_brownian_family 1
  let := m
  let := hP
  obtain ⟨B,hB,hψ,hdψ⟩ := ψ_bounds
  obtain ⟨Y,R,Rpos,CA,CV,hy,_hRpos,_hCA,_hCV,hFamily⟩ := exists_particle_weak_recovery (Ξ := Fin 2) ν P W hW hm hI initial
    (measurable_of_finite _) MemLp.of_discrete 1 (by norm_num) 1 atom atom_lipschitz
    1 1 (by decide) (fun _ => ψ) (fun _ => test) (fun _ => atom) B 1 1 1 2 (by norm_num)
    (fun _ => test_bounds) (fun _ => ψ_smooth) (fun _ => hψ) (fun _ => hdψ) (fun _ => ψ_zero) (fun _ => ψ_one)
    (fun _ => atom_growth) (fun _ => atom_lipschitz) unit (by intro x;norm_num [Fin.sum_univ_one,unit])
    1 (fun _ => test_bounded) 1 1 (by norm_num)
  refine ⟨Ω,m,P,hP,W,hW,B,Y,R,Rpos,CA,CV,hB,?_,fun N hN => ?_⟩
  · simpa only [one_smul] using hy
  · obtain ⟨BN,X,hs,_hpos,hRec⟩ := hFamily N hN
    refine ⟨BN,X,hs,?_⟩
    intro nt w τ hw hτ q e hq he ε hεm hεl hεq hqa hQa hqb hQb
    have hh := hRec nt w τ hw hτ ν q hq ε hεm hεl hεq e he hqa (by simpa only [qA,one_mul] using hQa) hqb (by simpa only [qb,one_mul] using hQb)
    have hKo : ‖atom 0‖ = 2 := by norm_num [atom,norm_smul,unit_norm]
    simpa only [one_pow,hKo,NNReal.coe_one,show (2 : ℝ)+1=3 by norm_num] using hh.2.2.2

end WMFKIJointAssembly.HumanCheck
