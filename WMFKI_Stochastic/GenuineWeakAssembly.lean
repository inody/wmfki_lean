import WMFKI_Stochastic.WeakResponseBridge

open MeasureTheory
open WMFKIExternalProbe
namespace WMFKIJointAssembly

/-- C3の二階Frechet微分境界から、実際のLaplacian境界を導く。 -/
theorem laplacian_bound_of_c3 {d : ℕ} {φ : EuclideanSpace ℝ (Fin d) → ℝ} {G H J : ℝ}
    (hφ : C3TestBounds d φ G H J) (x : EuclideanSpace ℝ (Fin d)) :
    |Laplacian.laplacian φ x| ≤ (d : ℝ)*H := by
  rw [euclidean_laplacian_trace]
  calc
    _ ≤ ∑ a, |fderiv ℝ (fderiv ℝ φ) x (EuclideanSpace.single a 1) (EuclideanSpace.single a 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : Fin d, H := by
      apply Finset.sum_le_sum
      intro a _
      have hh := (fderiv ℝ (fderiv ℝ φ) x).le_opNorm₂ (EuclideanSpace.single a 1) (EuclideanSpace.single a 1)
      have hb : |fderiv ℝ (fderiv ℝ φ) x (EuclideanSpace.single a 1) (EuclideanSpace.single a 1)| ≤
          ‖fderiv ℝ (fderiv ℝ φ) x‖ := by simpa [Real.norm_eq_abs] using hh
      exact hb.trans (hφ.second x)
    _ = _ := by simp

/-- 実際の観測サンプルと本物の微分から本番の組立入力を構成。
    モーメントやD0/V0を偽装するフィールドは追加しない。 -/
noncomputable def genuineWeakAssembly {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (N nt d nr nc : ℕ) (R q : ℝ) (hR : 0 ≤ R) (hq : 0 ≤ q)
    (O : ObservationSamples (E := EuclideanSpace ℝ (Fin d)) P N nt R q)
    (σ : ℝ) (w τ : Fin nt → ℝ) (ψ : Fin nr → ℝ → ℝ)
    (φ : Fin nr → EuclideanSpace ℝ (Fin d) → ℝ)
    (atom : Fin nc → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (B G H J C Cφ : ℝ) (hB : 0 ≤ B) (hG : 0 ≤ G) (hC : 0 ≤ C)
    (hφ : ∀ a, C3TestBounds d (φ a) G H J) (hφb : ∀ a x, |φ a x| ≤ Cφ)
    (hψ : ∀ a t, |ψ a (τ t)| ≤ B) (hAtom : ∀ m, Continuous (atom m))
    (hg : ∀ m x, ‖atom m x‖ ≤ C*(1+‖x‖)) :
    WMFKI.WeakAssemblyData (F := EuclideanSpace ℝ (Fin d)) P N nt nr nc where
  X := fun z i t => O.pos t i z
  noise := fun z i t => O.noise t i z
  φ := φ
  lap := fun a => Laplacian.laplacian (φ a)
  ψ := fun a t => ψ a (τ t)
  dψ := fun a t => deriv (ψ a) (τ t)
  g := fun a => gradient (φ a)
  Φ := atom
  w := w
  σ := σ
  RX := R
  Re := q
  B := B
  G := G
  K := C
  Cφ := Cφ
  Cl := (d : ℝ)*H
  hX := fun i t => O.pos_meas t i
  he := fun i t => O.noise_meas t i
  hiX := fun i t => (O.pos_lp t i).norm.integrable_sq
  hie := fun i t => (O.noise_lp t i).norm.integrable_sq
  hRX0 := hR
  hRe0 := hq
  hRX := fun i t => O.pos_moment t i
  hRe := fun i t => O.noise_moment t i
  hg := fun a => (euclidean_test_derivatives_continuous d (φ a) ((hφ a).smooth.of_le (by norm_num))).1
  hΦ := hAtom
  hφ := fun a => (hφ a).smooth.continuous
  hlap := fun a => (euclidean_test_derivatives_continuous d (φ a) ((hφ a).smooth.of_le (by norm_num))).2
  hB := hB
  hG := hG
  hK := hC
  hψ := hψ
  hgb := fun a => (hφ a).observation_bounds.1
  hΦb := hg
  hφb := hφb
  hlapb := fun a => laplacian_bound_of_c3 (hφ a)

end WMFKIJointAssembly
