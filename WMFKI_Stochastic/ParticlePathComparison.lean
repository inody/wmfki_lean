import WMFKI_Stochastic.ParticleDriftProbe
import FullAuditChapter4Gronwall

open MeasureTheory Set
open scoped BigOperators
namespace WMFKIExternalProbe

/-- A dimension-free component comparison. The particle average is bounded first;
no maximum over particle labels and no factor N is introduced. -/
theorem particle_path_comparison {N : ℕ} (hN : 0 < N)
    (u : Fin N → ℝ → ℝ) (a : Fin N → ℝ) (g T : ℝ)
    (hg : 0 < g) (hT : 0 ≤ T)
    (hc : ∀ i, ContinuousOn (u i) (Icc 0 T))
    (ha : ∀ i, 0 ≤ a i)
    (hb : ∀ i t, t ∈ Icc 0 T → u i t ≤ a i + g *
      ∫ s in 0..t, u i s + (N : ℝ)⁻¹ * ∑ j, u j s) :
    ∀ i t, t ∈ Icc 0 T → u i t ≤
      (a i + g*T*((N : ℝ)⁻¹ * ∑ j, a j)*Real.exp (2*g*T))*Real.exp (g*T) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  let m := fun t => (N : ℝ)⁻¹ * ∑ i, u i t
  let av := (N : ℝ)⁻¹ * ∑ i, a i
  have hav : 0 ≤ av := mul_nonneg (le_of_lt (inv_pos.mpr hn)) (Finset.sum_nonneg fun i _ => ha i)
  have hmc : ContinuousOn m (Icc 0 T) :=
    (continuousOn_finsetSum _ (fun i _ => hc i)).const_mul _
  have hi i t (ht : t ∈ Icc 0 T) : IntervalIntegrable (u i) volume 0 t :=
    ContinuousOn.intervalIntegrable_of_Icc ht.1 ((hc i).mono (Icc_subset_Icc le_rfl ht.2))
  have hmi t (ht : t ∈ Icc 0 T) : IntervalIntegrable m volume 0 t :=
    ContinuousOn.intervalIntegrable_of_Icc ht.1 (hmc.mono (Icc_subset_Icc le_rfl ht.2))
  have hmeq t (ht : t ∈ Icc 0 T) :
      (∫ s in 0..t, m s) = (N : ℝ)⁻¹ * ∑ i, ∫ s in 0..t, u i s := by
    dsimp only [m]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum]
    exact fun i _ => hi i t ht
  have hmb t (ht : t ∈ Icc 0 T) : m t ≤ av + (2*g) * ∫ s in 0..t, m s := by
    have hb' i : u i t ≤ a i + g * (∫ s in 0..t, u i s) + g * (∫ s in 0..t, m s) := by
      have hh := hb i t ht
      change u i t ≤ a i + g * (∫ s in 0..t, u i s + m s) at hh
      rw [intervalIntegral.integral_add (hi i t ht) (hmi t ht)] at hh
      nlinarith only [hh]
    have hh := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s := Finset.univ) fun i _ => hb' i)
      (le_of_lt (inv_pos.mpr hn))
    change m t ≤ _ at hh
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
    rw [hmeq t ht] at hh ⊢
    dsimp only [av]
    convert hh using 1
    field_simp
    ring
  have hmbound s (hs : s ∈ Icc 0 T) : m s ≤ av * Real.exp (2*g*T) := by
    apply (Asakura.FullAudit.ch4_gronwall_written m av (2*g) T hT hmc (by positivity) hmb s hs).trans
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hs.2 (by positivity))) hav
  have hmint t (ht : t ∈ Icc 0 T) : (∫ s in 0..t, m s) ≤ T*(av*Real.exp (2*g*T)) := by
    have hh := intervalIntegral.integral_mono_on ht.1 (hmi t ht)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => av*Real.exp (2*g*T)) volume 0 t)
      (fun s hs => hmbound s ⟨hs.1,hs.2.trans ht.2⟩)
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right ht.2 (mul_nonneg hav (le_of_lt (Real.exp_pos _))))
  intro i t ht
  let A := a i + g*T*av*Real.exp (2*g*T)
  have hA : 0 ≤ A := by
    have hai := ha i
    dsimp [A]
    positivity
  have hbi s (hs : s ∈ Icc 0 T) : u i s ≤ A + g * ∫ r in 0..s, u i r := by
    have hh := hb i s hs
    change u i s ≤ a i + g * (∫ r in 0..s, u i r + m r) at hh
    rw [intervalIntegral.integral_add (hi i s hs) (hmi s hs)] at hh
    have hbint := mul_le_mul_of_nonneg_left (hmint s hs) (le_of_lt hg)
    dsimp only [A]
    nlinarith only [hh,hbint]
  have hh := Asakura.FullAudit.ch4_gronwall_written (u i) A g T hT (hc i) hg hbi t ht
  exact hh.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hg.le)) hA)

end WMFKIExternalProbe
#print axioms WMFKIExternalProbe.particle_path_comparison
