import WMFKI_Stochastic.MeanFieldIndependentCopies

open MeasureTheory Set
open WMFKIMeanFieldAdapted

namespace WMFKIMeanFieldCopies
variable {Ω E I : Type*} [m : MeasurableSpace Ω] [MeasurableSpace E]

/-- 各コピーの過去情報を集めた共通フィルトレーション。ここでは完備化はまだ行わない。 -/
noncomputable abbrev copyFiltration (F : ℝ → MeasurableSpace Ω) (I : Type*) (t : ℝ) :
    MeasurableSpace (I → Ω) := ⨆ i : I, MeasurableSpace.comap (fun ω : I → Ω => ω i) (F t)

omit m in
theorem copy_filtration_mono {F : ℝ → MeasurableSpace Ω} (hF : Monotone F) :
    Monotone (copyFiltration F I) := by
  intro s t hst
  exact iSup_mono (fun _ => MeasurableSpace.comap_mono (hF hst))

theorem copy_filtration_le {F : ℝ → MeasurableSpace Ω} (hF : ∀ t, F t ≤ m) (t : ℝ) :
    copyFiltration F I t ≤ (inferInstance : MeasurableSpace (I → Ω)) := by
  apply iSup_le
  intro i
  exact (MeasurableSpace.comap_mono (hF t)).trans (measurable_pi_apply i).comap_le

omit m in
/-- 全コピーが同じフィルトレーションに適合する。各コピーの全未来情報を加えない。 -/
theorem copies_adapted {F : ℝ → MeasurableSpace Ω} {T : ℝ} {X : ℝ → Ω → E}
    (hX : AdaptedOn F T X) (i : I) : AdaptedOn (copyFiltration F I) T (copyProcess X i) := by
  intro t ht
  have hc : Measurable[(F t).comap (fun ω : I → Ω => ω i)] (copyProcess X i t) := by
    let : MeasurableSpace Ω := F t
    let : MeasurableSpace (I → Ω) := (F t).comap (fun ω : I → Ω => ω i)
    exact (hX t ht).comp (Measurable.of_comap_le le_rfl)
  exact hc.mono (le_iSup (fun i : I => (F t).comap (fun ω : I → Ω => ω i)) i) le_rfl

end WMFKIMeanFieldCopies
