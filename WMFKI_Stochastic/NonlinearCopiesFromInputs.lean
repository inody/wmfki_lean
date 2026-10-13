import WMFKI_Stochastic.IndependentBrownianCopies

open MeasureTheory ProbabilityTheory Set
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
open WMFKIMeanFieldPicard WMFKIMeanFieldAdapted
open scoped NNReal

namespace WMFKIMeanFieldCopies
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- 構成結果の証明書。下の原始入力存在定理の「出力」であり、入力仮定にはしない。
    一粒子Yを選んでから全Nを同じ式copyProcessで構成する。 -/
structure IIDNonlinearFamily (P : Measure Ω) (F : ℝ → MeasurableSpace Ω) (T : ℝ)
    (K : E → E) (ξ : Ω → E) (D Y : ℝ → Ω → E) (C : ℝ) : Prop where
  base_paths : FiniteL4Paths P T Y
  nonneg : 0 ≤ C
  paths : ∀ N : ℕ, ∀ i : Fin N, FiniteL4Paths (Measure.pi (fun _ : Fin N => P)) T (copyProcess Y i)
  adapted : ∀ N : ℕ, ∀ i : Fin N, AdaptedOn (copyFiltration F (Fin N)) T (copyProcess Y i)
  joint : ∀ N : ℕ, ∀ i : Fin N,
    StronglyMeasurable (fun z : ℝ × (Fin N → Ω) => copyProcess Y i z.1 z.2)
  independent : ∀ N : ℕ,
    iIndepFun (fun i : Fin N => finiteTrajectory T (copyProcess Y i)) (Measure.pi (fun _ : Fin N => P))
  law : ∀ N : ℕ, ∀ i : Fin N, ∀ t ∈ Icc 0 T,
    HasLaw (copyProcess Y i t) (P.map (Y t)) (Measure.pi (fun _ : Fin N => P))
  fourth : ∀ N : ℕ, ∀ i : Fin N, ∀ t ∈ Icc 0 T,
    MemLp (copyProcess Y i t) 4 (Measure.pi (fun _ : Fin N => P)) ∧
      (∫ ω, ‖copyProcess Y i t ω‖^4 ∂(Measure.pi (fun _ : Fin N => P))) ≤ C
  equation : ∀ N : ℕ, ∀ᵐ ω ∂(Measure.pi (fun _ : Fin N => P)), ∀ i : Fin N,
    copyProcess Y i 0 ω = ξ (ω i) ∧ ∀ t ∈ Icc 0 T,
      copyProcess Y i t ω = ξ (ω i) +
        (∫ s in (0 : ℝ)..t, ∫ y, K (copyProcess Y i s ω-y) ∂(P.map (Y s))) + D t (ω i)

variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- 構成済みの一粒子解からの組み立て。コピーの独立性や共通方程式を仮定しない。 -/
theorem iid_family_from_solution (F : ℝ → MeasurableSpace Ω) (T : ℝ) (K : E → E)
    (ξ : Ω → E) (D Y : ℝ → Ω → E) (hm : ∀ t, Measurable (Y t))
    (hc : ∀ ω, Continuous (fun t => Y t ω)) (hY : FiniteL4Paths P T Y) (hA : AdaptedOn F T Y)
    (he : ∀ᵐ ω ∂P, Y 0 ω = ξ ω ∧ ∀ t ∈ Icc 0 T,
      Y t ω = ξ ω + (∫ s in (0 : ℝ)..t, ∫ y, K (Y s ω-y) ∂(P.map (Y s))) + D t ω) :
    ∃ C : ℝ, IIDNonlinearFamily P F T K ξ D Y C := by
  obtain ⟨C,hC,hfour⟩ := copies_uniform_fourth hY
  refine ⟨C,⟨hY,hC,fun N i => finite_l4_paths_pullback (measurePreserving_eval (fun _ : Fin N => P) i) hY,
    fun _ i => copies_adapted hA i,fun _ i => copy_jointly_measurable hm hc i,
    fun _ => copies_independent_paths hY,fun _ i t ht => copy_hasLaw hY i t ht,hfour,?_⟩⟩
  intro N
  exact ae_all_iff.mpr (fun i => (measurePreserving_eval (fun _ : Fin N => P) i).quasiMeasurePreserving.ae he)

/-- 共有する過去情報は単調でambient以下。ただし積フィルトレーションの完備化や
    全駆動のBrownianSystem証明書は、この補題では構成しない。 -/
theorem brownian_copy_filtration {d : ℕ} (B : BrownianSystem P d) (I : Type*) :
    Monotone (copyFiltration (fun t => B.F (realTimeClamp t)) I) ∧
      ∀ t, copyFiltration (fun t => B.F (realTimeClamp t)) I t ≤
        (inferInstance : MeasurableSpace (I → Ω)) :=
  ⟨copy_filtration_mono (fun _ _ hst => B.mono (real_time_clamp_mono hst)),
    copy_filtration_le (fun _ => B.le _)⟩

set_option maxHeartbeats 1000000 in
/-- 初期値・Brownian法則・独立性・L4初期モーメントから、全Nの非線形コピーを構成する。
    各コピーの同一性、独立性、適合性、方程式、Nに依存しないモーメントはすべて結論。
    相互作用粒子SDEとの共通実現への埋め込みと同期誤差率は未主張。 -/
theorem exists_iid_nonlinear_family
    {A : Type*} [MeasurableSpace A] (π : Measure A) (P : Measure Ω)
    [IsProbabilityMeasure π] [IsProbabilityMeasure P] {d : ℕ}
    (W : Fin d → ℝ≥0 → Ω → ℝ) (hW : ∀ j, IsBrownianReal (W j) P)
    (hm : ∀ j t, Measurable (W j t)) (hI : iIndepFun (fun j ω t => W j t ω) P)
    (ξ : A → EuclideanSpace ℝ (Fin d)) (hξm : Measurable ξ) (hξ : MemLp ξ 4 π)
    (T : ℝ) (hT : 0 ≤ T) (σ : ℝ)
    {L : ℝ≥0} (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hK : LipschitzWith L K) :
    ∃ (B : BrownianSystem (π.prod P) d) (Y : ℝ → A × Ω → EuclideanSpace ℝ (Fin d)) (C : ℝ),
      IIDNonlinearFamily (π.prod P) (fun t => B.F (realTimeClamp t)) T K (fun z => ξ z.1)
        (fun t z => σ • WithLp.toLp 2 (fun j => W j (halfTimeReal (realTimeClamp t)) z.2)) Y C ∧
      (∀ N : ℕ,
        (∀ p : Fin N × Fin d, IsBrownianReal (fun t (ω : Fin N → A × Ω) => W p.2 t (ω p.1).2)
          (Measure.pi (fun _ : Fin N => π.prod P))) ∧
        (∀ (p : Fin N × Fin d) t, Measurable (fun ω : Fin N → A × Ω => W p.2 t (ω p.1).2)) ∧
        iIndepFun (fun (p : Fin N × Fin d) (ω : Fin N → A × Ω) t => W p.2 t (ω p.1).2)
          (Measure.pi (fun _ : Fin N => π.prod P))) := by
  obtain ⟨B,Y,_,hA,hYm,hYc,hE,_,_,he⟩ := exists_product_adapted_mean_field π P W hW hm hI
    ξ hξm hξ T hT σ K hK
  obtain ⟨C,hC⟩ := iid_family_from_solution (fun t => B.F (realTimeClamp t)) T K (fun z => ξ z.1)
    (fun t z => σ • WithLp.toLp 2 (fun j => W j (halfTimeReal (realTimeClamp t)) z.2)) Y hYm hYc
    (finite_l4_paths_of_global_envelope hYm hYc hE) hA he
  refine ⟨B,Y,C,hC,fun N => ?_⟩
  have hp : MeasurePreserving (Prod.snd : A × Ω → Ω) (π.prod P) P := measurePreserving_snd
  have hB (j : Fin d) := brownian_pullback hp (W j) (hW j)
  have hBm (j : Fin d) (t : ℝ≥0) : Measurable (fun z : A × Ω => W j t z.2) := (hm j t).comp measurable_snd
  have hBI := independent_family_pullback hp (fun j ω t => W j t ω)
    (fun j => Measurable.of_eval (hm j)) hI
  exact replicated_brownian_family (I := Fin N) (fun j t (z : A × Ω) => W j t z.2) hB hBm hBI

end WMFKIMeanFieldCopies
