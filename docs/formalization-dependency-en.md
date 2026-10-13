# WMFKI formalization: dependency graph of major declarations

This graph displays the declarations needed to understand the main mathematical route, rather than all 437 new declarations. The complete audited inventory is recorded in [`WMFKI_Stochastic/Audit.lean`](../WMFKI_Stochastic/Audit.lean) and [`SOURCE_MANIFEST.json`](../WMFKI_Stochastic/SOURCE_MANIFEST.json).

- Blue: constructed or proved in Lean
- Purple: bridge to the existing production definitions and recovery API
- Green: final output
- Yellow: explicit assumptions retained at application time
- Gray: outside the present formalization

```mermaid
flowchart TB
  classDef proved fill:#e9f6fa,stroke:#176b87,color:#17324a,stroke-width:1.5px
  classDef bridge fill:#efedff,stroke:#5747b7,color:#2f285f,stroke-width:1.5px
  classDef result fill:#e8f7ef,stroke:#26734d,color:#16452f,stroke-width:2px
  classDef assumed fill:#fff4df,stroke:#b56a00,color:#684000,stroke-width:1.5px
  classDef outside fill:#eef1f5,stroke:#7a8494,color:#4f5968,stroke-dasharray:5 4

  subgraph I[0. Primitive inputs]
    I0["π, P: probability measures"]:::assumed
    I1["ξ: measurable L⁴ initial variable"]:::assumed
    I2["W: independent Brownian family"]:::assumed
    I3["K: globally Lipschitz"]:::assumed
    I4["φ: bounded C³ test / ψ: C¹ time test"]:::assumed
    I5["dictionary atoms and exact true coefficients"]:::assumed
  end

  subgraph M[1. Mean-field construction]
    M0["lawDrift / picardStep"]:::proved
    M1["picardIter → picardLimit"]:::proved
    M2["FiniteL4Paths"]:::proved
    M3["exists_unique_product_adapted_mean_field"]:::proved
  end

  subgraph C[2. Copies and interacting particles]
    C0["exists_iid_nonlinear_family"]:::proved
    C1["ArrayNonlinearFamily"]:::proved
    C2["exists_synchronous_particle_family"]:::proved
    C3["SynchronousParticlePair"]:::proved
  end

  subgraph S[3. Synchronous fourth-moment rate]
    S0["iid_fluctuation_fourth"]:::proved
    S1["finite_integral_fourth_moment"]:::proved
    S2["synchronous_path_envelope"]:::proved
    S3["exists_synchronous_fourth_rate\nE‖Xᵢᴺ−Yᵢ‖⁴ ≤ C/N²"]:::proved
  end

  subgraph D[4A. Design branch D₀]
    D0["weak_pair_feature_coupling\ndependent L⁴×L⁴ bounds"]:::proved
    D1["exists_continuous_design_coupling"]:::proved
    D2["time_pair_kernel_moments"]:::proved
    D3["copy_design_identification"]:::proved
    D4["iid_pair_matrix_frobenius_rate"]:::proved
    D5["population_design_identification"]:::proved
    D6["exists_continuous_population_rate\nE‖Aᴺ−A∞‖F² ≤ CM/N"]:::proved
  end

  subgraph V[4B. Residual branch V₀]
    V0["weighted_particle_ito"]:::proved
    V1["weighted_particle_weak_balance"]:::proved
    V2["weak_residual_vector_energy\n∝ σ²/N"]:::proved
    V3["independent_residual_from_position"]:::proved
  end

  subgraph O[5. Observation and quadrature]
    O0["independentObservationSamples\nindependence only from latent system"]:::proved
    O1["observed_dictionary_moment"]:::proved
    O2["exists_observed_full_design_rate"]:::proved
    O3["exists_joint_weak_budgets\nD₀ and V₀ on the same X"]:::proved
    Q0["design RMS quadrature ≤ Qe"]:::assumed
    Q1["response RMS quadrature ≤ Qe"]:::assumed
  end

  subgraph B[6. Bridges to production definitions]
    B0["continuous_design_bridge"]:::bridge
    B1["discrete_design_bridge\n= fullPairDesign"]:::bridge
    B2["weak_response_bridge\n= observedWeakResponse"]:::bridge
    B3["full_residual_bridge\n= fullRegressionResidual"]:::bridge
    B4["genuineWeakAssembly"]:::bridge
  end

  subgraph R[7. Random-pair recovery]
    R0["WeakAssemblyData.oracle_recovery"]:::bridge
    R1["WeakAssemblyData.lasso_recovery"]:::bridge
    R2["recover_genuine_assembly"]:::bridge
    R3["RecoveryCertificate"]:::result
    R4["exists_particle_weak_recovery"]:::result
    A0["selected-design lower bound / cone lower bound"]:::assumed
    A1["sampling smallness, δ, ε"]:::assumed
    A2["column bound / λ conditions"]:::assumed
  end

  I0 --> M0
  I1 --> M0
  I2 --> M3
  I3 --> M0
  M0 --> M1 --> M2 --> M3
  M3 --> C0 --> C1
  I2 --> C2
  I3 --> C2
  C1 --> C2 --> C3

  C3 --> S0
  S0 --> S1 --> S2 --> S3

  I4 --> D0
  I5 --> D0
  S3 --> D0 --> D1
  C1 --> D2
  D2 --> D3
  C1 --> D4
  D3 --> D4
  D4 --> D6
  D5 --> D6
  D1 --> D6

  C3 --> V0 --> V1 --> V2 --> V3
  I4 --> V0
  I3 --> V0

  D6 --> O2
  O0 --> O1 --> O2
  Q0 --> O2
  V3 --> O3
  O2 --> O3
  Q1 --> O3

  O2 --> B0
  O2 --> B1
  O3 --> B2
  O3 --> B3
  B0 --> B4
  B1 --> B4
  B2 --> B4
  B3 --> B4

  B4 --> R2
  O3 --> R2
  R0 --> R2
  R1 --> R2
  A0 --> R0
  A0 --> R1
  A1 --> R0
  A1 --> R1
  A2 --> R1
  R2 --> R3 --> R4

  X0["transfer to an arbitrary pre-existing joint realization"]:::outside
  X1["uniform-in-time rate"]:::outside
  X2["numerical solver / support recovery"]:::outside
  R4 -. out of scope .-> X0
  R4 -. out of scope .-> X1
  R4 -. out of scope .-> X2

  click M1 "../WMFKI_Stochastic/MeanFieldPicardLimit.lean" "Picard limit"
  click M3 "../WMFKI_Stochastic/MeanFieldWellPosedness.lean" "Mean-field adaptedness and uniqueness"
  click C0 "../WMFKI_Stochastic/NonlinearCopiesFromInputs.lean" "iid copies"
  click C2 "../WMFKI_Stochastic/SynchronousArrayEquation.lean" "Synchronous particle system"
  click S3 "../WMFKI_Stochastic/SynchronousFourthRate.lean" "Synchronous rate"
  click D1 "../WMFKI_Stochastic/ActualDesignCoupling.lean" "Feature-design coupling"
  click D2 "../WMFKI_Stochastic/TimePairKernel.lean" "Actual time kernel"
  click D4 "../WMFKI_Stochastic/IIDPairMatrix.lean" "iid-pair P2 bound"
  click D5 "../WMFKI_Stochastic/PopulationFeatureLaw.lean" "Population identification"
  click D6 "../WMFKI_Stochastic/ContinuousPopulationRate.lean" "Continuous design rate"
  click V2 "../WMFKI_Stochastic/EmpiricalResidualEnergy.lean" "Weak residual energy"
  click V3 "../WMFKI_Stochastic/IndependentResidualFromPosition.lean" "Observation and quadrature V0"
  click O2 "../WMFKI_Stochastic/ActualObservedDesign.lean" "Observed D0"
  click O3 "../WMFKI_Stochastic/JointWeakBudgets.lean" "D0/V0 on the same realization"
  click B1 "../WMFKI_Stochastic/DiscreteDesignBridge.lean" "Identification with fullPairDesign"
  click B2 "../WMFKI_Stochastic/WeakResponseBridge.lean" "Identification with observedWeakResponse"
  click B4 "../WMFKI_Stochastic/GenuineWeakAssembly.lean" "WeakAssemblyData construction"
  click R2 "../WMFKI_Stochastic/RecoveryCertificate.lean" "Connection to production recovery API"
  click R4 "../WMFKI_Stochastic/PrimitiveRecovery.lean" "Public endpoint"
```

## Correspondence between the paper and Lean

| Role in the paper | Main Lean declaration | File |
|---|---|---|
| Construction and uniqueness of the mean-field equation | `exists_unique_product_adapted_mean_field` | [`MeanFieldWellPosedness.lean`](../WMFKI_Stochastic/MeanFieldWellPosedness.lean) |
| iid nonlinear copies | `exists_iid_nonlinear_family` | [`NonlinearCopiesFromInputs.lean`](../WMFKI_Stochastic/NonlinearCopiesFromInputs.lean) |
| Synchronous interacting particle system | `exists_synchronous_particle_family` | [`SynchronousArrayEquation.lean`](../WMFKI_Stochastic/SynchronousArrayEquation.lean) |
| Synchronous fourth-moment rate | `exists_synchronous_fourth_rate` | [`SynchronousFourthRate.lean`](../WMFKI_Stochastic/SynchronousFourthRate.lean) |
| Feature stability | `exists_continuous_design_coupling` | [`ActualDesignCoupling.lean`](../WMFKI_Stochastic/ActualDesignCoupling.lean) |
| P2 bound for the iid-pair design | `iid_pair_matrix_frobenius_rate` | [`IIDPairMatrix.lean`](../WMFKI_Stochastic/IIDPairMatrix.lean) |
| Identification with the actual population design | `population_design_identification` | [`PopulationFeatureLaw.lean`](../WMFKI_Stochastic/PopulationFeatureLaw.lean) |
| Continuous-design convergence (Theorem 4.9 type) | `exists_continuous_population_rate` | [`ContinuousPopulationRate.lean`](../WMFKI_Stochastic/ContinuousPopulationRate.lean) |
| Observed-design budget D₀ | `exists_observed_full_design_rate` | [`ActualObservedDesign.lean`](../WMFKI_Stochastic/ActualObservedDesign.lean) |
| Joint D₀/V₀ budgets on one realization (Theorems 4.8–4.9 type) | `exists_joint_weak_budgets` | [`JointWeakBudgets.lean`](../WMFKI_Stochastic/JointWeakBudgets.lean) |
| Connection to the production recovery API | `recover_genuine_assembly` | [`RecoveryCertificate.lean`](../WMFKI_Stochastic/RecoveryCertificate.lean) |
| Random-pair recovery (Theorem 4.12 type) | `exists_particle_weak_recovery` | [`PrimitiveRecovery.lean`](../WMFKI_Stochastic/PrimitiveRecovery.lean) |

## How to read the final theorem

The quantifier order in `exists_particle_weak_recovery` is:

```text
primitive inputs
  → ∃ Y, R, Rpos, CA, CV
  → ∀ N > 0, ∃ BN, X
  → for every finite grid, observation noise system, e, and q
  → D₀ bound ∧ V₀ bound ∧ RecoveryCertificate
```

Thus, `CA` and `CV` are not chosen separately for each `N`. The theorem also does not take `D₀`, `V₀`, or the unknown trajectories as primitive assumptions.

## Explicit assumptions and scope boundaries

### Explicit assumptions

- RMS quadrature accuracy for the design and response
- Exact representation of the true kernel by the dictionary
- Lower bound for the selected OLS population design
- Cone lower bound and column bound for LASSO
- Sampling smallness, `δ`, `ε`, a positive penalty, and the penalty lower bound

### Outside the present formalization

- Universal transfer to an arbitrary pre-existing joint realization
- Additional adaptedness of the copies to a newly constructed particle filtration
- Uniform-in-time rates
- Measurability of the estimators themselves
- Correctness of a numerical solver
- Support recovery

## Viewing the graph

GitHub and Mermaid-enabled Markdown previews render the diagram directly. The concept-oriented one-page English version, including this graph, is [`formalization-map-en.html`](formalization-map-en.html).
