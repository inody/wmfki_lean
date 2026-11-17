# WMFKI Lean Formalization

This repository contains the Lean 4 formalization accompanying
*[Mesh-Free Weak-Form Regression for Learning Interaction Kernels from Particle
Trajectories](https://arxiv.org/abs/2611.18455)*.
Its main public endpoint is

```lean
WMFKIJointAssembly.exists_particle_weak_recovery
```

Starting from primitive initial random variables and independent Brownian
inputs, the formalization constructs the mean-field and interacting particle
systems, proves the design and residual moment bounds, and connects them to
oracle OLS and LASSO coefficient-recovery certificates. Quadrature accuracy,
identifiability, sampling-smallness, probability-tolerance, and LASSO-penalty
conditions remain explicit assumptions. The recovery certificate covers both
the constructed LASSO estimator and any pointwise choice satisfying the same
LASSO minimization condition. The result concerns coefficient recovery, not
support recovery.

The audited project contains 565 declarations and 32 examples, with no
project-specific axioms and no `sorry`. Its permitted transitive dependencies
are Lean's standard `propext`, `Classical.choice`, and `Quot.sound`. For a clean
verification run:

```bash
./scripts/setup.sh
python3 scripts/verify.py --clean
```

See [`docs/formalization-map-en.html`](docs/formalization-map-en.html) for a
one-page overview and
[`docs/formalization-dependency-en.md`](docs/formalization-dependency-en.md)
for the theorem-dependency map and correspondence with the paper.

## Libraries and verified components

- `Lean_Code/`: matrices, sampling, OLS/LASSO, and the recovery API;
  128 audited declarations and 26 examples.
- `WMFKI_Stochastic/`: the connection from particle SDEs to that API;
  437 audited declarations and 6 examples.

| Component | Verified scope |
|---|---|
| Particle SDEs | Construct finite-particle solutions from independent initial variables and Brownian inputs, with nonlinear copies on the same primitive-input space. |
| Mean-field equation | Picard construction, uniqueness within the finite-L4 path class, adaptedness, finite-time consistency, and independent nonlinear copies. |
| Synchronous coupling | Fourth-moment particle error bounded by `C/N^2` for globally Lipschitz, linearly growing kernels; constants are chosen before all particle counts `N`. |
| Population design | Measurability, L2 bounds, and Fubini conditions for actual time-integrated feature kernels; identification with the design under the actual marginal laws. |
| Continuous-design budget | Dependence-safe L4-by-L4 coupling bounds and the iid-pair P2 estimate give Frobenius mean-square error `O(M/N)`, where `M` is the dictionary size. |
| Observed-design budget | Observation noise may be biased and internally dependent; supplied RMS quadrature accuracy gives `CA(1/N + e + q)`. |
| Joint residual budget | Particle weak residuals, observation perturbations, and response quadrature are evaluated on the same particle system, yielding `CV(sigma^2/N + e + q)`. |
| Regression definitions | Identify continuous/discrete designs, `fullPairDesign`, `observedWeakResponse`, and `fullRegressionResidual` exactly. |
| Primitive recovery endpoint | Pass the jointly constructed design/residual budgets to `WeakAssemblyData` and obtain oracle OLS and LASSO recovery certificates. |
| Matrices and norms | Euclidean-space representation, operator norm bounded by Frobenius norm, active-column restriction, transpose/adjoint identities, and matrix/vector norm agreement. |
| Moment transfer | Frobenius-square integrability implies operator-norm-square integrability and the corresponding integral bound. |
| Moore-Penrose inverse | Four operator identities, existence in finite-dimensional coefficient spaces, and least-squares minimization; existence does not require full column rank. |
| OLS | Residual orthogonality, prediction/coefficient error, perturbation bounds, and probabilistic recovery with constant 4. |
| LASSO existence | Construct a minimizer from continuity and coercivity for positive penalties. |
| Deterministic LASSO | Derive the basic inequality, cone inclusion, and coefficient-error bound with constant 9 from the half-squared-loss minimization condition. |
| Probabilistic LASSO | Cone and column-norm perturbations, adjoint-score control, recovery with constant 144, and the equality-penalty bound with constant 576. |
| Probability bounds | Markov bounds with explicit integrability, the zero-budget case, and event intersections without independence assumptions. |
| Conditional orthogonality | Conditional centering and measurability give the second-moment identity for a difference. |
| Independent sampling variance | Weighted variance for `P` samples at each time is bounded by `C sum(w_n^2)/P`. |
| Uniform ordered-pair sampling | Construct the off-diagonal population of `N(N-1)` pairs and sampling with replacement; derive independence and centering from the product measure. |
| Conditioning on observations | Prove centering using ordinary conditional expectation on a product of arbitrary observation and sampling laws. |
| Sampled-design assembly | Identify the centered error as sampled minus all-pair design, including the `(N-1)/N` and `1/sqrt(L)` factors. |
| Pair-error moments | From feature measurability, L2 regularity, and second moments, bound the design error by `M C_A Q/P` and its coefficient direction by `C_K Q/P`. |
| Feature moments | Bounded test-gradient maps and linear growth yield explicit L2 bounds from the observed-position second-moment budget `R`, including `3(BGK)^2(1+2R)`. |
| Additive observations | Bound the second moment of `Y = X + epsilon` by `2R_X + 2R_epsilon`, without adding centering or independence assumptions. |
| Observed feature assembly | Define finite-sum weak responses and pair features and prove their measurability and L2 regularity. |
| Dictionary realizability | Given exact dictionary representation of the true kernel, identify the coefficient combination of dictionary features with its feature; directional bounds use the true kernel's growth rate. |
| Actual sampled residual | Prove `r_sampled = r_full - D theta` and the orthogonal second-moment decomposition, adding the pair budget to the full-pair residual budget. |
| Total design error | Decompose the Frobenius mean-square error into all-pair and sampling contributions, then bound the operator error. |
| Recovery application | Derive measurability and integrability before applying the OLS/LASSO results; do not separately assume the sampled-error estimates. |
| Known support | Control selected-column error using the full design; the OLS lower bound is required only on active columns, not the entire dictionary. |

Sampling independence is proved conditional on the observations. Independence
of the features after averaging over observations is not assumed. All rows and
atoms share the same sampling sequence; coefficient-direction bounds use the
combined feature's second moment rather than introducing an unnecessary
coefficient-norm factor.

The stochastic layer identifies gradients, Laplacians, and temporal derivatives
with genuine Frechet derivatives. It constructs the primitive inputs on an
explicit product probability space; it does not transfer the result to every
pre-existing joint realization.

## From particle inputs to recovery

Write `D0` and `V0` for the full-pair design and residual mean-square budgets.
Here `e` corresponds to the paper's `Delta t^(2p)` quadrature budget, and `q`
to the observation-error second-moment budget. The construction gives

```text
primitive initial variables + independent Brownian inputs
  -> mean-field and interacting particle systems, synchronous coupling
  -> fourth-moment rate C/N^2, time-integrated features, population design
  -> D0 <= CA(1/N + e + q), V0 <= CV(sigma^2/N + e + q)
  -> uniform ordered-pair sampling and conditional centering
  -> D = D0 + M C_A Q/P, V = V0 + C_K Q/P
  -> oracle OLS and raw-design LASSO coefficient recovery
```

In the sampling step, `P` is the pair count, `Q` is the sum of squared
quadrature weights, and `C_A` and `C_K` are the corresponding feature-moment
constants. The design budget is derived in Frobenius mean square; a Frobenius
bound is not inferred in the reverse direction from an operator-norm bound.

The primitive-input endpoint is
`WMFKIJointAssembly.exists_particle_weak_recovery`. Its recovery-side APIs are
`WMFKI.WeakAssemblyData.oracle_recovery` and `lasso_recovery`.
`lasso_recovery_of_minimizer` and `RecoveryCertificate.lasso_any` also cover
any pointwise choice satisfying the LASSO minimization condition, not only the
particular minimizer constructed by the library.

### Meaning of the recovery bounds

For oracle OLS, let `B` and `A_inf` denote the design and population reference
restricted to the known active columns, `y` the response, and `theta_star`
the true active coefficients. With mean-square upper bounds `D,V`, stability
constant `gamma > 0`, and confidence parameters `0 < delta, epsilon` satisfying
`delta + epsilon < 1`, the conditions take the form

```text
E ||B - A_inf||_op^2 <= D, E ||y - B theta_star||^2 <= V,
for all u: gamma ||u|| <= ||A_inf u||, D <= delta gamma^2/4.
```

It obtains a measurable event of probability at least `1 - delta - epsilon`
on which

```text
||theta_hat - theta_star||^2 <= 4V/(epsilon gamma^2).
```

For LASSO, use the full design and let `S` contain the true support. Under the
corresponding cone lower bound, column-norm bound `R`, moment and smallness
conditions, and a positive
penalty satisfying `lambda >= 2(R + gamma/2) sqrt(V/epsilon)`, a measurable
event of probability at least `1 - delta - epsilon` satisfies

```text
theta_hat - theta_star belongs to cone(S),
||theta_hat - theta_star||^2 <= 144 |S| lambda^2/gamma^4.
```

Substituting equality in the penalty lower bound gives
`576 |S| (R + gamma/2)^2 V/(epsilon gamma^4)`. This substitution does not
remove the requirement `lambda > 0`.

The design and residual need not be independent. `EstimatorRecovery.lean`
uses existence of the estimators, rather than taking their minimization
conditions as separate assumptions for the constructed choices. Measurability
of a selected estimator and correctness of a numerical solver are not proved.
The statements explicitly exhibit measurable good events and do not silently
rely on estimator measurability.

## Axiom audit and scope limits

All 565 audited declarations have transitive axiom dependencies contained in
`propext`, `Classical.choice`, and `Quot.sound`. There are no project-specific
axioms or `sorry`. The fixed OLS definitions, `Showcase`, and LASSO
specifications retain their protected hashes.

The 32 examples include genuine third-order Frechet derivatives, compact
bumps, biased and fully dependent observation noise, a nonzero selected-support
residual, and the primitive Brownian recovery endpoint.

The following remain explicit assumptions or outside the verified scope:

- **RMS quadrature accuracy** is supplied for the same actual particle system;
  it is not derived from temporal regularity alone.
- **Exact representation of the true kernel by the dictionary** is an input
  assumption.
- **Identifiability and restricted-cone geometry, sampling smallness,
  probability tolerances, and LASSO penalty conditions** remain assumptions
  at recovery application time.
- **Support recovery**, correctness of numerical algorithms, and measurability
  of a selected estimator are not formalized.
- **Universal transfer to an arbitrary pre-existing joint realization** and
  uniform-in-time rates are not formalized.
- Additional adaptedness of nonlinear copies to the enlarged particle
  filtration is not formalized; it is not needed for the finite-time ordinary
  integral estimates used here.
- Mathlib uses its official compiled cache rather than a full source rebuild.
  The required transitive stochastic-analysis modules are built from the pinned
  dependency. Upstream linter warnings are recorded separately from the zero
  project-source warning count.
- Verification has not been independently repeated by another researcher in a
  separate environment.

See [`WMFKI_Stochastic/README.md`](WMFKI_Stochastic/README.md) and
[`WMFKI_Stochastic/THIRD_PARTY.md`](WMFKI_Stochastic/THIRD_PARTY.md) for the
stochastic layer's scope and provenance.

## Reproducing verification

Run the setup and verification commands above from this directory.

- Lean **4.34.1** and Mathlib **v4.34.1**, pinned to
  `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- `stochasticAnalysis`, pinned to `0cb33378176178d269f53a4dada439f8ecd3bf5e`,
  under Apache-2.0.
- elan **4.2.4**, installed in the dedicated `~/.cache/wmfki-lean/` cache.
- `.lake` is a symlink to that external cache; dependencies and build artifacts
  remain outside the repository. Shell configuration and existing Lean
  environments are not modified.
- Set `WMFKI_LEAN_CACHE` to choose another cache location. Setup refuses to
  overwrite an existing `.lake` that points elsewhere.
- The initial setup requires network access and at least several GB of free
  space; tens of GB are recommended for the Mathlib and stochastic-analysis
  build caches.

**Do not run bare `lake clean`.** The verifier uses
`lake clean wmfki_formalization` to rebuild only this project's targets.
Individual checks are available through

```bash
./scripts/lake env lean Lean_Code/Human_Check.lean
./scripts/lake env lean WMFKI_Stochastic/Audit.lean
```

The optional historical R06 manuscript-protection check is

```bash
python3 scripts/verify.py --clean --check-paper
```

This compares historical protected hashes and is expected to fail if those
manuscript sources have subsequently changed. To check the current L4DC theorem,
sampled LASSO definition, residual scale, and pair-sampling assumption, place
this checkout in the paper repository's `lean/` directory alongside `L4DC/`
and run

```bash
python3 scripts/verify.py --clean --check-l4dc
```

`--check-paper` protects the historical R06 snapshot; `--check-l4dc` checks the
extracted environments recorded in `l4dc-statement-lock.json`.

## Source guide

- `docs/formalization-map-en.html` and `docs/formalization-dependency-en.md`:
  English concept map, Mermaid dependency graph, and paper correspondence.
  The [Japanese map](docs/formalization-map.html) and
  [Japanese dependency guide](docs/formalization-dependency.md) remain available.
- `Blueprint.md` and `EXTENSION_PLAN.md`: design and dependencies.
- `Lean_Code/Definitions.lean` and `LassoDefinitions.lean`: fixed definitions
  and conditional theorem statements.
- `Showcase.lean`: the unchanged original OLS specification endpoint.
- `Lean_Code/MatrixBridge.lean` and `MatrixMoments.lean`: matrix/norm bridges.
- `Lean_Code/MoorePenrose*.lean`: pseudoinverse existence and minimization.
- `Lean_Code/Lasso*.lean`: existence, geometry, and deterministic/probabilistic
  LASSO bounds.
- `Lean_Code/EstimatorRecovery.lean`: recovery for the constructed estimators.
- `Lean_Code/ConditionalOrthogonality.lean` and `SamplingVariance.lean`:
  conditional orthogonality and sampling-variance results.
- `Lean_Code/FiniteSampling.lean` and `PairSampling.lean`: uniform finite
  populations and ordered-pair sampling.
- `Lean_Code/SamplingConditional.lean`, `SamplingIntegrability.lean`, and
  `SamplingMoments.lean`: the observation/sampling product space.
- `Lean_Code/PairDesignMoments.lean` and `PairAssembly.lean`: shared-sampling
  matrix/directional bounds and exact assembly identities.
- `Lean_Code/FeatureMoments.lean`, `ObservationMoments.lean`, and
  `ObservedFeatures.lean`: feature growth, additive observations, and assembly.
- `Lean_Code/ResidualOrthogonality.lean` and `SampledResidual.lean`: conditional
  orthogonality for the actual regression residual.
- `Lean_Code/WeakPairMoments.lean`: combine weak responses, position moments,
  and full-pair residual bounds.
- `Lean_Code/SamplingRegularity.lean`: measurability and squared-norm
  integrability of matrices and residuals.
- `Lean_Code/DesignComposition.lean`: Frobenius-error addition and operator
  bounds.
- `Lean_Code/PairRecovery.lean` and `WeakPairRecovery.lean`: apply recovery to
  raw pair features and the observed regression, including known-support OLS.
- `Lean_Code/Human_Check.lean` and `AXIOM_STATUS.md`: examples and proof ledger.
- `WMFKI_Stochastic/PrimitiveRecovery.lean`: the primitive-input endpoint.
- `WMFKI_Stochastic/RecoveryCertificate.lean`: application conditions and
  conclusions for oracle OLS and constructed or arbitrary LASSO minimizers.
- `WMFKI_Stochastic/HumanCheckJointRecovery.lean` and `Audit.lean`: six examples
  and the audit of 437 declarations.
- `WMFKI_Stochastic/SOURCE_MANIFEST.json` and `THIRD_PARTY.md`: source origins,
  hashes, dependencies, and licensing.
- `statement-lock.json` and `extension-statement-lock.json`: fixed Lean
  specification hashes.
- `l4dc-statement-lock.json`: current L4DC theorem/prerequisite hashes.
- `verification/validation.json`, `build.log`, and `axioms.log`: verification
  evidence.

The `docs/` directory contains formalization maps and dependency material.
Manuscript sources, input materials, and build caches are not included here.

## License

The project's own source is licensed under the MIT License, with
`Copyright (c) 2026 Daisuke Inoue`; see [`LICENSE`](LICENSE). Third-party
dependencies retain their upstream licenses. The pinned stochastic-analysis
dependency and its Apache-2.0 license are documented in
[`WMFKI_Stochastic/THIRD_PARTY.md`](WMFKI_Stochastic/THIRD_PARTY.md).
