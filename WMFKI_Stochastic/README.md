# Particle-to-recovery formalization

This library contains the production-adopted finite-horizon proof chain from primitive particle inputs to random-pair OLS and LASSO recovery.

Public endpoint:

```lean
WMFKIJointAssembly.exists_particle_weak_recovery
```

Within the explicit product-model scope, the endpoint:

1. constructs the mean-field process and synchronously coupled interacting particle system from initial randomness and independent Brownian inputs;
2. proves the fourth-moment synchronous rate;
3. constructs the actual time-integrated feature kernel and population design;
4. proves the continuous particle-to-population Frobenius error rate;
5. adds independent observation noise and supplied RMS quadrature budgets on the same realization;
6. derives the design and residual budgets
   `D0 ≤ CA * (1/N + e + q)` and
   `V0 ≤ CV * (σ²/N + e + q)`;
7. returns a `RecoveryCertificate` connected to the existing production known-support OLS and LASSO APIs.

The RMS quadrature hypotheses, population identifiability or restricted-cone geometry, sampling-smallness conditions, probability tolerances, and LASSO penalty condition remain explicit assumptions at their proper interfaces. Coefficient recovery is not claimed to imply support recovery.

`HumanCheckJointRecovery.lean` contains six semantic examples, including genuine bounded sine derivatives, a nonzero compactly supported time test, dependent biased observation noise, a nonzero selected-support residual, and an internally constructed Brownian endpoint.

`Audit.lean` audits every public declaration in the adopted closure. `SOURCE_MANIFEST.json` and `THIRD_PARTY.md` record provenance and licensing.
