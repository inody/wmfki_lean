# Third-party dependency and provenance

## `stochasticAnalysis`

The stochastic-analysis foundation used by this directory is fetched as a Lake dependency:

- Repository: <https://github.com/MasaakiFukasawa/stochastic-analysis-lean>
- Commit: `0cb33378176178d269f53a4dada439f8ecd3bf5e`
- Package name: `stochasticAnalysis`
- License: Apache License 2.0
- Local license copy: `LICENSE-FUKASAWA-APACHE-2.0.txt`

The upstream source is not copied into this directory. Lake stores the pinned checkout in the project cache outside the repository. The project keeps Mathlib fixed at `d13f23b723b8a846827a245b89c10fc7d3f11612`; the selected upstream declarations were checked at this pin before adoption and are rebuilt by the production verifier.

## Project integration modules

`SOURCE_MANIFEST.json` records every adopted project module, its pre-adoption source path and SHA-256 hash, and the adopted SHA-256 hash. The only automated source transformation was changing imports between adopted project modules from `Foo` to `WMFKI_Stochastic.Foo`. Namespaces and theorem statements were not changed.

Files marked `integration-adapter` in the manifest are project-side adapters around the pinned upstream API. They are not presented as upstream originals. Files marked with a stage directory name are the audited WMFKI proof modules produced in the isolated formalization stages.

The Sharp-W2 repository surveyed during development supplied API and proof-architecture inspiration only. No Sharp-W2 source is copied into the adopted module closure and it is not a build dependency.
