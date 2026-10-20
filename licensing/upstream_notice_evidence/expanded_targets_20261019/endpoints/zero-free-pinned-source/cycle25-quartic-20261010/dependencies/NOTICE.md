# Dependency provenance and compatibility changes

The source lock preserves the exact Git revisions used by the completed proof.
Upstream sources are downloaded at reproduction time; dependency archives,
compiled caches, and unused exploratory modules are not included in this PR.
The four PrimeNumberTheoremAnd modules and 15 RellichKondrachov modules modified
by the included patches retain the exact Lean source bytes used in the
verification environment. Their original copyright and author headers remain
intact. The new PrimeNumberTheoremAnd build configuration only removes unused
research targets/tooling and fixes its Mathlib revision.

PrimeNumberTheoremAnd is from Alex Kontorovich and the project's attributed
contributors, at `c39a751132c88b6e8080b74c74023fd95b3d8be0`:
<https://github.com/AlexKontorovich/PrimeNumberTheoremAnd>.
Rellich–Kondrachov is from Adam Benenson and the project's attributed
contributors, at `70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23`:
<https://github.com/abenenson/rellich-kondrachov>.
Both projects release these sources under Apache-2.0. Their licenses are
retained in `licenses/`; additional upstream notices remain in their downloaded
archives. See the proof directory's principal NOTICE for OpenAI and reused
proof-source attribution.

The original PR 8 PNT patch has SHA-256
`0890432340c0025973bcfe070b634355fa366cc831595f68526e4c73c8903d82`.
The new minimal patch has SHA-256
`e6e3e2931a6fc4d3e99f7217756ce6ba8aaa5467a59bd11078c85550c9e7ff33`.
The unchanged Rellich patch has SHA-256
`0c121d8517dfeadc93ef24fe2deb56beec7cb3998e2552dee8f61c780b1408c8`.
