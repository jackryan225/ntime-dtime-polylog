# Our two patches to OpenAI's Lean library

Both patches change files of openai/math (commit 3344da59991ed94f9ba711217b29c1d760badfa6, folder lean/), which is
licensed under the Apache License, Version 2.0 (`../LICENSE-APACHE-2.0`). The patches are distributed under the same
license. They are byte-identical to the patches of the audited build (sha256 in `../../LEAN-AUDIT.md`).

| Patch | sha256 | What it changes |
|---|---|---|
| `field-uniform.patch` | `32a3d814c7bd3fb45f528979da619d594cf5baaec9143d9fdb0637c00405021f` | `OAI/Computability/MultitapeWeakETH/`: Cloud, FieldLower, FoldedGeometry, GraphGeometry, Main, Padding, Placement, Price; new file MainOver. The port hypothesis and the results that use it are stated for every field, not only in characteristic 0 (`PortOver F`; `PortTwo := PortOver (AlgebraicClosure (ZMod 2))`). |
| `port-over.patch` | `5efa498961c36d2da7f4b6d80ee0af7d2a7a4609c04c969f932c75052f5a330a` | `PortTemplates.lean`: the same proof body for any field: `wireExpanders_of_port_over`, `templates_of_port_over`, `wireExpanders_of_portTwo`. |

Order: `field-uniform.patch` first, then `port-over.patch` (`patch -p1`, from a folder that contains `OAI/`).
`../scripts/get-upstream.sh` does this and checks the result against `../CLOSURE-SHA256SUMS`.

The patched files are compiled and kernel-checked as part of the build, so the proof does not rest on trust in the patches;
a wrong patch could only make the build fail. The statements of the theorems do not mention any OpenAI definition.
