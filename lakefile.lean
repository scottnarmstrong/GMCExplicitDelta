import Lake

open Lake DSL

package GMCExplicitDelta

require SubdiffusiveProcess from git
  "https://github.com/nitromannitol/subdiffusive-process" @ "4c6b8fa60357a07fd5713e5104a6cc70f8e432dc"

@[default_target]
lean_lib GMCExplicitDelta where
  globs := #[.andSubmodules `GMCExplicitDelta]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

lean_lib «GMCExplicitDeltaAudit» where
  globs := #[.submodules `GMCExplicitDeltaAudit]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]
