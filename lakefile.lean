import Lake
open Lake DSL

package «auto» {
  precompileModules := false
  preferReleaseBuild := false
}

@[default_target]
lean_lib «Auto» {
  -- add any library configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.15.0"
