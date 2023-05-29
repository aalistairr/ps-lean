import Lake
open Lake DSL

package «hammer» {
  precompileModules := true,
}

@[default_target]
lean_lib «Hammer»
