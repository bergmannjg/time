import Lake
open System Lake DSL

package time {
  precompileModules := if get_config? env = some "noprecompile" then false else true
}

require mathlib from git "https://github.com/leanprover-community/mathlib4"
  @ "9893bbd22fdca4005b93c8dbff16c1d2de21bc1a"

meta if get_config? env = some "dev" then
require «doc-gen4» from  git "https://github.com/leanprover/doc-gen4"
  @ "f7307953d84be8b1edaff97436e67434111244b0"

@[default_target]
lean_lib Time

@[default_target]
lean_lib Test {
  srcDir := "test"
}

@[default_target]
lean_exe runLinter where
  root := `scripts.runLinter
  supportInterpreter := true

target localtime.o pkg : FilePath := do
  let oFile := pkg.buildDir / "native/" / "localtime.o"
  let srcJob ← inputFile <| pkg.dir / "native/" / "localtime.cpp"
  let flags := #["-I", (← getLeanIncludeDir).toString, "-fPIC"]
  buildO "localtime.cpp" oFile srcJob flags "c++"

extern_lib libleanlocaltime pkg := do
  let name := nameToStaticLib "leanlocaltime"
  let localtime ← fetch <| pkg.target ``localtime.o
  buildStaticLib (pkg.nativeLibDir / name) #[localtime]
