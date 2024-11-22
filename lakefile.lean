import Lake
open System Lake DSL

package time {
  precompileModules := if get_config? env = some "noprecompile" then false else true
}

meta if get_config? env = some "dev" then
require «doc-gen4» from  git "https://github.com/leanprover/doc-gen4" @ "v4.13.0"

require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.13.0"

@[default_target]
lean_lib Time

target localtime.o pkg : FilePath := do
  let oFile := pkg.buildDir / "native/" / "localtime.o"
  let srcJob ← inputTextFile <| pkg.dir / "native/" / "localtime.cpp"
  let flags := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob  flags #["-fPIC"] "c++"

extern_lib libleanlocaltime pkg := do
  let name := nameToStaticLib "leanlocaltime"
  let localtime ← localtime.o.fetch
  buildStaticLib (pkg.nativeLibDir / name) #[localtime]

lean_lib Test where
  srcDir := "test"
  roots := #[`Test]

@[test_driver]
lean_exe test where
  srcDir := "test"
  root := `Test

lean_lib Verify where
  globs := #[.andSubmodules `Time.Verify]
