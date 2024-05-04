import Lake
open System Lake DSL

package time {
  precompileModules := if get_config? env = some "noprecompile" then false else true
}

require std from git "https://github.com/leanprover/std4" @ "v4.8.0-rc1"

meta if get_config? env = some "dev" then
require CMark from git
  "https://github.com/xubaiw/CMark.lean" @ "main"

meta if get_config? env = some "dev" then
require «UnicodeBasic» from git
  "https://github.com/fgdorais/lean4-unicode-basic" @ "main"

meta if get_config? env = some "dev" then
require Cli from git
  "https://github.com/mhuisi/lean4-cli" @ "nightly"

meta if get_config? env = some "dev" then
require leanInk from git
  "https://github.com/hargonix/LeanInk" @ "doc-gen"

meta if get_config? env = some "dev" then
require «doc-gen4» from  git "https://github.com/leanprover/doc-gen4" @ "main"

@[default_target]
lean_lib Time

@[default_target]
lean_lib Test {
  srcDir := "test"
}

target localtime.o pkg : FilePath := do
  let oFile := pkg.buildDir / "native/" / "localtime.o"
  let srcJob ← inputFile <| pkg.dir / "native/" / "localtime.cpp"
  let flags := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob  flags #["-fPIC"] "c++"

extern_lib libleanlocaltime pkg := do
  let name := nameToStaticLib "leanlocaltime"
  let localtime ← localtime.o.fetch
  buildStaticLib (pkg.nativeLibDir / name) #[localtime]
