import Lake
open System Lake DSL

package time {
  precompileModules := if get_config? env = some "noprecompile" then false else true
}

require std from git "https://github.com/leanprover/std4" @ "v4.7.0"

meta if get_config? env = some "dev" then
require leanInk from git "https://github.com/hargonix/LeanInk" @ "doc-gen"

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
  let flags := #["-I", (← getLeanIncludeDir).toString, "-fPIC"]
  buildO "localtime.cpp" oFile srcJob flags #[] "c++"

extern_lib libleanlocaltime pkg := do
  let name := nameToStaticLib "leanlocaltime"
  let localtime ← fetch <| pkg.target ``localtime.o
  buildStaticLib (pkg.nativeLibDir / name) #[localtime]
