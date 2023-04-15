import Lake
open System Lake DSL

package time {
  precompileModules := if get_config? env = some "noprecompile" then false else true
}

require mathlib4 from git "https://github.com/leanprover-community/mathlib4"
  @ "ea4e0dd0dd8021d1677b63fbbe5eab18e5186318"

meta if get_config? env = some "dev" then
require «doc-gen4» from  git "https://github.com/leanprover/doc-gen4" @ "main"

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

target localtime.o (pkg : Package) : FilePath := do
  let oFile := pkg.buildDir / "native/" / "localtime.o"
  let srcJob ← inputFile <| pkg.dir / "native/" / "localtime.cpp"
  let flags := #["-I", (← getLeanIncludeDir).toString, "-fPIC"]
  buildO "localtime.cpp" oFile srcJob flags "c++"

extern_lib libleanlocaltime (pkg : Package) := do
  let name := nameToStaticLib "leanlocaltime"
  let localtime ← fetch <| pkg.target ``localtime.o
  buildStaticLib (pkg.libDir / name) #[localtime]

def excludes (p : FilePath) : Bool :=
  Array.any #["build", "lake-packages"] (fun s => p.toString.endsWith s)

partial def readDirAll (p : FilePath) (acc : Array IO.FS.DirEntry)
    : IO (Array IO.FS.DirEntry) := do
  let folder (ent : IO.FS.DirEntry) (acc : Array IO.FS.DirEntry) : IO (Array IO.FS.DirEntry) := do
    if ← ent.path.isDir then
      if !excludes ent.path then
        return (← readDirAll ent.path acc)
      else return acc
    else return Array.push acc ent

  return ← (Array.foldrM folder acc (← p.readDir))

def exec (cmd: String) (args: Array String ) : IO PUnit := do
  let output  ← IO.Process.output { cmd := cmd, args := args }
  if output.stderr.length > 2 then IO.println s!"{output.stderr}"

def processFile (p : String) : IO PUnit := do
  IO.println s!"processing file {p}"
  exec "lake" #["env", "./lake-packages/doc-gen4/build/bin/doc-gen4", "single", p]
  exec "lake" #["env", "./lake-packages/doc-gen4/build/bin/doc-gen4", "single", p, "--ink"]

def execInDir (p : FilePath) : IO PUnit := do
  for ent in (← readDirAll p Array.empty) do
    if ent.path.toString.endsWith ".lean" then
      processFile <| (ent.path.toString.replace "/" ".").replace ".lean" ""

-- 'lake -Kenv=dev build Time:docs' fails
script buildDocs (args) do
  if args.length > 0 then IO.println s!"{args}"

  if ← FilePath.isDir "./lake-packages/doc-gen4/build/bin" then
    exec "rm" #["-rf", "build/doc/book"]
    execInDir "Time"
    processFile "Time"
    exec "lake" #["env", "./lake-packages/doc-gen4/build/bin/doc-gen4", "genCore"]
    exec "lake" #["env", "./lake-packages/doc-gen4/build/bin/doc-gen4", "index"]
    exec "mdbook" #["build", "doc"]
  else
    IO.println s!"directory 'doc-gen4/build/bin' not found"
    IO.println s!"run 'lake -Kenv=dev update && lake -Kenv=dev build Time.Calendar.Days:docs'"
    IO.println s!"to install and compile doc-gen4"

  return 0
