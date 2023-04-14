import Lake
open System Lake DSL

package test

require time from "../"

@[default_target]
lean_lib Test

@[default_target]
lean_exe test {
  root := `Test
}
