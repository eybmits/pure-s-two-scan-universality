import Lake

open Lake DSL

package pure_s_two_scans where
  version := v!"1.0.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "56a005855ea17e0b0958f73ec801ae140b0a1679"

private def modules : Array String := run_io
  let files ← (__dir__ / "formal").readDir
  return (files.filterMap fun f =>
    if f.path.extension == some "lean" then f.path.fileStem else none).qsort (· < ·)

@[default_target]
lean_lib Certified where
  srcDir := "formal"
  roots := modules.map Lean.Name.mkSimple
