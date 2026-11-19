import Lean.CoreM
import Lean.Replay
open Lean

/-- `leanchecker`'s `replayFromImports` (Lean v4.36.0-rc2, src/lean/LeanChecker.lean), applied to
exactly the named module (no prefix expansion). -/
unsafe def replayExact (module : Name) : IO Nat := do
  let mFile ← findOLean module
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"object file '{mFile}' of module {module} does not exist"
  let mut fnames := #[mFile]
  let sFile := OLeanLevel.server.adjustFileName mFile
  if (← sFile.pathExists) then
    fnames := fnames.push sFile
    let pFile := OLeanLevel.private.adjustFileName mFile
    if (← pFile.pathExists) then
      fnames := fnames.push pFile
  let parts ← readModuleDataParts fnames
  if h : parts.size = 0 then throw <| IO.userError "failed to read module data" else
  let (mod, _) := parts[0]
  let (_, s) ← importModulesCore mod.imports |>.run
  let env ← finalizeImport s mod.imports {} 0 false false (isModule := true)
  let mut newConstants : Std.HashMap Name ConstantInfo := {}
  for name in parts[parts.size-1].1.constNames, ci in parts[parts.size-1].1.constants do
    newConstants := newConstants.insert name ci
  discard <| env.toKernelEnv.replay newConstants
  env.freeRegions
  return newConstants.size

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  for a in args do
    let n ← replayExact a.toName
    IO.println s!"{a}: replayed {n} constants, accepted"
  return 0
