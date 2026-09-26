/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

import all CompPoly.Fields.KoalaBear.Ext5.QuinticIrreducible
import all CompPoly.Fields.KoalaBear.Ext6.SexticIrreducible
public meta import Lean

/-!
# KoalaBear irreducibility proof replay

Recheck the complete dependency closures of the KoalaBear quintic and sextic irreducibility
proofs in a fresh kernel environment. This matches the verifier boundary: imported declarations
are included in the replay rather than trusted as an existing environment.
-/

meta section

open Lean

deriving instance BEq for Lean.QuotKind, Lean.QuotVal, Lean.InductiveVal, Lean.ConstantInfo

private meta def exportClosure
    (env : Environment) (roots : Array Name) : IO (Std.HashMap Name ConstantInfo) := do
  let mut out : Std.HashMap Name ConstantInfo := {}
  let mut pending := roots
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if out.contains name then continue
    let some ci := env.find? name | throw <| IO.userError s!"Missing replay constant {name}"
    if ci.isUnsafe || ci.isPartial then
      throw <| IO.userError s!"Unsafe or partial constant in replay closure: {name}"
    out := out.insert name ci
    for dep in ci.getUsedConstantsAsSet do pending := pending.push dep
    if let .inductInfo info := ci then
      pending := pending ++ info.all.toArray ++ info.ctors.toArray
    if let .quotInfo _ := ci then
      pending := pending ++ #[`Quot, `Quot.mk, `Quot.lift, `Quot.ind, `Eq]
  return out

private meta def replayClosure (constants : Std.HashMap Name ConstantInfo) : IO Unit := do
  -- Adding `Quot` installs these three constants, so replay must not add them twice.
  let quotientChildren := #[`Quot.mk, `Quot.lift, `Quot.ind]
  let replayConstants := quotientChildren.foldl (fun cs name => cs.erase name) constants
  let checked ← (← mkEmptyEnvironment).toKernelEnv.replay replayConstants
  for (name, _) in constants.toList do
    unless (checked.find? name).isSome do
      throw <| IO.userError s!"Fresh replay omitted {name}"
  for name in #[`Quot] ++ quotientChildren do
    if let some original := constants[name]? then
      let some actual := checked.find? name
        | throw <| IO.userError s!"Missing quotient constant: {name}"
      unless actual == original do
        throw <| IO.userError s!"Quotient constant mismatch: {name}"

run_elab do
  let env ← importModules
    #[{ module := `CompPoly.Fields.KoalaBear.Ext5.QuinticIrreducible },
      { module := `CompPoly.Fields.KoalaBear.Ext6.SexticIrreducible }]
    {} (trustLevel := 0) (loadExts := false) (level := .private)
  let constants ← exportClosure env
    #[`KoalaBear.quinticPoly_irreducible, `KoalaBear.sexticPoly_irreducible]
  replayClosure constants
