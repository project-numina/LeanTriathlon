/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Lean
public import Qq

@[expose] public meta section

open Lean Elab Meta Qq Command

inductive AMS

  | «0»

  | «1»

  | «3»

  | «5»

  | «6»

  | «8»

  | «11»

  | «12»

  | «13»

  | «14»

  | «15»

  | «16»

  | «17»

  | «18»

  | «19»

  | «20»

  | «22»

  | «26»

  | «28»

  | «30»

  | «31»

  | «32»

  | «33»

  | «34»

  | «35»

  | «37»

  | «39»

  | «40»

  | «41»

  | «42»

  | «43»

  | «44»

  | «45»

  | «46»

  | «47»

  | «49»

  | «51»

  | «52»

  | «53»

  | «54»

  | «55»

  | «57»

  | «58»

  | «60»

  | «62»

  | «65»

  | «68»

  | «70»

  | «74»

  | «76»

  | «78»

  | «80»

  | «81»

  | «82»

  | «83»

  | «85»

  | «86»

  | «90»

  | «91»

  | «92»

  | «93»

  | «94»

  | «97»
  deriving Inhabited, BEq, Hashable, ToExpr

def numToAMSName (n : Nat) : MetaM Name := do
  let nm : Name := Name.str ``AMS (ToString.toString n)
  unless !(← Lean.hasConst nm) do return nm
  throwError "Out of bounds"

def AMS.getDesc (a : AMS) : CoreM String := do
  let .const n [] := Lean.toExpr a | throwError "this shouldn't happen"
  let .some doc := ← Lean.findDocString? (← getEnv) n | throwError m!"{.ofConstName n} is missing a docstring"
  return doc.trimAscii.toString

def AMS.toNat? (a : AMS) : Option Nat := do
  let .const (.str _ m) [] := Lean.toExpr a | none
  m.toNat?

unsafe def numToAMSSubjects (n : Nat) : MetaM AMS := do
  let nm ← numToAMSName n
  Meta.evalExpr AMS q(AMS) (.const nm [])

elab "#AMS" : command => do
  let env ← Lean.getEnv
  let lines ← (List.range 97).filterMapM fun n => do
    let nm : Name := Name.str ``AMS (ToString.toString n)
    if ← Lean.hasConst nm then
      if let some doc := ← Lean.findDocString? env nm then
        return s!"{n} {doc.trimAscii}"
    return none
  Lean.logInfo ("\n".intercalate lines)
