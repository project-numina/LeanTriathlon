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

public import LiveLeanTriathlonSorry.Util.Attributes.AMS

@[expose] public meta section

open Lean Elab Meta Qq

namespace ProblemAttributes

structure SubjectTag where

  declName : Name

  subjects : List AMS

  informal : String
  deriving Inhabited, BEq, Hashable, ToExpr

initialize subjectExt : SimplePersistentEnvExtension SubjectTag (Std.HashSet SubjectTag) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun as => as.foldl Std.HashSet.insertMany {}
    addEntryFn := .insert
  }

def addSubjectEntry {m : Type → Type} [MonadEnv m] (name : Name)
    (subjects : List AMS) (informal : String) : m Unit :=
  modifyEnv (subjectExt.addEntry ·
    { declName := name, subjects := subjects, informal := informal })

syntax subjectList := many(num)

def Syntax.toSubjects (stx : TSyntax ``subjectList) : MetaM (Array AMS) := do
  match stx with
  | `(subjectList|$[$nums] *) =>
    nums.mapM fun (n : TSyntax `num) => do
      let nVal := n.getNat
      let name ← numToAMSName nVal
      Elab.addConstInfo n name
      unsafe Meta.evalExpr AMS q(AMS) (.const name [])
  | _ => throwUnsupportedSyntax

syntax (name := problemSubject) "AMS" subjectList : attr

initialize Lean.registerBuiltinAttribute {
  name := `problemSubject
  descr := "Annotation of the subject of a given problem statement"
  add := fun decl stx _attrKind => do
    let oldDoc := (← findDocString? (← getEnv) decl).getD ""
    let subjects ← match stx with
      | `(attr| AMS $n) => withRef n <|
        Lean.Meta.MetaM.run' (Syntax.toSubjects n)
      | _ => throwUnsupportedSyntax
    addSubjectEntry decl subjects.toList oldDoc
}

section Helper

def getSubjectTags {m : Type → Type} [Monad m] [MonadEnv m] : m (Array SubjectTag) := do
  return subjectExt.getState (← MonadEnv.getEnv) |>.toArray

end Helper

end ProblemAttributes
