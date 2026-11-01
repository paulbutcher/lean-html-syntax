/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HtmlSyntax
public import HtmlRenderer
public meta import Lean.Elab.Command

public section

namespace HtmlSyntaxTests

open Lean Elab Command

/-- Elaborates a term that should fail, and reports the source its first error points at with
the message, so that `#guard_msgs` checks where the error is as well as what it says. -/
syntax (name := htmlError) "#html_error " term : command

@[command_elab htmlError] meta def elabHtmlError : CommandElab := fun stx => do
  let saved := (← get).messages
  modify fun s => { s with messages := {} }
  try
    liftTermElabM do
      discard <| Term.elabTerm stx[1] none
      Term.synthesizeSyntheticMVarsNoPostponing
  catch ex => logException ex
  let msgs := (← get).messages
  modify fun s => { s with messages := saved }
  let some m := msgs.toList.find? (·.severity == .error) | logError "expected an error"
  let fm ← getFileMap
  let at_ := String.Pos.Raw.extract fm.source (fm.ofPosition m.pos) (fm.ofPosition (m.endPos.getD m.pos))
  logInfo m!"at `{at_}`: {← m.data.toString}"

end HtmlSyntaxTests
