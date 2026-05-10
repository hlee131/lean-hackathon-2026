import Lean
import Hackathon.Option

open Lean Parser Meta Elab

def letOptUnshared := leading_parser
  nonReservedSymbol "unshared"

def letPosOptUnshared := leading_parser (withAnonymousAntiquot := false)
  " +" >> checkNoWsBefore >> letOptUnshared

open Lean.Parser.Term in
@[term_parser]
def letUnshared := leading_parser:leadPrec
  withPosition ("let" >> letPosOptUnshared >> letConfig >> letDecl) >> optSemicolon termParser

partial def instrumentLetUnshared (fvarId : FVarId) : Expr → TermElabM Expr
  | .letE name type val body nondep => do
    let fvar : Expr := .fvar fvarId

    let some declStr ← Term.getDeclName?
      | unreachable!
    /- let fileMap ← getFileMap -/

    /- let locStr := match stx.getPos? with
     - | some p => s!"{(FileMap.toPosition fileMap p).line}"
     - | _ => s!"<unknown loc>" -/

    let dbgMsg := s!"in {declStr} on line TEMP"

    let wrapped ← mkAppM ``dbgTraceIfShared #[mkStrLit dbgMsg, fvar]

    let val :=
      if name == (← fvarId.getUserName) then
        val.replaceFVar fvar wrapped
      else val

    withLetDecl name type val (nondep := nondep) fun fvar => do
      let openedBody := body.instantiate1 fvar
      let instrumentedBody ← instrumentLetUnshared fvar.fvarId! openedBody
      mkLetFVars #[fvar] instrumentedBody

  | .mdata _ e => instrumentLetUnshared fvarId e
  | e => pure e

@[term_elab letUnshared]
def elabLetUnshared : Term.TermElab := fun stx expectedType? => do
  -- "let" "+unshared" letConfig letDecl optSemicolon body
  --   0        1          2        3         4        5
  let letConfig : TSyntax `Lean.Parser.Term.letConfig := ⟨stx[2]⟩
  let letDecl : TSyntax `Lean.Parser.Term.letDecl := ⟨stx[3]⟩
  let body : Term := ⟨stx[5]⟩
  let normalLet ← `(let $letConfig:letConfig $letDecl:letDecl; $body)
  let e ← Term.elabTerm normalLet expectedType?

  if unshared.runtimeWarning.get (← getOptions) then
    match e with
    | .letE name type val body nondep =>
      withLetDecl name type val (nondep := nondep) fun fvar => do
        let openedBody := body.instantiate1 fvar
        let instrumentedBody ← instrumentLetUnshared fvar.fvarId! openedBody
        mkLetFVars #[fvar] instrumentedBody
    | _ => unreachable!
  else
    return e

set_option linter.unusedVariables false
def foo (arr : Array Nat) : Array Nat :=
  let +unshared arr := arr
  let arr := arr.reverse
  let bar := 5
  let arr := arr.reverse
  (fun x =>
    let arr := arr.reverse
    arr) ()
