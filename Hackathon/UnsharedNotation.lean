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

        let currElab ← Term.getDeclName?
        let fileMap ← getFileMap

        let declStr := match currElab with
        | some n => n.toString
        | _ => s!"<unnamed>"

        let locStr := match stx.getPos? with
        | some p => s!"{(FileMap.toPosition fileMap p).line}"
        | _ => s!"<unknown loc>"

        let dbgMsg := s!"in {declStr} on line {locStr}"

        let wrapped ← mkAppM ``dbgTraceIfShared #[mkStrLit dbgMsg, fvar]
        mkLetFVars #[fvar] $ openedBody.replaceFVar fvar wrapped
    | _ => unreachable!
  else
    return e

set_option linter.unusedVariables false
def foo (arr : Array Nat) : Array Nat :=
  let +unshared arr := arr
  let arr := arr.reverse
  let bar := 5
  arr
