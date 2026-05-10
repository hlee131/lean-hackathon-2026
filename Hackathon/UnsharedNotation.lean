import Lean

open Lean Parser Meta Elab

def markUnshared (e : Expr) : Expr :=
  e.setOption `unshared true

def isUnshared : Expr → Bool
  | .mdata d _ => d.getBool `unshared
  | _ => false

def fooExpr : MetaM Expr := do
  let type := mkConst ``Nat
  let val := markUnshared $ mkNatLit 42
  withLetDecl `x type val fun x => do
    let body := mkApp2 (mkConst ``Nat.add) x x
    return ← mkLetFVars #[x] body

run_meta logInfo (← fooExpr)

elab "unshared_let " x:ident " := " e:term " in " body:term : term => do
  let e ← Term.elabTermAndSynthesize e none
  let type ← inferType e
  withLetDecl x.getId type e fun fvar => do
    let body ← Term.elabTerm body none
    let msg := x.getId.toString
    let wrapped ← mkAppM ``dbgTraceIfShared #[mkStrLit msg, fvar]
    let body := body.replaceFVar fvar wrapped
    return ← mkLetFVars #[fvar] body

def fooLet (arr : Array Nat) : Array Nat :=
  unshared_let foo := arr in
  let foo := foo.reverse
  let foo := foo.reverse

#print fooLet

syntax (name := unshared) "unshared " term : term

open Term in
@[term_elab «unshared»]
def elabUnshared : TermElab := fun stx expectedType? =>
  match stx with
  | `(unshared $t) => do
    let t ← elabTermAndSynthesize t expectedType?
    return ← mkAppM ``dbgTraceIfShared #[mkStrLit "shared!", t]
  | _ => throwUnsupportedSyntax

def foo : IO Unit :=
  let foo := unshared "a string"
  IO.println foo

#print foo
