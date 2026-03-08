import Lean
open Lean Elab Meta

macro "test" lhs:term "," rhs:term : command =>
  `(command|
    #eval do
      let l := $lhs
      let r := $rhs
      if l != r then
        throw (IO.userError s!"test failed: {repr l} ≠ {repr r}")
      else
        IO.println s!"test passed: {repr l} == {repr r}")

-- Nat arithmetic
test 1 + 1, 2

inductive STLC : Nat -> Type where
  | Var : Fin n -> STLC n
  | App : STLC n -> STLC n -> STLC n
  | Plus : STLC n -> STLC n -> STLC n
  | Abs : STLC (n + 1) -> STLC n
  | Const : Nat -> STLC n
  deriving ToExpr

declare_syntax_cat stlc

syntax:70 ident : stlc
syntax:60 num : stlc
syntax:100 "(" stlc ")" : stlc
syntax:50 "fun" ident "=>" stlc : stlc
syntax:40 stlc:41 stlc:40 : stlc
syntax:30 stlc:31 "+" stlc:30 : stlc

def Ctx := List String

def Ctx.lookup (c : Ctx) (s : String) : Option (Fin c.length) :=
  c.finIdxOf? s

partial def STLC.elab (t : TSyntax `stlc) (ctx : Ctx) : MetaM Expr :=
  match t with
  | `(stlc| ( $e ) ) => STLC.elab e ctx
  | `(stlc | $i:ident ) =>
    match ctx.lookup i.getId.toString with
    | none => throwError s!"Unknown variable: {i}"
    | some idx =>
      return ((mkConst ``STLC.Var).app (mkNatLit ctx.length)).app (toExpr idx)
  | `(stlc | fun $i => $e ) => do
    let s <- STLC.elab e (i.getId.toString :: ctx) -- DeBruijn index: new variables at head of list
    mkAppM ``STLC.Abs #[s]
  | `(stlc | $e1 $e2 ) => do
    mkAppM ``STLC.App #[<- STLC.elab e1 ctx, <- STLC.elab e2 ctx]
  | `(stlc | $c:num ) => do
    mkAppM ``STLC.Const #[mkNatLit c.getNat]
  | `(stlc | $e1 + $e2) => do
    mkAppM ``STLC.Plus #[<- STLC.elab e1 ctx, <- STLC.elab e2 ctx]
  | _ => throwUnsupportedSyntax

elab "{{" e:stlc "}}" : term => STLC.elab e []

set_option pp.fieldNotation false

#eval {{ fun i => fun j => i + j }}
