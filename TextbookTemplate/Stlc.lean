import VersoManual
import DemoTextbook.Meta.Lean
import Lean
open Lean Elab Meta


-- This gets access to most of the manual genre (which is also useful for textbooks)
open Verso.Genre Manual

-- This gets access to Lean code that's in code blocks, elaborated in the same process and
-- environment as Verso
open Verso.Genre.Manual.InlineLean

macro "#test" lhs:term "," rhs:term : command =>
  `(command|
    #eval do
      let l := $lhs
      let r := $rhs
      if l != r then
        throw (IO.userError s!"test failed: {repr l} ≠ {repr r}")
      else
        IO.println s!"test passed: {repr l} == {repr r}")

open DemoTextbook

set_option pp.rawOnError true

#doc (Manual) "Simply Typed Lambda Calculus" =>

Now we will explore some of the metatheory of the simply-typed lambda calculus.
We have the following surface syntax:

$$`e ::= \lambda x . e \mid e ~ e \mid x \mid n \mid e + e`

Then we can give the abstract syntax:

```savedLean
inductive STLC : Nat -> Type where
  | Var : Fin n -> STLC n
  | App : STLC n -> STLC n -> STLC n
  | Plus : STLC n -> STLC n -> STLC n
  | Abs : STLC (n + 1) -> STLC n
  | Const : Nat -> STLC n
  deriving BEq, Repr
```

This abstract syntax is in *DeBruijn style*: variables are referred to by their
binding depth.  A value of type `STLC n` is an STLC program with `n` free
variables.  This AST is also *implicitly well-scoped*: well-typed ASTs
implicitly cannot refer to unbound variables. This style of AST is quite
unpleasant to program in, so as in the previous section we will create an
embedded DSL for representing lambda terms:

```savedLean
declare_syntax_cat stlc

syntax:70 ident : stlc
syntax:60 num : stlc
syntax:100 "(" stlc ")" : stlc
syntax:50 "fun" ident "=>" stlc : stlc
syntax "[" term "]": stlc
syntax:40 stlc:41 stlc:40 : stlc
syntax:30 stlc:31 "+" stlc:30 : stlc

def Ctx := List String

def Ctx.lookup (c : Ctx) (s : String) : Option (Fin c.length) :=
  c.finIdxOf? s

partial def STLC.elab (t : TSyntax `stlc) (ctx : Ctx) : TermElabM Expr :=
  match t with
  | `(stlc| ( $e ) ) => STLC.elab e ctx
  | `(stlc| [ $e:term ]) => do
    let expr ← Term.elabTerm e none
    return expr
  | `(stlc | $i:ident ) =>
    match ctx.lookup i.getId.toString with
    | none => throwError s!"Unknown variable: {i}"
    | some idx =>
      -- elaborate into a 3-part application:
      -- First, a call the the var constructor
      -- then, pass it a proof that the variable is well-scoped
      -- finally, pass it the variable itself
      return ((mkConst ``STLC.Var).app (mkNatLit ctx.length)).app (toExpr idx)
  | `(stlc | fun $i => $e ) => do
    let s <- STLC.elab e (i.getId.toString :: ctx) -- DeBruijn index: new variables at head of list
    mkAppM ``STLC.Abs #[s]
  | `(stlc | $e1 $e2 ) => do
    mkAppM ``STLC.App #[<- STLC.elab e1 ctx, <- STLC.elab e2 ctx]
  | `(stlc | $c:num ) => do
    return ((mkConst ``STLC.Const).app (mkNatLit ctx.length)).app (mkNatLit c.getNat)
  | `(stlc | $e1 + $e2) => do
    mkAppM ``STLC.Plus #[<- STLC.elab e1 ctx, <- STLC.elab e2 ctx]
  | _ => throwUnsupportedSyntax

elab "{stlc" e:stlc "}" : term => STLC.elab e []
```

The above elaborator performs DeBruijn conversion. Concretely, we
can write STLC programs in the natural style that is not DeBruijn indexed:

```lean (name := parse_stlc)
#eval {stlc fun x => fun y => x + y }
```
```leanOutput parse_stlc
STLC.Abs (STLC.Abs (STLC.Plus (STLC.Var 1) (STLC.Var 0)))
```

It will also be useful to have surface syntax for writing DeBruijn terms directly:

```savedLean
declare_syntax_cat stlc_debruijn

syntax:60 num : stlc_debruijn
syntax:60 "v" num : stlc_debruijn
syntax:100 "(" stlc_debruijn ")" : stlc_debruijn
syntax:50 "λ" "." stlc_debruijn : stlc_debruijn
syntax "[" term "]": stlc_debruijn
syntax:40 stlc_debruijn:41 stlc_debruijn:40 : stlc_debruijn
syntax:30 stlc_debruijn:31 "+" stlc_debruijn:30 : stlc_debruijn

-- elaborate a syntactic debruijn in context ctx
-- the context is the number of free variables
partial def STLC.elab_debruijn (t : TSyntax `stlc_debruijn) (ctx : Nat) : TermElabM Expr :=
  match t with
  | `(stlc_debruijn| ( $e ) ) => STLC.elab_debruijn e ctx
  | `(stlc_debruijn| [ $e:term ]) => do
    let expr ← Term.elabTerm e none
    return expr
  | `(stlc_debruijn| λ . $e ) => do
    let s <- STLC.elab_debruijn e (ctx + 1)
    mkAppM ``STLC.Abs #[s]
  | `(stlc_debruijn | $e1 $e2 ) => do
    mkAppM ``STLC.App #[<- STLC.elab_debruijn e1 ctx, <- STLC.elab_debruijn e2 ctx]
  | `(stlc_debruijn | v $c:num ) =>
    -- this is a "decision procedure branch", which names the proof that a
    -- particular branch of the `if` is taken
    if pf : c.getNat < ctx then
      let n : Fin ctx := ⟨ c.getNat, pf ⟩
      return ((mkConst ``STLC.Var).app (mkNatLit ctx)).app (toExpr n)
    else
      throwError s!"Unknown variable: {c.getNat}"
  | `(stlc_debruijn | $c:num ) => do
    return ((mkConst ``STLC.Const).app (mkNatLit ctx)).app (mkNatLit c.getNat)
  | `(stlc_debruijn | $e1 + $e2) => do
    mkAppM ``STLC.Plus #[<- STLC.elab_debruijn e1 ctx, <- STLC.elab_debruijn e2 ctx]
  | _ => throwUnsupportedSyntax

elab "{stlc_debruijn" e:stlc_debruijn "}" : term => STLC.elab_debruijn e 0

-- it is also helpful to be able to desugar an open term in debruijn for many
-- examples and proofs, so we provide this as well
syntax "{stlc_debruijn_open " num "|" stlc_debruijn "}": term
elab_rules : term
  | `({stlc_debruijn_open $t:num | $e}) => do
    STLC.elab_debruijn e t.getNat
```

# Semantics of STLC

We will once again give the small-step semantics of STLC, but this time we will
use *evaluation contexts*.

$$`E ::= [\cdot] \mid E~e \mid (\lambda x . e)~E \mid E+e \mid n + E`

```savedLean
inductive EvalCtx where
| Hole
| App1 : EvalCtx -> STLC 0 -> EvalCtx
| App2 : STLC 1 -> EvalCtx -> EvalCtx
| Add1 : EvalCtx -> STLC 0 -> EvalCtx
| Add2 : Nat -> EvalCtx -> EvalCtx
```

Now we can give the small-step evaluation rules:

$$`\dfrac{~}{E[(\lambda x . e) ~ v] \rightarrow E\Big[e[v/x]\Big]}~\text{(E-Beta)}`

$$`\dfrac{~}{E[n_1 + n_2] \rightarrow E[n_1 + n_2]}~\text{(E-Add)}`

## Substitution

To implement these rules we of course need substitution, which is given as
follows. This substitution is quite simplified because we do not need to
concern ourselves with capture avoidance, since we are only implementing a
call-by-value small-step semantics.

First, we define a helper function that renames free variables:

```savedLean
def STLC.rename (e : STLC n) (f : Fin n -> Fin m) : STLC m :=
  match e with
  | .Var i => .Var (f i)
  | .App e1 e2 => .App (e1.rename f) (e2.rename f)
  | .Plus e1 e2 => .Plus (e1.rename f) (e2.rename f)
  | .Const i => .Const i
  | .Abs k => .Abs (k.rename (bumpRename f))
  where
    bumpRename : (Fin n -> Fin m) -> Fin (n + 1) -> Fin (m + 1) :=
      fun f i =>
        Fin.cases
          0
          (Fin.succ ∘ f)
          i
```

For example:

```lean
#test (STLC.rename {stlc_debruijn_open 1 | (λ . v 1)} Fin.succ),
      {stlc_debruijn_open 2 | (λ . v 2)}
#test (STLC.rename {stlc_debruijn_open 1 | (λ . v 0)} Fin.succ),
      {stlc_debruijn_open 2 | (λ . v 0)}
```

Now we can implement substitution using this helper function:

```savedLean
def STLC.subst (e : STLC n) (f : Fin n -> STLC m) : STLC m :=
  match e with
  | .Var i => f i
  | .App e1 e2 => .App (e1.subst f) (e2.subst f)
  | .Plus e1 e2 => .Plus (e1.subst f) (e2.subst f)
  | .Const i => .Const i
  | .Abs k => .Abs (k.subst (bumpSubst f)) -- Need to lift f to Fin n + 1 -> STLC m + 1
  where
    bumpSubst : (Fin n -> STLC m) -> (Fin (n + 1) -> STLC (m + 1)) :=
      fun f i =>
        Fin.cases
          (.Var 0)
          (fun j => (f j).rename Fin.succ)
          i

-- perform substitution (λ.v1)[λ.v0/v1] = λ . λ . v0
#test (STLC.subst {stlc_debruijn_open 1 | λ . v 1}
           (fun (i : Fin 1) => {stlc_debruijn λ . v 0 })),
      {stlc_debruijn λ . (λ . v 0)}
```

## Operational Semantics

Now we are ready to define the operational semantics. We need a few extra
inductive definitions to distinguish our value forms:

```savedLean
inductive Val : STLC m -> Prop where
  | LamV : Val (STLC.Abs e)
  | NumV : Val (STLC.Const n)
```

Next, we can define composition of contexts with terms:

```savedLean
-- compose E[t]
def compose (E : EvalCtx) (t : STLC 0) : STLC 0 :=
  match E with
  | .Hole => t
  | .App1 E' e => .App (compose E' t) e
  | .App2 e E' => .App (.Abs e) (compose E' t)
  | .Add1 E' e => .Plus (compose E' t) e
  | .Add2 n E' => .Plus (.Const n) (compose E' t)

notation E "[" t "]" => compose E t
```

Now, we can define head reduction, which defines primitive reductions:

```savedLean
inductive Head : STLC 0 -> STLC 0 -> Prop where
  | beta : ∀ x : STLC 0, ∀ e : STLC 1,
          Val x ->
          Head {stlc_debruijn (λ . [e]) [x]}
             (STLC.subst e (fun i : Fin 1 => x))
  | add : ∀ n1 n2 : Nat,
          Head (.Plus (.Const n1) (.Const n2)) (.Const (n1 + n2))
```

And now, finally, we can define how to take a step using the evaluation
context in concert with the head reduction:

```savedLean
inductive Step : STLC 0 → STLC 0 → Prop where
  | ctx : ∀ E : EvalCtx,
          Head e e' →
          Step (E[e]) (E[e'])

infix:50 " ⟶ " => Step
```

Seeing these rules work together is a bit involved, so let's see a
small example of working with them:

```lean
example : Step {stlc (1 + 2) + 3} {stlc 3 + 3} := by
  have hd : Head {stlc (1 + 2)} {stlc 3} := by constructor
  apply Step.ctx (.Add1 .Hole (.Const 3)) hd

example : Step {stlc ((fun x => x) 10) + 20} {stlc 10 + 20} := by
  have hd : Head {stlc (fun x => x) 10} {stlc 10} := by
    constructor
    constructor
  apply Step.ctx (.Add1 .Hole (.Const 20)) hd
```

Note how, to establish a particular step, we first identify the
head reduction, then we explicitly construct the appropriate evaluation
context and apply the `Step.ctx` constructor.

# Typing Judgment

# Metatheory

## Subject Reduction

## Type soundness
