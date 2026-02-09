import Lean
import Lean.Elab.Term
import VersoManual
import TextbookTemplate.Meta.Lean
import TextbookTemplate.Papers

open Lean Elab Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open TextbookTemplate

set_option pp.rawOnError true
set_option quotPrecheck false

#doc (Manual) "Software Foundations in Lean" =>

%%%
authors := ["Steven Holtzen"]
%%%


# Typed arithmetic expressions

Consider the following surface syntax of expressions:

```
t ::= true
    | false
    | if t then t else t
    | 0
    | succ t
    | pred t
    | iszero t
```

This can be encoded as the following Lean inductive type:

```savedLean
/--
  An inductive type of typed arithmetic expressions.
-/
inductive tm : Type where
| fls : tm
| tru : tm
| ite : tm -> tm -> tm -> tm
| zro : tm
| succ : tm -> tm
| prd : tm -> tm
| iszro : tm -> tm
```

Now we can give this language a simple surface syntax for working with it:

```savedLean
declare_syntax_cat tarith
syntax "false" : tarith
syntax "true" : tarith
syntax "[" term "]": tarith
syntax "if" tarith "then" tarith "else" tarith : tarith
syntax:100 "(" tarith ")" : tarith
syntax "zero" : tarith
syntax "pred" tarith : tarith
syntax "succ" tarith : tarith
syntax "zero?" tarith : tarith

partial def tm.elab (t : TSyntax `tarith) : TermElabM Expr :=
  match t with
  | `(tarith| ( $e ) ) => tm.elab e
  | `(tarith| [ $e:term ]) => do
    let expr ← Term.elabTerm e none
    return expr
  | `(tarith| true) => do
    mkAppM ``tm.tru #[]
  | `(tarith| false) => do
    mkAppM ``tm.fls #[]
  | `(tarith| if $e1 then $e2 else $e3 ) => do
   mkAppM ``tm.ite #[<- tm.elab e1,
                     <- tm.elab e2,
                     <- tm.elab e3]
  | `(tarith| zero) => do
    mkAppM ``tm.zro #[]
  | `(tarith| succ $e1) => do
    mkAppM ``tm.succ #[<- tm.elab e1]
  | `(tarith| pred $e1) => do
    mkAppM ``tm.prd #[<- tm.elab e1]
  | `(tarith| zero? $e1) => do
    mkAppM ``tm.iszro #[<- tm.elab e1]
  | _ => throwUnsupportedSyntax

elab "{{" e:tarith "}}" : term => tm.elab e
```

Now we can use our parser and elaborator together to easily parse
typed arithmetic expressions:

```lean (name := parse_tarith)
#eval {{ if (zero? zero) then true else false }}
-- here is an example showcasing the unquote mechanism
#eval {{ if [ tm.zro ] then true else false}}
```
```leanOutput parse_tarith
tm.ite (tm.iszro (tm.zro)) (tm.tru) (tm.fls)
```

## Operational semantics

First let's define a notion of values:

```savedLean
/--
  Boolean values
-/
inductive bvalue : tm -> Prop
| bv_true : bvalue {{true}}
| bv_false : bvalue {{false}}

/--
  Numeric values
-/
inductive nvalue : tm -> Prop
| nv_0 : nvalue {{zero}}
| nv_succ : nvalue t -> nvalue {{succ [t]}}

def value (t : tm) : Prop := bvalue t ∨ nvalue t
```

Let's give operational semantics for this language:

```savedLean
inductive step : tm -> tm -> Prop
| st_if_true : ∀ e1 e2 : tm,
  step {{ if true then [e1] else [e2] }} e1
| st_if_false : ∀ e1 e2 : tm,
  step {{ if false then [e1] else [e2] }} e2
| st_if : ∀ e1 e2 e3 : tm,
  step e1 e1' ->
  step {{ if [e1] then [e2] else [e3] }}
       {{ if [e1'] then [e2] else [e3]}}
| st_succ :
  step e1 e1' ->
  step {{ succ [e1]}} {{ succ [e1']}}
| st_pred0 :
  step {{ pred zero }} {{ zero }}
| st_pred_succ :
  nvalue v ->
  step {{pred (succ [v])}} v
| st_pred :
  step e e' ->
  step {{pred [e]}} {{pred [e']}}
| st_zero?_zero :
  step {{zero? zero}} {{true}}
| st_zero?_succ :
  nvalue v ->
  step {{zero? (succ [v])}} {{false}}
| st_zero? :
  step e e' ->
  step {{zero? [e]}} {{zero? [e']}}
```

## Normal Forms and Values

Sometimes terms can be *stuck*: they cannot take a step and are not a value. For
example:

```savedLean
def relation (X : Type) := X -> X -> Prop

def normal_form (R : relation X) (t : X) : Prop :=
  ¬ ∃ t', R t t'

def step_normal_form := (normal_form step)

def stuck (t : tm) : Prop :=
  step_normal_form t ∧ ¬ value t

```

Let's prove a useful example: there is some stuck term.

```savedLean
example : ∃ t, stuck t := by
  -- the `exists` tactic eliminates the existential
  exists {{if zero then zero else zero}}
  constructor
  · intro ⟨ witness, contradiction ⟩
    cases witness with
    | _ => contradiction
  · intro a
    cases a with
    | _ => contradiction
```

Now let's prove a more interesting theorem: every
value is a normal form.

```savedLean
theorem value_is_nf : ∀ t,
  value t → step_normal_form t := by
  intro tm v
  cases v with
  | inl h =>
    -- boolean value
    intro ⟨ witness, contradiction ⟩
    cases h with
    | _ => contradiction
  | inr h =>
    -- numeric value. We need to do induction here,
    -- in general, it's a good idea to keep your proof
    -- state as simple as possible before you do
    -- induction; induction does some pretty complicated
    -- proof state manipulation
    induction h with
    | nv_0 =>
      intro ⟨ witness, contradiction ⟩
      contradiction
    | nv_succ nv ih =>
      rename_i t
      intro ⟨ witness, c ⟩
      cases c
      rename_i t' s
      apply ih
      exists t'
```

We can prove our step relation is deterministic:

```savedLean
def deterministic (R : relation X) :=
  ∀ x y1 y2 : X, R x y1 → R x y2 → y1 = y2

theorem step_deterministic: deterministic step := by
  sorry
```

Exercise: is there a way to make this proof nice and not
painful?

# Type systems

```savedLean
inductive ty : Type where
| Bool : ty
| Nat : ty

inductive has_type : tm -> ty -> Prop where
| t_true : has_type {{true}} .Bool
| t_false : has_type {{false}} .Bool
| t_ite :
  ∀ g thn els : tm,
  has_type g .Bool ->
  has_type thn t ->
  has_type els t ->
  has_type {{if [g] then [thn] else [els]}} t
| t_zro : has_type {{zero}} .Nat
| t_succ :
  ∀ t : tm,
  has_type t .Nat ->
  has_type {{succ [t]}} .Nat
| t_pred :
  ∀ t,
  has_type t .Nat ->
  has_type {{pred [t]}} .Nat
| t_zero? :
  ∀ t,
  has_type t .Nat ->
  has_type {{zero? [t]}} .Bool
```

Some useful metatheoretic properties of the
type system:

```savedLean
theorem bool_canonical :
  ∀ t,
  has_type t .Bool -> value t -> bvalue t := by
  intro t ty v
  cases v with
  | inl => assumption
  | inr =>
    rename_i h
    cases ty <;> contradiction

theorem num_canonical :
  ∀ t,
  has_type t .Nat -> value t -> nvalue t := by
  intro t ty v
  cases v with
  | inl => cases ty <;> contradiction
  | inr => assumption
```
